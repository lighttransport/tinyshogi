#!/usr/bin/env python3
"""Small stdio MCP server for the tinyshogi engine.

It intentionally uses only the Python standard library, so it can run on a
training host without installing an MCP SDK.  The connected MCP client/LLM
owns the JSON-RPC transport; this process owns one engine game and one
optional self-play subprocess.
"""
import json
import os
import subprocess
import sys
import threading
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ENGINE = Path(os.environ.get("TINYSHOGI_ENGINE", ROOT / "build" / "tinyshogi"))


class TinyShogi:
    def __init__(self):
        self.proc = subprocess.Popen(
            [str(ENGINE)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL, text=True, bufsize=1
        )
        self.lock = threading.Lock()
        self.moves = []
        self.training = None
        self.base_sfen = None
        self.send("usi")
        self.read_until("usiok")
        self.send("isready")
        self.read_until("readyok")

    def send(self, line):
        if self.proc.poll() is not None:
            raise RuntimeError("engine has exited")
        self.proc.stdin.write(line + "\n")
        self.proc.stdin.flush()

    def read_until(self, marker):
        lines = []
        while True:
            line = self.proc.stdout.readline()
            if not line:
                raise RuntimeError("engine closed stdout")
            line = line.rstrip("\n")
            lines.append(line)
            if line == marker or line.startswith(marker + " "):
                return lines

    def position(self):
        command = "position startpos" if self.base_sfen is None else "position sfen " + self.base_sfen
        if self.moves:
            command += " moves " + " ".join(self.moves)
        self.send(command)

    def sfen(self):
        self.position()
        self.send("sfen")
        lines = self.read_until("readyok") if False else self.read_until_sfen()
        return lines

    def read_until_sfen(self):
        line = self.proc.stdout.readline()
        if not line:
            raise RuntimeError("engine closed stdout")
        return line.strip()

    def board(self):
        with self.lock:
            value = self.sfen()
        fields = value.split()
        if len(fields) < 4:
            raise RuntimeError("invalid SFEN from engine: " + value)
        return {
            "sfen": value,
            "board": fields[0],
            "side_to_move": "black" if fields[1] == "b" else "white",
            "hands": fields[2],
            "move_number": int(fields[3]),
            "moves": list(self.moves),
        }

    def play(self, move):
        if not isinstance(move, str) or not move or any(c.isspace() for c in move):
            raise ValueError("move must be a USI move string")
        with self.lock:
            old = self.sfen()
            self.moves.append(move)
            new = self.sfen()
            if new == old:
                self.moves.pop()
                raise ValueError("illegal or unparseable move: " + move)
        return self.board()

    def reset(self, sfen=None):
        with self.lock:
            if sfen:
                self.send("position sfen " + sfen)
                self.send("sfen")
                actual = self.read_until_sfen()
                if actual != sfen:
                    raise ValueError("invalid SFEN or engine normalization: " + actual)
                # Preserve arbitrary SFEN positions as a single opaque state.
                self.base_sfen = sfen
                self.moves = []
            else:
                self.base_sfen = None
                self.moves = []
        return self.board()

    def search(self, nodes=256, movetime=0):
        with self.lock:
            self.position()
            self.send("go movetime " + str(int(movetime)) if movetime else "go nodes " + str(int(nodes)))
            lines = self.read_until("bestmove")
        best = lines[-1].split(maxsplit=1)[1] if len(lines[-1].split()) > 1 else "resign"
        return {"bestmove": best, "output": lines, "board": self.board()}

    def start_training(self, args):
        if self.training and self.training.poll() is None:
            raise RuntimeError("training is already running")
        output = str(args.get("output", "selfplay.jsonl"))
        command = [str(ENGINE), "--selfplay", "--output", output]
        for key, option in (("games", "--games"), ("simulations", "--simulations"),
                            ("threads", "--threads"), ("seed", "--seed"),
                            ("temperature", "--temperature"),
                            ("temperature_cutoff", "--temperature-cutoff"),
                            ("max_plies", "--max-plies")):
            if key in args:
                command += [option, str(int(args[key]))]
        self.training = subprocess.Popen(command, stdout=subprocess.DEVNULL,
                                          stderr=subprocess.PIPE, text=True)
        return {"pid": self.training.pid, "output": output, "command": command}

    def training_status(self):
        if not self.training:
            return {"running": False, "started": False}
        code = self.training.poll()
        return {"running": code is None, "started": True, "pid": self.training.pid,
                "returncode": code}

    def stop_training(self):
        if self.training and self.training.poll() is None:
            self.training.terminate()
            self.training.wait(timeout=5)
        return self.training_status()


GAME = None


def result(text, structured=None):
    return {"content": [{"type": "text", "text": text}],
            **({"structuredContent": structured} if structured is not None else {})}


def tools():
    def schema(properties=None, required=None):
        return {"type": "object", "properties": properties or {}, "required": required or []}
    return [
        {"name": "query_board", "description": "Return exact current board/SFEN and move history.", "inputSchema": schema()},
        {"name": "play_move", "description": "Play one legal USI move on the current board.", "inputSchema": schema({"move": {"type": "string"}}, ["move"])},
        {"name": "reset_board", "description": "Reset to startpos or a supplied SFEN.", "inputSchema": schema({"sfen": {"type": "string"}})},
        {"name": "search", "description": "Search the current board and return bestmove plus engine output.", "inputSchema": schema({"nodes": {"type": "integer", "minimum": 1}, "movetime": {"type": "integer", "minimum": 1}})},
        {"name": "training_start", "description": "Start background deterministic self-play data generation.", "inputSchema": schema({"games": {"type": "integer"}, "simulations": {"type": "integer"}, "threads": {"type": "integer"}, "seed": {"type": "integer"}, "output": {"type": "string"}, "temperature": {"type": "integer"}, "temperature_cutoff": {"type": "integer"}, "max_plies": {"type": "integer"}})},
        {"name": "training_status", "description": "Query background self-play status.", "inputSchema": schema()},
        {"name": "training_stop", "description": "Stop background self-play.", "inputSchema": schema()},
        {"name": "llm_context", "description": "Create a compact board context for an LLM analysis turn.", "inputSchema": schema()},
        {"name": "llm_message", "description": "Wrap an LLM message with current board context for the connected client.", "inputSchema": schema({"message": {"type": "string"}}, ["message"])},
    ]


def call(name, args):
    global GAME
    if GAME is None:
        GAME = TinyShogi()
    if name == "query_board": data = GAME.board()
    elif name == "play_move": data = GAME.play(args.get("move"))
    elif name == "reset_board": data = GAME.reset(args.get("sfen"))
    elif name == "search": data = GAME.search(args.get("nodes", 256), args.get("movetime", 0))
    elif name == "training_start": data = GAME.start_training(args)
    elif name == "training_status": data = GAME.training_status()
    elif name == "training_stop": data = GAME.stop_training()
    elif name == "llm_context":
        data = {"board": GAME.board(), "prompt": "Analyze this shogi position and propose a legal USI move."}
    elif name == "llm_message":
        data = {"message": args.get("message", ""), "context": GAME.board()}
    else: raise ValueError("unknown tool: " + name)
    return result(json.dumps(data, ensure_ascii=False), data)


def main():
    for line in sys.stdin:
        try:
            request = json.loads(line)
            method = request.get("method")
            ident = request.get("id")
            if method == "notifications/initialized": continue
            if method == "initialize":
                response = {"protocolVersion": request.get("params", {}).get("protocolVersion", "2024-11-05"), "capabilities": {"tools": {}, "prompts": {}}, "serverInfo": {"name": "tinyshogi", "version": "1"}}
            elif method == "tools/list": response = {"tools": tools()}
            elif method == "tools/call": response = call(request["params"]["name"], request["params"].get("arguments", {}))
            else: raise ValueError("unsupported method: " + str(method))
            if ident is not None: print(json.dumps({"jsonrpc": "2.0", "id": ident, "result": response}), flush=True)
        except Exception as exc:
            if request.get("id") is not None:
                print(json.dumps({"jsonrpc": "2.0", "id": request["id"], "error": {"code": -32000, "message": str(exc)}}), flush=True)


if __name__ == "__main__": main()
