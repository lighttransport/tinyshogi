"""USI transport with bounded deadlines and concurrent stdout/stderr draining."""

import json
import os
import re
import selectors
import subprocess
import time
from collections import deque


class Engine:
    def __init__(self, name, path, options, timeout, environment=None, cpu_affinity=None):
        self.name = name
        self.path = str(path)
        self.timeout = timeout
        self.last_nodes = None
        self.last_info = {}
        self.last_elapsed_ms = 0
        self.identity = []
        self.advertised = set()
        self.option_specs = {}
        self.options = {}
        self.diagnostics = deque(maxlen=30)
        self.pending = bytearray()
        self.process = subprocess.Popen(
            [self.path], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0, env=environment)
        self.selector = selectors.DefaultSelector()
        for stream in (self.process.stdout, self.process.stderr):
            os.set_blocking(stream.fileno(), False)
            self.selector.register(stream, selectors.EVENT_READ)
        try:
            if cpu_affinity is not None:
                os.sched_setaffinity(self.process.pid, cpu_affinity)
            self.cpu_affinity = (sorted(os.sched_getaffinity(self.process.pid))
                                 if hasattr(os, "sched_getaffinity") else None)
            self.send("usi")
            self.read_until("usiok")
            for key, value in options.items():
                if key not in self.advertised:
                    raise RuntimeError(f"{name} does not advertise option {key}")
                self.validate_option(key, value)
                self.send(f"setoption name {key} value {value}")
                self.options[key] = str(value)
            self.send("isready")
            self.read_until("readyok")
        except BaseException:
            self.close()
            raise

    def validate_option(self, name, value):
        kind, specification = self.option_specs[name]
        value = str(value)
        if kind == "spin":
            minimum = re.search(r"(?:^| )min (-?\d+)(?: |$)", specification)
            maximum = re.search(r"(?:^| )max (-?\d+)(?: |$)", specification)
            if (not re.fullmatch(r"-?\d+", value) or
                    minimum and int(value) < int(minimum[1]) or
                    maximum and int(value) > int(maximum[1])):
                raise ValueError(f"invalid {name} value: {value}")
        elif kind == "check" and value not in ("true", "false"):
            raise ValueError(f"invalid {name} boolean: {value}")
        elif kind == "combo":
            choices = re.findall(r"(?:^| )var (.*?)(?= var |$)", specification)
            if value not in choices:
                raise ValueError(f"invalid {name} choice: {value} (expected {choices})")
        elif kind == "button":
            raise ValueError(f"button options cannot configure a match: {name}")

    def send(self, command):
        if "\n" in command or "\r" in command:
            raise ValueError("embedded newline in USI command")
        if self.process.poll() is not None:
            raise RuntimeError(f"{self.name} exited with status {self.process.returncode}")
        try:
            self.process.stdin.write((command + "\n").encode())
            self.process.stdin.flush()
        except BrokenPipeError as error:
            raise RuntimeError(f"{self.name} closed stdin") from error

    def _line(self, deadline):
        while True:
            if time.monotonic() >= deadline:
                raise RuntimeError(f"timeout reading {self.name}: {list(self.diagnostics)}")
            if b"\n" in self.pending:
                line, _, rest = self.pending.partition(b"\n")
                self.pending = bytearray(rest)
                return line.decode(errors="replace").strip()
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise RuntimeError(f"timeout reading {self.name}: {list(self.diagnostics)}")
            for key, _ in self.selector.select(remaining):
                block = os.read(key.fd, 65536)
                if not block:
                    self.selector.unregister(key.fileobj)
                    if key.fileobj is self.process.stdout:
                        raise RuntimeError(f"{self.name} closed stdout: {list(self.diagnostics)}")
                elif key.fileobj is self.process.stdout:
                    self.pending.extend(block)
                    if len(self.pending) > 4 * 1024 * 1024:
                        raise RuntimeError(f"oversized output from {self.name}")
                else:
                    self.diagnostics.append(block.decode(errors="replace")[-4000:])

    def read_until(self, marker):
        deadline = time.monotonic() + self.timeout
        while True:
            line = self._line(deadline)
            self.diagnostics.append(line[-4000:])
            if line.startswith("id "):
                self.identity.append(line)
            option = re.match(r"option name (.*?) type (\w+)(?: (.*))?$", line)
            if option:
                self.advertised.add(option[1])
                self.option_specs[option[1]] = (option[2], option[3] or "")
            for field in ("nodes", "depth", "seldepth", "time", "nps", "mainnodes", "qnodes",
                          "rootnodes", "ttcutoffs", "transcutoffs", "evaluations", "evalhits",
                          "iterations", "interrupted", "recaptures", "ttreplacements", "ttretained",
                          "rootreductions", "rootresearches", "qpruned"):
                value = re.search(r"(?:^| )" + field + r" (\d+)(?: |$)", line)
                if value:
                    self.last_info[field] = int(value[1])
                    if field == "nodes":
                        self.last_nodes = int(value[1])
            score = re.search(r"score (cp|mate) (-?\d+)", line)
            if score:
                self.last_info["score"] = {"kind": score[1], "value": int(score[2])}
            if any(token in line.lower() for token in (
                    "load failed", "failed to read", "hash mismatch", "invalid position", "error!")):
                raise RuntimeError(f"{self.name}: {line}")
            if line == marker or line.startswith(marker + " "):
                return line

    def read_sfen(self):
        deadline = time.monotonic() + self.timeout
        while True:
            line = self._line(deadline)
            if len(line.split()) == 4 and "/" in line:
                return line
            if "invalid position" in line:
                raise RuntimeError(f"{self.name}: {line}")

    def set_position(self, position, moves=None):
        if isinstance(position, str):
            command = "position sfen " + position
        else:
            command = "position startpos"
            moves = list(position or ()) + list(moves or ())
        if moves:
            command += " moves " + " ".join(moves)
        self.send(command)

    def bestmove(self, position, limit, moves=None):
        self.last_nodes = None
        self.last_info = {}
        self.set_position(position, moves)
        start = time.monotonic()
        self.send("go " + limit)
        line = self.read_until("bestmove")
        self.last_elapsed_ms = (time.monotonic() - start) * 1000
        fields = line.split()
        if len(fields) < 2:
            raise RuntimeError(f"malformed bestmove from {self.name}: {line}")
        return fields[1]

    def status(self, position, moves=None):
        self.set_position(position, moves)
        self.send("status")
        return json.loads(self.read_until("info string status").split("status ", 1)[1])

    def new_game(self):
        self.send("usinewgame")
        self.send("isready")
        self.read_until("readyok")

    def close(self):
        if self.process.poll() is None:
            try:
                self.send("quit")
                self.process.wait(timeout=2)
            except (BrokenPipeError, RuntimeError, subprocess.TimeoutExpired):
                self.process.kill()
                self.process.wait(timeout=2)
        self.selector.close()
        for stream in (self.process.stdin, self.process.stdout, self.process.stderr):
            stream.close()
