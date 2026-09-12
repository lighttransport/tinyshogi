#!/usr/bin/env python3
import json
import os
import subprocess
import sys

engine = sys.argv[1] if len(sys.argv) > 1 else 'build/make/tinyshogi'
proc = subprocess.Popen([sys.executable, 'tools/tinyshogi_mcp.py'], stdin=subprocess.PIPE,
                        stdout=subprocess.PIPE, text=True,
                        env={**os.environ, 'TINYSHOGI_ENGINE': engine})

def call(request):
    proc.stdin.write(json.dumps(request) + '\n')
    proc.stdin.flush()
    return json.loads(proc.stdout.readline())

assert call({'jsonrpc': '2.0', 'id': 1, 'method': 'initialize', 'params': {}})['result']['serverInfo']['name'] == 'tinyshogi-native'
tools = call({'jsonrpc': '2.0', 'id': 2, 'method': 'tools/list'})['result']['tools']
assert any(tool['name'] == 'legal_moves' for tool in tools)
board = call({'jsonrpc': '2.0', 'id': 3, 'method': 'tools/call', 'params': {'name': 'query_board', 'arguments': {}}})['result']['structuredContent']
assert board['legal_moves'] and board['result'] == 'ongoing'
assert call({'jsonrpc': '2.0', 'id': 4, 'method': 'tools/call', 'params': {'name': 'play_move', 'arguments': {'move': board['legal_moves'][0]}}})['result']['structuredContent']['moves']
call({'jsonrpc': '2.0', 'id': 5, 'method': 'shutdown'})
proc.stdin.close()
proc.wait(timeout=5)
print('PASS native MCP adapter')
