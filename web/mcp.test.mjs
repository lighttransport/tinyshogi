import assert from 'node:assert/strict';
import { createWasmMcp } from './mcp.js';

let sfen = 'lnsgkgsnl/1r5b1/p1ppppp1p/7p1/9/9/P1PPPPP1P/1B5R1/LNSGKGSNL b - 1';
let searchedNodes = 0;
const api = {
  getSfen: () => sfen,
  setSfen: value => { if (!value.includes(' ')) return 0; sfen = value; return 1; },
  reset: () => { sfen = 'startpos b - 1'; },
  count: () => 1,
  moveUsi: () => '7g7f',
  playUsi: move => move === '7g7f' ? (sfen = sfen.replace(' b ', ' w '), 1) : 0,
  historyCount: () => 0,
  historyMove: () => '',
  result: () => 0,
  engineMove: nodes => {
    searchedNodes = nodes;
    if (nodes === 13) { sfen = 'changed'; throw new Error('search failed'); }
    return '７七６六';
  }, engineNodes: () => 12, engineScore: () => 3,
  engineDepth: () => 2, engineTime: () => 1, engineNps: () => 12000
};
const mcp = createWasmMcp(api);
const init = await mcp.handle({ jsonrpc: '2.0', id: 1, method: 'initialize', params: {} });
assert.equal(init.result.serverInfo.name, 'tinyshogi-wasm');
const listed = await mcp.handle({ jsonrpc: '2.0', id: 2, method: 'tools/list' });
assert.ok(listed.result.tools.some(tool => tool.name === 'legal_moves'));
const board = await mcp.handle({ jsonrpc: '2.0', id: 3, method: 'tools/call', params: { name: 'query_board', arguments: {} } });
assert.deepEqual(board.result.structuredContent.legal_moves, ['7g7f']);
assert.equal((await mcp.handle({ jsonrpc: '2.0', id: 4, method: 'tools/call', params: { name: 'play_move', arguments: { move: 'bad' } } })).error.code, -32000);
assert.equal((await mcp.handle({ jsonrpc: '2.0', id: 5, method: 'tools/call', params: { name: 'search', arguments: { nodes: Infinity } } })).error.code, -32000);
assert.equal((await mcp.handle({ jsonrpc: '2.0', id: 6, method: 'tools/call', params: { name: 'reset_board', arguments: { sfen: 12 } } })).error.code, -32000);
await mcp.handle({ jsonrpc: '2.0', id: 7, method: 'tools/call', params: { name: 'search', arguments: { nodes: 3000000 } } });
assert.equal(searchedNodes, 2000000);
assert.equal((await mcp.handle({ jsonrpc: '2.0', id: 8, method: 'tools/call', params: { name: 'search', arguments: { nodes: '10' } } })).error.code, -32000);
assert.equal((await mcp.handle({ jsonrpc: '2.0', id: 9, method: 'tools/call', params: { name: 'play_move', arguments: { move: '7g7f'.repeat(1000) } } })).error.code, -32000);
const beforeFailure = sfen;
assert.equal((await mcp.handle({ jsonrpc: '2.0', id: 10, method: 'tools/call', params: { name: 'search', arguments: { nodes: 13 } } })).error.code, -32000);
assert.equal(sfen, beforeFailure);
assert.equal(await mcp.handle({ jsonrpc: '2.0', method: 'notifications/initialized' }), null);
console.log('PASS WASM MCP adapter');
