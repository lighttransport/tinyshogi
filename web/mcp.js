/* MCP JSON-RPC adapter for the tinyshogi WASM API.
 * The transport is deliberately separate: callers can use handle() from a
 * browser worker, a WebSocket bridge, or any other JSON-lines transport. */
export const MCP_PROTOCOL_VERSION = '2024-11-05';

const schema = (properties = {}, required = []) => ({ type: 'object', properties, required });
export const MCP_TOOLS = [
  { name: 'query_board', description: 'Return the current board, SFEN, legal moves, and history.', inputSchema: schema() },
  { name: 'legal_moves', description: 'List legal USI moves for the current position.', inputSchema: schema() },
  { name: 'play_move', description: 'Play one legal USI move.', inputSchema: schema({ move: { type: 'string' } }, ['move']) },
  { name: 'reset_board', description: 'Reset to startpos or a supplied SFEN.', inputSchema: schema({ sfen: { type: 'string' } }) },
  { name: 'search', description: 'Search and return the best USI move without changing the position.', inputSchema: schema({ nodes: { type: 'integer', minimum: 1 } }) }
];

function resultText(data) {
  return { content: [{ type: 'text', text: JSON.stringify(data) }], structuredContent: data };
}

export function createWasmMcp(api) {
  if (!api || typeof api.getSfen !== 'function' || typeof api.setSfen !== 'function') {
    throw new TypeError('createWasmMcp requires the tinyshogi WASM API');
  }
  const board = () => {
    const sfen = api.getSfen();
    const fields = String(sfen).trim().split(/\s+/);
    if (fields.length < 4) throw new Error(`invalid SFEN from WASM: ${sfen}`);
    const legal = [];
    const count = typeof api.count === 'function' ? api.count() : 0;
    for (let i = 0; i < count; ++i) {
      const move = typeof api.moveUsi === 'function' ? api.moveUsi(i) : '';
      if (move) legal.push(move);
    }
    const history = [];
    if (typeof api.historyCount === 'function' && typeof api.historyMove === 'function') {
      for (let i = 0; i < api.historyCount(); ++i) history.push(api.historyMove(i));
    }
    return { sfen, board: fields[0], side_to_move: fields[1] === 'b' ? 'black' : 'white',
      hands: fields[2], move_number: Number(fields[3]), legal_moves: legal, moves: history,
      result: typeof api.result === 'function' ? api.result() : 0 };
  };
  const call = (name, args = {}) => {
    if (name === 'query_board') return board();
    if (name === 'legal_moves') return board().legal_moves;
    if (name === 'play_move') {
      if (typeof args.move !== 'string' || !args.move || /\s/.test(args.move)) throw new Error('move must be a USI move string');
      if (!api.playUsi(args.move)) throw new Error(`illegal move: ${args.move}`);
      return board();
    }
    if (name === 'reset_board') {
      const sfen = args.sfen || '';
      if (!sfen) { api.reset(); return board(); }
      if (!api.setSfen(sfen)) throw new Error('invalid SFEN');
      return board();
    }
    if (name === 'search') {
      const nodes = Math.max(1, Math.min(2000000, Number(args.nodes ?? 256) || 256));
      const before = api.getSfen();
      const bestmove = api.engineMove(nodes);
      api.setSfen(before);
      return { bestmove: bestmove || 'resign', nodes: api.engineNodes?.() ?? 0,
        score: api.engineScore?.() ?? 0, depth: api.engineDepth?.() ?? 0,
        timeMs: api.engineTime?.() ?? 0, nps: api.engineNps?.() ?? 0, board: board() };
    }
    throw new Error(`unknown tool: ${name}`);
  };
  const handle = async request => {
    const id = request?.id;
    if (!request || request.jsonrpc !== '2.0' || typeof request.method !== 'string') {
      return id === undefined ? null : { jsonrpc: '2.0', id, error: { code: -32600, message: 'invalid request' } };
    }
    if (request.method === 'notifications/initialized') return null;
    try {
      let value;
      if (request.method === 'initialize') value = { protocolVersion: MCP_PROTOCOL_VERSION, capabilities: { tools: {} }, serverInfo: { name: 'tinyshogi-wasm', version: '1' } };
      else if (request.method === 'ping') value = {};
      else if (request.method === 'tools/list') value = { tools: MCP_TOOLS };
      else if (request.method === 'tools/call') value = resultText(call(request.params?.name, request.params?.arguments));
      else if (request.method === 'shutdown') value = null;
      else throw Object.assign(new Error(`unsupported method: ${request.method}`), { code: -32601 });
      return id === undefined ? null : { jsonrpc: '2.0', id, result: value };
    } catch (error) {
      return id === undefined ? null : { jsonrpc: '2.0', id, error: { code: error.code || -32000, message: error.message || String(error) } };
    }
  };
  return { handle, tools: MCP_TOOLS, board };
}
