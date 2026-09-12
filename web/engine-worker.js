import createTinyshogi from './build/tinyshogi.js';
import { createWasmMcp } from './mcp.js';

const engineReady = createTinyshogi().then(module => {
const api = {
  init: module.cwrap('web_init', null, []),
  reset: module.cwrap('web_reset', null, []),
  setSfen: module.cwrap('web_set_sfen', 'number', ['string']),
  playUsi: module.cwrap('web_play_usi', 'number', ['string']),
  count: module.cwrap('web_legal_move_count', 'number', []),
  moveUsi: module.cwrap('web_move_usi', 'string', ['number']),
  historyCount: module.cwrap('web_history_count', 'number', []),
  historyMove: module.cwrap('web_history_move', 'string', ['number']),
  engineMove: module.cwrap('web_engine_move', 'string', ['number']),
  engineNodes: module.cwrap('web_engine_last_nodes', 'number', []),
  engineScore: module.cwrap('web_engine_last_score', 'number', []),
  engineDepth: module.cwrap('web_engine_last_depth', 'number', []),
  engineTime: module.cwrap('web_engine_last_time_ms', 'number', []),
  engineNps: module.cwrap('web_engine_last_nps', 'number', []),
  nnueActive: module.cwrap('web_nnue_active', 'number', []),
  gameResult: module.cwrap('web_game_result', 'number', []),
  getSfen: module.cwrap('web_get_sfen', 'string', [])
};
api.init();
return { api, module, mcp: createWasmMcp(api) };
});

self.onmessage = async event => {
  const { mode = 'move', sfen, nodes = 64, maxPlies = 1000, buffer } = event.data || {};
  let engine;
  try {
    engine = await engineReady;
  } catch (error) {
    self.postMessage({ error: `Engine initialization failed: ${error.message || error}`, autoplay: mode === 'autoplay' });
    return;
  }
  const { api, module, mcp } = engine;
  if (mode === 'mcp') {
    const response = await mcp.handle(event.data.request);
    if (response) self.postMessage({ mcp: response });
    return;
  }
  if (mode === 'load-model') {
    try {
      if (!buffer) throw new Error('no NNUE model data received');
      module.FS.writeFile('/nn.bin', new Uint8Array(buffer));
      api.init();
      self.postMessage({ model: true, nnue: Boolean(api.nnueActive()) });
    } catch (error) {
      self.postMessage({ model: true, error: `WASM NNUE load failed: ${error.message || error}` });
    }
    return;
  }
  if (!api.setSfen(sfen || '')) {
    self.postMessage({ error: 'Invalid SFEN', autoplay: mode === 'autoplay' });
    return;
  }
  if (mode === 'autoplay') {
    const moves = [];
    let reason = 'move-limit';
    const limit = Math.max(1, Math.min(1000, Number(maxPlies) || 1000));
    for (let ply = 0; ply < limit; ++ply) {
      const result = api.gameResult();
      if (result !== 0) {
        reason = result === 1 ? 'black-wins' : result === 2 ? 'white-wins' : 'draw';
        break;
      }
      const move = api.engineMove(nodes);
      if (!move) {
        reason = api.gameResult() === 0 ? 'search-error' : 'terminal';
        break;
      }
      moves.push(move);
      const resultAfterMove = api.gameResult();
      if (resultAfterMove !== 0) {
        reason = resultAfterMove === 1 ? 'black-wins' : resultAfterMove === 2 ? 'white-wins' : 'draw';
        break;
      }
    }
    self.postMessage({ autoplay: true, moves, sfen: api.getSfen(), plies: moves.length,
      reason, nnue: Boolean(api.nnueActive()), nodes: api.engineNodes(),
      score: api.engineScore(), depth: api.engineDepth(), timeMs: api.engineTime(), nps: api.engineNps() });
    return;
  }
  const move = api.engineMove(nodes);
  self.postMessage({ move, sfen: api.getSfen(), nodes: api.engineNodes(), score: api.engineScore(), depth: api.engineDepth(), timeMs: api.engineTime(), nps: api.engineNps(), nnue: Boolean(api.nnueActive()) });
};
