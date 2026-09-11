import createTinyshogi from './build/tinyshogi.js';

const engineReady = createTinyshogi().then(module => {
  return fetch(new URL(/* @vite-ignore */ '../nn.bin', import.meta.url))
    .then(response => {
      if (!response.ok) throw new Error(`NNUE model request failed (${response.status})`);
      return response.arrayBuffer();
    })
    .then(buffer => {
      module.FS.writeFile('/nn.bin', new Uint8Array(buffer));
      return module;
    })
    .catch(error => {
      console.warn(`WASM NNUE unavailable; using material evaluator: ${error.message || error}`);
      return module;
    });
}).then(module => {
const api = {
  init: module.cwrap('web_init', null, []),
  setSfen: module.cwrap('web_set_sfen', 'number', ['string']),
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
return api;
});

self.onmessage = async event => {
  const { mode = 'move', sfen, nodes = 64, maxPlies = 1000 } = event.data || {};
  let api;
  try {
    api = await engineReady;
  } catch (error) {
    self.postMessage({ error: `Engine initialization failed: ${error.message || error}`, autoplay: mode === 'autoplay' });
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
