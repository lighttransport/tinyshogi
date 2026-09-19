import createTinyshogi from './build/tinyshogi.js';

const engineReady = createTinyshogi().then(module => {
const api = {
  init: module.cwrap('web_init', null, []),
  setSfen: module.cwrap('web_set_sfen', 'number', ['string']),
  engineMove: module.cwrap('web_engine_move', 'string', ['number']),
  engineNodes: module.cwrap('web_engine_last_nodes', 'number', []),
  engineScore: module.cwrap('web_engine_last_score', 'number', []),
  engineDepth: module.cwrap('web_engine_last_depth', 'number', []),
  engineTime: module.cwrap('web_engine_last_time_ms', 'number', []),
  engineNps: module.cwrap('web_engine_last_nps', 'number', []),
  getSfen: module.cwrap('web_get_sfen', 'string', [])
};
api.init();
return api;
});

self.onmessage = async event => {
  try {
    const request = event.data;
    if (!request || typeof request !== 'object' ||
        typeof request.sfen !== 'string' || request.sfen.length > 511) {
      throw new Error('Invalid engine request');
    }
    if (request.nodes !== undefined && typeof request.nodes !== 'number') {
      throw new Error('Invalid node budget');
    }
    const requestedNodes = Number(request.nodes ?? 64);
    const nodes = Number.isFinite(requestedNodes)
      ? Math.max(1, Math.min(2000000, Math.trunc(requestedNodes))) : 64;
    const api = await engineReady;
    if (!api.setSfen(request.sfen)) throw new Error('Invalid SFEN');
    const move = api.engineMove(nodes);
    self.postMessage({ move, sfen: api.getSfen(), nodes: api.engineNodes(), score: api.engineScore(), depth: api.engineDepth(), timeMs: api.engineTime(), nps: api.engineNps() });
  } catch (error) {
    self.postMessage({ error: error.message || String(error) });
  }
};
