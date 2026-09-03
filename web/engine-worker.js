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
  const { sfen, nodes = 64 } = event.data || {};
  let api;
  try {
    api = await engineReady;
  } catch (error) {
    self.postMessage({ error: `Engine initialization failed: ${error.message || error}` });
    return;
  }
  if (!api.setSfen(sfen || '')) {
    self.postMessage({ error: 'Invalid SFEN' });
    return;
  }
  const move = api.engineMove(nodes);
  self.postMessage({ move, sfen: api.getSfen(), nodes: api.engineNodes(), score: api.engineScore(), depth: api.engineDepth(), timeMs: api.engineTime(), nps: api.engineNps() });
};
