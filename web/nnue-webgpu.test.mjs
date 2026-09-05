import assert from 'node:assert/strict';

import { WebGpuNnue } from './nnue-webgpu.js';

const FEATURE_COUNT = 81 * 28 * 81 + 2 * 7 * 19;
const writes = [];

globalThis.GPUBufferUsage = {
  STORAGE: 1, COPY_DST: 2, COPY_SRC: 4, MAP_READ: 8, UNIFORM: 16
};
globalThis.GPUMapMode = { READ: 1 };

let validationError = null;
const device = {
  limits: { maxStorageBufferBindingSize: 2 ** 30 },
  lost: new Promise(() => {}),
  pushErrorScope: () => {},
  popErrorScope: async () => validationError,
  queue: { writeBuffer: (...args) => writes.push(args), submit: () => {} },
  createBuffer: spec => ({ ...spec, destroy: () => {} }),
  createShaderModule: () => ({}),
  createComputePipeline: () => ({ getBindGroupLayout: () => ({}) }),
  createBindGroup: () => ({})
};
Object.defineProperty(globalThis, 'navigator', {
  value: { gpu: { requestAdapter: async () => ({ requestDevice: async () => device }) } },
  configurable: true
});

function linearNnue(version, hidden) {
  const headerBytes = version === 1 ? 29 : 33;
  const featureBytes = FEATURE_COUNT * hidden * 2;
  const bytes = new ArrayBuffer(headerBytes + featureBytes + hidden * 2 * 2 + 4);
  const view = new DataView(bytes);
  new Uint8Array(bytes, 0, 5).set(new TextEncoder().encode(`NNUE${version}`));
  view.setUint32(5, version, true);
  view.setUint32(9, FEATURE_COUNT, true);
  view.setUint32(13, hidden, true);
  view.setUint32(17, 2, true);
  view.setInt32(21, 256, true);
  view.setInt32(25, 1024, true);
  if (version === 2) view.setInt32(29, 127, true);
  view.setUint16(headerBytes, 0x1234, true);
  view.setUint16(headerBytes + 2, 0xfedc, true);
  const outputOffset = headerBytes + featureBytes;
  view.setInt16(outputOffset, 100, true);
  view.setInt16(outputOffset + 2, 200, true);
  view.setInt16(outputOffset + 4, 300, true);
  view.setInt16(outputOffset + 6, 400, true);
  view.setInt32(outputOffset + 8, 500, true);
  return bytes;
}

function nnue3(hidden) {
  const headerBytes = 45;
  const featureBytes = FEATURE_COUNT * hidden * 2;
  const headWeightBytes = 2 * hidden * 2;
  const headBiasBytes = 2 * 8;
  const finalWeightBytes = 2 * 2;
  const finalBiasBytes = 2 * 8;
  const bytes = new ArrayBuffer(headerBytes + featureBytes + headWeightBytes + headBiasBytes + finalWeightBytes + finalBiasBytes);
  const view = new DataView(bytes);
  new Uint8Array(bytes, 0, 5).set(new TextEncoder().encode('NNUE3'));
  view.setUint32(5, 3, true);
  view.setUint32(9, FEATURE_COUNT, true);
  view.setUint32(13, hidden, true);
  view.setUint32(17, 1, true);
  view.setUint32(21, 2, true);
  view.setInt32(25, 256, true);
  view.setInt32(29, 256, true);
  view.setInt32(33, 1024, true);
  view.setInt32(37, 127, true);
  view.setInt32(41, 127, true);
  view.setUint16(headerBytes, 0x1234, true);
  view.setUint16(headerBytes + 2, 0xfedc, true);
  const headOffset = headerBytes + featureBytes;
  view.setInt16(headOffset, 100, true);
  view.setInt16(headOffset + 2, 200, true);
  view.setInt16(headOffset + 4, 300, true);
  view.setInt16(headOffset + 6, 400, true);
  const headBiasOffset = headOffset + headWeightBytes;
  view.setBigInt64(headBiasOffset, 1000n, true);
  view.setBigInt64(headBiasOffset + 8, 2000n, true);
  const finalWeightOffset = headBiasOffset + headBiasBytes;
  view.setInt16(finalWeightOffset, 5, true);
  view.setInt16(finalWeightOffset + 2, 6, true);
  const finalBiasOffset = finalWeightOffset + finalWeightBytes;
  view.setBigInt64(finalBiasOffset, 100n, true);
  view.setBigInt64(finalBiasOffset + 8, 200n, true);
  return bytes;
}

async function upload(bytes) {
  writes.length = 0;
  const evaluator = new WebGpuNnue();
  await evaluator.load(bytes);
  const featureWrite = writes[0];
  evaluator.dispose();
  return featureWrite;
}

const evenWrite = await upload(linearNnue(1, 2));
assert.equal(evenWrite.length, 3, 'upload must not pass an unaligned ArrayBuffer offset');
assert.ok(evenWrite[2] instanceof Uint32Array);
assert.equal(evenWrite[2].byteOffset, 0);
assert.equal(evenWrite[2].length, FEATURE_COUNT);
assert.equal(evenWrite[2][0], 0xfedc1234 >>> 0, 'NNUE1 upload must begin at its feature section');

const oddWrite = await upload(linearNnue(1, 3));
assert.equal(oddWrite.length, 3);
assert.ok(oddWrite[2] instanceof Uint32Array);
assert.equal(oddWrite[2].byteOffset, 0);
assert.equal(oddWrite[2].length, FEATURE_COUNT * 2, 'odd widths need one padded word per row');

for (const model of [linearNnue(2, 2), nnue3(2)]) {
  const write = await upload(model);
  assert.equal(write.length, 3, 'format-specific headers must not become GPU source offsets');
  assert.ok(write[2] instanceof Uint32Array);
  assert.equal(write[2].byteOffset, 0);
  assert.equal(write[2][0], 0xfedc1234 >>> 0, 'format-specific feature offset was parsed incorrectly');
}

const scorer = new WebGpuNnue();
await scorer.load(linearNnue(1, 2));
const expectedScore = Math.round(Math.tanh((500 * 256 + 10 * 100 + 20 * 200) / (256 * 1024)) * 1000);
assert.equal(scorer.score(new Int32Array([10, 20]), 0), expectedScore,
  'NNUE1 output weights or bias were parsed at the wrong offset');
scorer.dispose();

const nnue3Scorer = new WebGpuNnue();
await nnue3Scorer.load(nnue3(2));
const headActivation = Math.min(Number((6000n + 128n) >> 8n), 127);
const expectedNnue3Score = Math.round(Math.tanh((100 + headActivation * 5) / (256 * 1024)) * 1000);
assert.equal(nnue3Scorer.score(new Int32Array([10, 20]), 0), expectedNnue3Score,
  'NNUE3 head or final projection was parsed at the wrong offset');
nnue3Scorer.dispose();

validationError = { message: 'synthetic validation error' };
await assert.rejects(
  new WebGpuNnue().load(linearNnue(1, 2)),
  /WebGPU validation failed: synthetic validation error/,
);
validationError = null;

console.log('PASS WebGPU NNUE aligned feature uploads');
