const FEATURE_COUNT = 81 * 28 * 81 + 2 * 7 * 19;
function i16(bytes, offset, count) {
  return new Int16Array(bytes.slice(offset, offset + count * 2));
}

function parseModel(bytes) {
  const view = new DataView(bytes);
  const magic = new TextDecoder().decode(bytes.slice(0, 5));
  if (!['NNUE1', 'NNUE2', 'NNUE3'].includes(magic)) throw new Error('Not a tinyshogi NNUE model');
  let offset = 5;
  const u32 = () => { const n = view.getUint32(offset, true); offset += 4; return n; };
  const i32 = () => { const n = view.getInt32(offset, true); offset += 4; return n; };
  const version = u32(), featureCount = u32(), hidden = u32();
  if (featureCount !== FEATURE_COUNT || hidden === 0 || hidden > 4096) throw new Error('Unsupported NNUE dimensions');
  let headDim = 0;
  if (magic === 'NNUE3') {
    headDim = u32();
    if (u32() !== 2 || headDim === 0 || headDim > 128) throw new Error('Unsupported NNUE3 heads');
    i32(); i32(); i32(); // feature, head, output scales
    const activationClip = i32(), headClip = i32();
    const featureOffset = offset, featureBytes = featureCount * hidden * 2;
    offset += featureBytes;
    const headWeights = i16(bytes, offset, 2 * headDim * hidden); offset += 2 * headDim * hidden * 2;
    const headBias = [];
    for (let n = 0; n < 2 * headDim; ++n) { headBias.push(view.getBigInt64(offset, true)); offset += 8; }
    const finalWeights = i16(bytes, offset, 2 * headDim); offset += 2 * headDim * 2;
    const finalBias = [view.getBigInt64(offset, true), view.getBigInt64(offset + 8, true)];
    return { magic, hidden, featureOffset, featureBytes, headDim, headWeights, headBias, finalWeights, finalBias, activationClip, headClip };
  }
  const featureScale = i32(), outputScale = i32();
  const activationClip = magic === 'NNUE2' ? i32() : 0x7fffffff;
  const featureOffset = offset, featureBytes = featureCount * hidden * 2;
  offset += featureBytes;
  const outputWeights = i16(bytes, offset, hidden * 2); offset += hidden * 2 * 2;
  return { magic, hidden, featureOffset, featureBytes, outputWeights, outputBias: view.getInt32(offset, true), featureScale, outputScale, activationClip };
}

const shader = /* wgsl */`
struct Params { count: u32, hidden: u32 }
@group(0) @binding(0) var<storage, read> weights: array<u32>;
@group(0) @binding(1) var<storage, read> ids: array<u32>;
@group(0) @binding(2) var<storage, read_write> sums: array<i32>;
@group(0) @binding(3) var<uniform> params: Params;
@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
  let unit = gid.x;
  if (unit >= params.hidden) { return; }
  var total: i32 = 0;
  let word = unit / 2u;
  let high = (unit & 1u) != 0u;
  for (var n: u32 = 0u; n < params.count; n++) {
    let packed = weights[ids[n] * ((params.hidden + 1u) / 2u) + word];
    total += select(bitcast<i32>(packed << 16u) >> 16, bitcast<i32>(packed) >> 16, high);
  }
  sums[unit] = total;
}`;

export class WebGpuNnue {
  static available() { return typeof navigator !== 'undefined' && !!navigator.gpu; }

  async load(bytes) {
    if (!WebGpuNnue.available()) throw new Error('WebGPU is not available in this browser');
    const model = parseModel(bytes);
    const adapter = await navigator.gpu.requestAdapter();
    if (!adapter) throw new Error('No WebGPU adapter is available');
    const device = await adapter.requestDevice();
    if (model.featureBytes > device.limits.maxStorageBufferBindingSize) {
      throw new Error(`Model needs ${(model.featureBytes / 1048576).toFixed(0)} MiB GPU storage; this adapter allows ${(device.limits.maxStorageBufferBindingSize / 1048576).toFixed(0)} MiB`);
    }
    this.device = device;
    this.model = model;
    const storage = GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST;
    this.weightBuffer = device.createBuffer({ size: model.featureBytes, usage: storage });
    device.queue.writeBuffer(this.weightBuffer, 0, bytes, model.featureOffset, model.featureBytes);
    this.idBuffer = device.createBuffer({ size: 128 * 4, usage: storage });
    this.sumBuffer = device.createBuffer({ size: model.hidden * 4, usage: storage | GPUBufferUsage.COPY_SRC });
    this.readBuffer = device.createBuffer({ size: model.hidden * 4, usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ });
    this.paramBuffer = device.createBuffer({ size: 8, usage: GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST });
    const module = device.createShaderModule({ code: shader });
    this.pipeline = device.createComputePipeline({ layout: 'auto', compute: { module, entryPoint: 'main' } });
    this.bindGroup = device.createBindGroup({ layout: this.pipeline.getBindGroupLayout(0), entries: [
      { binding: 0, resource: { buffer: this.weightBuffer } }, { binding: 1, resource: { buffer: this.idBuffer } },
      { binding: 2, resource: { buffer: this.sumBuffer } }, { binding: 3, resource: { buffer: this.paramBuffer } }
    ] });
    device.lost.then(info => { this.failure = `WebGPU device lost: ${info.message || info.reason}`; });
    return `${model.magic}, ${model.hidden} hidden units`;
  }

  async evaluate(featureIds, perspective) {
    if (!this.device || this.failure) throw new Error(this.failure || 'No NNUE model loaded');
    if (featureIds.length > 128) throw new Error('Too many NNUE features');
    const ids = new Uint32Array(128); ids.set(featureIds);
    this.device.queue.writeBuffer(this.idBuffer, 0, ids);
    this.device.queue.writeBuffer(this.paramBuffer, 0, new Uint32Array([featureIds.length, this.model.hidden]));
    const encoder = this.device.createCommandEncoder();
    const pass = encoder.beginComputePass(); pass.setPipeline(this.pipeline); pass.setBindGroup(0, this.bindGroup);
    pass.dispatchWorkgroups(Math.ceil(this.model.hidden / 64)); pass.end();
    encoder.copyBufferToBuffer(this.sumBuffer, 0, this.readBuffer, 0, this.model.hidden * 4);
    this.device.queue.submit([encoder.finish()]);
    await this.readBuffer.mapAsync(GPUMapMode.READ);
    const sum = new Int32Array(this.readBuffer.getMappedRange().slice(0)); this.readBuffer.unmap();
    return this.score(sum, perspective);
  }

  score(sum, perspective) {
    const m = this.model;
    if (m.magic !== 'NNUE3') {
      let raw = BigInt(m.outputBias);
      const base = perspective * m.hidden;
      for (let i = 0; i < m.hidden; ++i) raw += BigInt(Math.min(Math.max(sum[i], 0), m.activationClip)) * BigInt(m.outputWeights[base + i]);
      return Math.round(Math.tanh(Number(raw) / (m.featureScale * m.outputScale)) * 1000);
    }
    let raw = m.finalBias[perspective];
    for (let head = 0; head < m.headDim; ++head) {
      let value = m.headBias[perspective * m.headDim + head];
      const base = (perspective * m.headDim + head) * m.hidden;
      for (let i = 0; i < m.hidden; ++i) value += BigInt(Math.min(Math.max(sum[i], 0), m.activationClip)) * BigInt(m.headWeights[base + i]);
      let activated = value > 0n ? Number((value + 128n) >> 8n) : 0;
      activated = Math.min(activated, m.headClip);
      raw += BigInt(activated) * BigInt(m.finalWeights[perspective * m.headDim + head]);
    }
    return Math.round(Math.tanh(Number(raw) / (256 * 1024)) * 1000);
  }
}
