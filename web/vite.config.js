import { defineConfig } from 'vite';

export default defineConfig({
  // The production bundle can be served from any static subdirectory.
  base: './',
  // Serve/copy the repository's external NNUE weights as /nn.bin.
  publicDir: '../eval/hao/eval',
  build: {
    target: 'esnext',
    rollupOptions: {
      output: { format: 'es' }
    }
  }
});
