project('tinyshogi', 'c',
  version : '0.2.0',
  default_options : ['c_std=c11', 'warning_level=3']
)

cc = meson.get_compiler('c')
threads_dep = dependency('threads')
math_dep = cc.find_library('m')
dl_dep = cc.find_library('dl', required : false)
engine_sources = files(
  'src/main.c',
  'src/search.c',
  'src/shogi.c',
  'src/nnue.c',
  'src/simd.c',
  'src/eval.c',
  'src/thread_posix.c'
)

tinyshogi = executable('tinyshogi', engine_sources, dependencies : [threads_dep, math_dep, dl_dep],
  link_args : ['-rdynamic'], install : false)
test('selftest', tinyshogi, args : ['--selftest'])

rules_test = executable('tinyshogi-rules-test', 'tests/test_rules.c',
  sources : ['src/shogi.c'], dependencies : [threads_dep, math_dep], install : false)
test('rules', rules_test)

search_test = executable('tinyshogi-search-test', 'tests/test_search.c',
  sources : ['src/search.c', 'src/shogi.c', 'src/eval.c', 'src/thread_posix.c'],
  dependencies : [threads_dep, math_dep, dl_dep], install : false)
test('search', search_test)

nnue_test = executable('tinyshogi-nnue-test', 'tests/test_nnue.c',
  sources : ['src/nnue.c', 'src/simd.c', 'src/shogi.c'], dependencies : [math_dep], install : false)
test('nnue', nnue_test)

brute_test = executable('tinyshogi-brute-test', 'tests/test_brute.c',
  sources : ['src/brute.c', 'src/shogi.c'], dependencies : [math_dep], install : false)
test('brute', brute_test)

integer_test = executable('tinyshogi-integer-test', 'tests/test_int.c',
  sources : ['src/int_math.c', 'src/int_model.c', 'src/simd.c'], dependencies : [math_dep], install : false)
test('integer', integer_test)

integer_batch_test = executable('tinyshogi-integer-batch-test',
  'tests/test_int_batch.c',
  sources : ['src/int_math.c', 'src/int_model.c', 'src/simd.c'],
  dependencies : [math_dep], install : false)
test('integer-batch', integer_batch_test)

simd_test = executable('tinyshogi-simd-test', 'tests/test_simd.c',
  sources : ['src/simd.c'], install : false)
test('simd', simd_test)

simd_bench = executable('tinyshogi-simd-bench', 'bench/simd_bench.c',
  sources : ['src/simd.c'], install : false)
benchmark('simd', simd_bench)

nnue_state_bench = executable('tinyshogi-nnue-state-bench',
  'bench/nnue_state_bench.c',
  sources : ['src/nnue.c', 'src/simd.c', 'src/shogi.c'],
  dependencies : [math_dep], install : false)
benchmark('nnue-state', nnue_state_bench)

nnue_batch_bench = executable('tinyshogi-nnue-batch-bench',
  'bench/nnue_batch_bench.c',
  sources : ['src/nnue.c', 'src/simd.c', 'src/shogi.c'],
  dependencies : [math_dep], install : false)
benchmark('nnue-batch', nnue_batch_bench)

perpetual_bench = executable('tinyshogi-perpetual-bench',
  'bench/perpetual_check_bench.c',
  sources : ['src/search.c', 'src/shogi.c', 'src/nnue.c', 'src/simd.c',
             'src/eval.c', 'src/thread_posix.c'],
  dependencies : [threads_dep, math_dep, dl_dep], install : false)
benchmark('perpetual-check', perpetual_bench)
