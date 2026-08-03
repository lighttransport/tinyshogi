project('tinyshogi', 'c',
  version : '0.2.0',
  default_options : ['c_std=c11', 'warning_level=3']
)

cc = meson.get_compiler('c')
threads_dep = dependency('threads')
math_dep = cc.find_library('m')
engine_sources = files(
  'src/main.c',
  'src/search.c',
  'src/shogi.c',
  'src/thread_posix.c'
)

tinyshogi = executable('tinyshogi', engine_sources, dependencies : [threads_dep, math_dep], install : false)
test('selftest', tinyshogi, args : ['--selftest'])

rules_test = executable('tinyshogi-rules-test', 'tests/test_rules.c',
  sources : ['src/shogi.c'], dependencies : [threads_dep, math_dep], install : false)
test('rules', rules_test)

search_test = executable('tinyshogi-search-test', 'tests/test_search.c',
  sources : ['src/search.c', 'src/shogi.c', 'src/thread_posix.c'],
  dependencies : [threads_dep, math_dep], install : false)
test('search', search_test)
