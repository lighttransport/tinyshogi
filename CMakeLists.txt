cmake_minimum_required(VERSION 3.16)

project(tinyshogi VERSION 0.2.0 LANGUAGES C)

include(CTest)
find_package(Threads REQUIRED)
include(CheckIncludeFile)

set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

option(TINYSHOGI_BUILD_BENCHMARKS "Build benchmark programs" ON)
option(TINYSHOGI_BUILD_EXAMPLES "Build evaluator plugin examples" ON)

set(TINYSHOGI_WARNINGS -Wall -Wextra -Wpedantic)
set(TINYSHOGI_ENGINE_SOURCES
    src/main.c
    src/search.c
    src/shogi.c
    src/nnue.c
    src/simd.c
    src/eval.c
    src/thread_posix.c
)

set(TINYSHOGI_COMMON_LIBS Threads::Threads m ${CMAKE_DL_LIBS})

function(tinyshogi_target target)
  add_executable(${target} ${ARGN})
  target_include_directories(${target} PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src)
  target_compile_options(${target} PRIVATE ${TINYSHOGI_WARNINGS})
  target_link_libraries(${target} PRIVATE ${TINYSHOGI_COMMON_LIBS})
endfunction()

tinyshogi_target(tinyshogi ${TINYSHOGI_ENGINE_SOURCES})
set_target_properties(tinyshogi PROPERTIES ENABLE_EXPORTS ON)

if(BUILD_TESTING)
  tinyshogi_target(tinyshogi-rules-test tests/test_rules.c src/shogi.c)
  add_test(NAME rules COMMAND tinyshogi-rules-test)

  tinyshogi_target(tinyshogi-search-test
                   tests/test_search.c src/search.c src/shogi.c src/eval.c
                   src/thread_posix.c)
  add_test(NAME search COMMAND tinyshogi-search-test)
  tinyshogi_target(tinyshogi-search-hash-test
                   tests/test_search_hash.c src/shogi.c src/eval.c src/thread_posix.c)
  add_test(NAME search-hash COMMAND tinyshogi-search-hash-test)

  tinyshogi_target(tinyshogi-nnue-test tests/test_nnue.c src/nnue.c src/simd.c src/shogi.c)
  add_test(NAME nnue COMMAND tinyshogi-nnue-test)

  tinyshogi_target(tinyshogi-brute-test tests/test_brute.c src/brute.c src/shogi.c)
  add_test(NAME brute COMMAND tinyshogi-brute-test)

  tinyshogi_target(tinyshogi-integer-test
                   tests/test_int.c src/int_math.c src/int_model.c src/simd.c)
  add_test(NAME integer COMMAND tinyshogi-integer-test)

  tinyshogi_target(tinyshogi-integer-batch-test
                   tests/test_int_batch.c src/int_math.c src/int_model.c src/simd.c)
  add_test(NAME integer-batch COMMAND tinyshogi-integer-batch-test)

  tinyshogi_target(tinyshogi-simd-test tests/test_simd.c src/simd.c)
  add_test(NAME simd COMMAND tinyshogi-simd-test)

  add_test(NAME selftest COMMAND tinyshogi --selftest)
  find_package(Python3 COMPONENTS Interpreter)
  if(Python3_Interpreter_FOUND)
    add_test(NAME match-tools COMMAND ${Python3_EXECUTABLE} -B
             ${CMAKE_CURRENT_SOURCE_DIR}/tests/test_match_tools.py $<TARGET_FILE:tinyshogi>)
    add_test(NAME mcp COMMAND ${Python3_EXECUTABLE} -B
             ${CMAKE_CURRENT_SOURCE_DIR}/tests/test_mcp.py $<TARGET_FILE:tinyshogi>)
  endif()

  tinyshogi_target(tinyshogi-yaneuraou-nnue-test
                   tests/test_yaneuraou_nnue.c
                   examples/yaneuraou_nnue_direct.c src/shogi.c src/eval.c)
  add_test(NAME yaneuraou-nnue COMMAND tinyshogi-yaneuraou-nnue-test)
endif()

if(TINYSHOGI_BUILD_BENCHMARKS)
  tinyshogi_target(tinyshogi-simd-bench bench/simd_bench.c src/simd.c)
  tinyshogi_target(tinyshogi-nnue-state-bench
                   bench/nnue_state_bench.c src/nnue.c src/simd.c src/shogi.c)
  tinyshogi_target(tinyshogi-nnue-batch-bench
                   bench/nnue_batch_bench.c src/nnue.c src/simd.c src/shogi.c)
endif()

if(TINYSHOGI_BUILD_EXAMPLES)
  add_library(tinyshogi-eval-plugin MODULE examples/tinyshogi_eval_plugin.c)
  target_include_directories(tinyshogi-eval-plugin PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src)
  target_compile_options(tinyshogi-eval-plugin PRIVATE ${TINYSHOGI_WARNINGS})

  add_library(tinyshogi-yaneuraou-nnue-direct MODULE examples/yaneuraou_nnue_direct.c)
  target_include_directories(tinyshogi-yaneuraou-nnue-direct PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src)
  target_compile_options(tinyshogi-yaneuraou-nnue-direct PRIVATE ${TINYSHOGI_WARNINGS})

  add_library(tinyshogi-yaneuraou-eval-adapter MODULE examples/yaneuraou_eval_adapter.c)
  target_include_directories(tinyshogi-yaneuraou-eval-adapter PRIVATE ${CMAKE_CURRENT_SOURCE_DIR}/src)
  target_compile_options(tinyshogi-yaneuraou-eval-adapter PRIVATE ${TINYSHOGI_WARNINGS})
  target_link_libraries(tinyshogi-yaneuraou-eval-adapter PRIVATE Threads::Threads)
endif()
