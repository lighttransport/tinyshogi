set_languages("c11")

add_rules("mode.debug", "mode.release")

target("tinyshogi")
    set_kind("binary")
    add_files("src/main.c", "src/search.c", "src/shogi.c", "src/thread_posix.c")
    add_syslinks("pthread", "m")

target("tinyshogi-rules-test")
    set_kind("binary")
    add_files("tests/test_rules.c", "src/shogi.c")
    add_syslinks("pthread", "m")

target("tinyshogi-search-test")
    set_kind("binary")
    add_files("tests/test_search.c", "src/search.c", "src/shogi.c", "src/thread_posix.c")
    add_syslinks("pthread", "m")

target("tinyshogi-integer-test")
    set_kind("binary")
    add_files("tests/test_int.c", "src/int_math.c", "src/int_model.c")
    add_syslinks("m")
