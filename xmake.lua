set_languages("c11")

add_rules("mode.debug", "mode.release")

target("tinyshogi")
    set_kind("binary")
    add_files("src/main.c")
