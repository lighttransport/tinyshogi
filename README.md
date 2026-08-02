# tinyshogi

Minimal tiny shogi engine in pure C11.

## Build with Meson

```sh
meson setup build
meson compile -C build
meson test -C build
```

## Build with xmake

```sh
xmake f -m release
xmake
```

## Run

```sh
./build/tinyshogi
```

USI commands supported: `usi`, `isready`, `position startpos`, `go`, `d`, `quit`.
