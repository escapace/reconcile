#!/bin/sh
# The C compiler of the check rounds' Lean builds: Lake's generated C and its linking unchanged,
# without optimization, so that the round's budget is not spent optimizing the hundreds of
# metaprogramming modules the oracle imports. Not the compiler of the TypeScript package.
for argument in "$@"; do
  if [ "$argument" = -c ]; then exec cc "$@" -O0; fi
done
libraries="$LEAN_SYSROOT/lib"
if [ ! -d "$libraries" ]; then
  echo "Missing Lean toolchain libraries: $libraries" >&2
  exit 1
fi
exec cc "$@" "-L$libraries" "-Wl,-rpath,$libraries" -O0
