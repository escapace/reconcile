#!/bin/sh
# The C compiler of the check rounds' Lean builds: Lake's generated C and its linking unchanged,
# without optimization, so that the round's budget is not spent optimizing the hundreds of
# metaprogramming modules the oracle imports. Not the compiler of the TypeScript package. A link
# finds the toolchain's libraries under LEAN_SYSROOT, or else where `lean` says it is installed.
for argument in "$@"; do
  if [ "$argument" = -c ]; then exec cc "$@" -O0; fi
done
sysroot=${LEAN_SYSROOT:-$(lean --print-prefix)} || exit 1
libraries="$sysroot/lib"
if [ ! -d "$libraries" ]; then
  echo "Missing Lean toolchain libraries: $libraries" >&2
  exit 1
fi
exec cc "$@" "-L$libraries" "-Wl,-rpath,$libraries" -O0
