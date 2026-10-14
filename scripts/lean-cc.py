#!/usr/bin/env python3
"""Compile check-only Lean executables without optimizing proof/tactic dependencies.

Lake's generated C and ordinary linking are unchanged. Avoid spending the bounded
check budget optimizing hundreds of imported metaprogramming modules. This is
not the compiler used to build the TypeScript package.
"""

import os
import pathlib
import sys

args = sys.argv[1:]
if "-c" not in args:
    libraries = pathlib.Path(os.environ["LEAN_SYSROOT"]) / "lib"
    if not libraries.is_dir():
        raise RuntimeError(f"Missing Lean toolchain libraries: {libraries}")
    args += [f"-L{libraries}", f"-Wl,-rpath,{libraries}"]
os.execvp("cc", ["cc", *args, "-O0"])
