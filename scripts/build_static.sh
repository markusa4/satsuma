#!/usr/bin/env bash
# Run in satsuma/build. Also fetches dejavu into ../src/dejavu, which ganak --symm needs.
set -euo pipefail

rm -rf CMakeCache.txt CMakeFiles cmake_install.cmake Makefile _deps
cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_EXE_LINKER_FLAGS=-static -DCMAKE_EXPORT_COMPILE_COMMANDS=ON ..
make -j$(nproc) satsuma
strip satsuma
