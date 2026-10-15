#!/usr/bin/env bash
# Assemble the extractor image: extractor.bin (code, little-endian 32-bit words) and an empty
# extractor.data (no data words). These two files are the submitted image the renderer reads.
set -euo pipefail
cd "$(dirname "$0")"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
riscv64-unknown-elf-as -march=rv64im -o "$T/extractor.o" extractor.S
riscv64-unknown-elf-objcopy -O binary -j .text "$T/extractor.o" extractor.bin
riscv64-unknown-elf-objdump -d -M no-aliases "$T/extractor.o" > extractor.dis
: > extractor.data
echo "extractor image: $(( $(stat -c %s extractor.bin) / 4 )) code words, $(( $(stat -c %s extractor.data) / 8 )) data words"
