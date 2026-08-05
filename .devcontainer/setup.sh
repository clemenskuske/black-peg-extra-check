#!/usr/bin/env bash
set -euo pipefail

if ! command -v elan >/dev/null 2>&1; then
  curl --proto '=https' --tlsv1.2 -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi

export PATH="${HOME}/.elan/bin:${PATH}"

lake exe cache get
bash scripts/verify.sh
