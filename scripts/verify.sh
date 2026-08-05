#!/usr/bin/env bash
set -euo pipefail

export PATH="${HOME}/.elan/bin:${PATH}"

lake build
lake env lean BlackPegExtraCheck/DecisionTree.lean
lake env lean BlackPegExtraCheck/TenFieldsElevenColors.lean
