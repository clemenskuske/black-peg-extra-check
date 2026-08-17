#!/usr/bin/env bash
set -euo pipefail

export PATH="${HOME}/.elan/bin:${PATH}"

lake build
lake env lean BlackPegExtraCheck/DecisionTree.lean
lake env lean BlackPegExtraCheck/TenFieldsElevenColors.lean
lake env lean BlackPegExtraCheck/FiveZeroBridge.lean
lake env lean BlackPegExtraCheck/Separator.lean
lake env lean BlackPegExtraCheck/CyclicStrategy.lean
lake env lean BlackPegExtraCheck/SharpEightRookCertificate.lean
python3 research/ten-fields-eleven-colors/five_zero_survivor_probe.py
