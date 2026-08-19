#!/usr/bin/env bash
set -euo pipefail

export PATH="${HOME}/.elan/bin:${PATH}"

lake build
lake env lean BlackPegExtraCheck/DecisionTree.lean
lake env lean BlackPegExtraCheck/TenFieldsElevenColors.lean
lake env lean BlackPegExtraCheck/FiveZeroBridge.lean
lake env lean BlackPegExtraCheck/ExactFiberCapacity.lean
lake env lean BlackPegExtraCheck/AggregateFourPathBridge.lean
lake env lean BlackPegExtraCheck/RegularMarginalStructure.lean
lake env lean BlackPegExtraCheck/RegularQueryClass.lean
lake env lean BlackPegExtraCheck/RegularCompletionObstruction.lean
lake env lean BlackPegExtraCheck/Separator.lean
lake env lean BlackPegExtraCheck/SeparatorTransport.lean
lake env lean BlackPegExtraCheck/CyclicStrategy.lean
lake env lean BlackPegExtraCheck/SharpEightRookCertificate.lean
python3 research/ten-fields-eleven-colors/five_zero_survivor_probe.py
python3 research/ten-fields-eleven-colors/switching_layer_counterexample.py
python3 research/ten-fields-eleven-colors/overlap_marginal_counterexample.py
g++ -std=c++2a -O3 research/ten-fields-eleven-colors/verify_eight_rook_sep3.cpp -o /tmp/verify_eight_rook_sep3
/tmp/verify_eight_rook_sep3
g++ -std=c++2a -O3 research/ten-fields-eleven-colors/verify_nine_rook_sep4.cpp -o /tmp/verify_nine_rook_sep4
/tmp/verify_nine_rook_sep4
