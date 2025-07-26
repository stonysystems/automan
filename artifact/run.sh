#!/bin/bash
set -e

SCRIPTS=(
  # Figure 11
  # "Figure11-AutoManKV-I0.sh"
  # "Figure11-AutoManKV-I1.sh"
  # "Figure11-IronKV.sh"

  # Figure 12
  "Figure12-PaxosKV-I0.sh"
  "Figure12-PaxosKV-I1.sh"
  "Figure12-RaftKV.sh"

  # Figure 9
  "Figure9-AutoManRSL-I0.sh"
  "Figure9-AutoManRSL-I1.sh"
  "Figure9-IronRSL.sh"

  # Figure 8
  # "Figure8-AutoManRSL-I0.sh"
  # "Figure8-AutoManRSL-I1.sh"
  # "Figure8-IronRSL.sh"
  # "Figure8-AutoManPBFT-I1.sh"
  # "Figure8-AutoManPBFT-I0.sh"
)

for script in "${SCRIPTS[@]}"; do
  echo "======================================"
  echo ">>> Running script: $script"
  echo "======================================"
  bash "$script"
  echo
done

echo "[✓] All experiments completed."
