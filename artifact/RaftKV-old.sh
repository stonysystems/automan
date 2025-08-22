#!/bin/bash
set -e

RESULT_DIR="Figure12"
CODE_DIR="pgo"
Line="PGo-RaftKV"
PARAM_DIR="$CODE_DIR/raftkvs"
mkdir -p "$RESULT_DIR"

echo -n "" > "$RESULT_DIR/$Line.txt"

for i in {1..7}; do
  echo "=============================="
  echo ">>> Running experiment with $i client(s)"
  echo "=============================="

  CONFIG_FILE="$PARAM_DIR/configs/test-3-$i.yaml"

  $PARAM_DIR/server -srvId 1 -c "$CONFIG_FILE" &
  PID1=$!
  $PARAM_DIR/server -srvId 2 -c "$CONFIG_FILE" &
  PID2=$!
  $PARAM_DIR/server -srvId 3 -c "$CONFIG_FILE" &
  PID3=$!

  sleep 3

  client_pids=()
  for ((cid = 1; cid <= i; cid++)); do
    $PARAM_DIR/client -clientId "$cid" -c "$CONFIG_FILE" &
    client_pids+=($!)
  done

  for pid in "${client_pids[@]}"; do
    wait "$pid"
  done

  echo "[*] Waiting for experiment_result.txt..."
  while [ ! -f experiment_result.txt ]; do
    sleep 1
  done

  total_throughput=0
  total_latency=0
  count=0

  while read -r line; do
    th=$(echo "$line" | grep -oP 'throughput: \K[0-9.]+')
    lat=$(echo "$line" | grep -oP 'latency: \K[0-9.]+')

    if [[ -n "$th" && -n "$lat" ]]; then
      total_throughput=$(echo "$total_throughput + $th" | bc)
      total_latency=$(echo "$total_latency + $lat" | bc)
      count=$((count + 1))
    fi
  done < experiment_result.txt

  avg_latency=$(echo "scale=6; $total_latency / $count" | bc)

  echo "clients num: $i throughput: $total_throughput, avg latency: ${avg_latency}ms" >> "$RESULT_DIR/$Line.txt"
  echo "[✓] Appended aggregated result to $RESULT_DIR/$Line.txt"

  rm -f experiment_result.txt

  kill $PID1 $PID2 $PID3 2>/dev/null || true
  wait
  sleep 2
done
