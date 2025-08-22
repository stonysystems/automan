#!/bin/bash
set -e

HOST="localhost"

# configure port here.
SERVER_BASE_PORT=4001    
SERVER_MON_BASE=5001  
CLIENT_BASE_PORT=4019 

RESULT_DIR="Figure12"
CODE_DIR="pgo"
Line="PGo-RaftKV"
PARAM_DIR="$CODE_DIR/raftkvs"
CONFIG_OUT_DIR="$PARAM_DIR/configs/generated"

mkdir -p "$RESULT_DIR"
mkdir -p "$CONFIG_OUT_DIR"

echo -n "" > "$RESULT_DIR/$Line.txt"

kill_port () {
  local port=$1
  local pids_tcp
  pids_tcp=$(lsof -ti tcp:"$port" || true)
  if [ -n "$pids_tcp" ]; then
    echo "[!] TCP port $port used by: $pids_tcp, killing..."
    kill -9 $pids_tcp || true
  fi
  local pids_udp
  pids_udp=$(lsof -ti udp:"$port" || true)
  if [ -n "$pids_udp" ]; then
    echo "[!] UDP port $port used by: $pids_udp, killing..."
    kill -9 $pids_udp || true
  fi
}

generate_config () {
  local nclients=$1
  local outfile="$CONFIG_OUT_DIR/test-3-$nclients.yaml"

  cat > "$outfile" <<EOF
numServers: 3
numClients: $nclients

debug: false
persist: false

clientRequestTimeout: 1500ms

fd:
  pullInterval: 200ms
  timeout: 100ms

mailboxes:
  receiveChanSize: 10000
  dialTimeout: 50ms
  readTimeout: 50ms
  writeTimeout: 50ms

leaderElection:
  timeout: 150ms
  timeoutOffset: 150ms

appendEntriesSendInterval: 1ms
sharedResourceTimeout: 1ms
inputChanReadTimeout: 1ms

servers:
  1:
    mailboxAddr: "${HOST}:$((SERVER_BASE_PORT + 0))"
    monitorAddr: "${HOST}:$((SERVER_MON_BASE  + 0))"
  2:
    mailboxAddr: "${HOST}:$((SERVER_BASE_PORT + 1))"
    monitorAddr: "${HOST}:$((SERVER_MON_BASE  + 1))"
  3:
    mailboxAddr: "${HOST}:$((SERVER_BASE_PORT + 2))"
    monitorAddr: "${HOST}:$((SERVER_MON_BASE  + 2))"

clients:
EOF

  for ((cid=1; cid<=nclients; cid++)); do
    echo "  $cid:" >> "$outfile"
    echo "    mailboxAddr: \"${HOST}:$((CLIENT_BASE_PORT + cid - 1))\"" >> "$outfile"
    echo "" >> "$outfile"
  done

  echo "$outfile"
}


for i in {1..7}; do
  echo "=============================="
  echo ">>> Running experiment with $i client(s)"
  echo "=============================="

  CONFIG_FILE=$(generate_config "$i")
  echo "[*] Generated config: $CONFIG_FILE"

  for p in \
    $((SERVER_BASE_PORT+0)) $((SERVER_BASE_PORT+1)) $((SERVER_BASE_PORT+2)) \
    $((SERVER_MON_BASE+0))  $((SERVER_MON_BASE+1))  $((SERVER_MON_BASE+2))
  do
    kill_port "$p"
  done
  for ((cid=1; cid<=i; cid++)); do
    kill_port $((CLIENT_BASE_PORT + cid - 1))
  done
  sleep 1

  "$PARAM_DIR/server" -srvId 1 -c "$CONFIG_FILE" &
  PID1=$!
  "$PARAM_DIR/server" -srvId 2 -c "$CONFIG_FILE" &
  PID2=$!
  "$PARAM_DIR/server" -srvId 3 -c "$CONFIG_FILE" &
  PID3=$!

  sleep 3

  client_pids=()
  for ((cid = 1; cid <= i; cid++)); do
    "$PARAM_DIR/client" -clientId "$cid" -c "$CONFIG_FILE" &
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
    th=$(echo "$line" | grep -oE 'throughput:[[:space:]]*[0-9]+(\.[0-9]+)?' | awk '{print $2}')
    lat=$(echo "$line" | grep -oE 'latency:[[:space:]]*[0-9]+(\.[0-9]+)?'    | awk '{print $2}')
    if [[ -n "$th" && -n "$lat" ]]; then
      total_throughput=$(echo "$total_throughput + $th" | bc)
      total_latency=$(echo "$total_latency + $lat" | bc)
      count=$((count + 1))
    fi
  done < experiment_result.txt

  if [[ "$count" -gt 0 ]]; then
    avg_latency=$(echo "scale=6; $total_latency / $count" | bc)
  else
    avg_latency="0"
  fi

  echo "clients num: $i throughput: $total_throughput, avg latency: ${avg_latency}ms" >> "$RESULT_DIR/$Line.txt"
  echo "[✓] Appended aggregated result to $RESULT_DIR/$Line.txt"

  rm -f experiment_result.txt

  kill $PID1 $PID2 $PID3 2>/dev/null || true
  wait $PID1 $PID2 $PID3 2>/dev/null || true
  sleep 2
done

echo "[✓] All done. See $RESULT_DIR/$Line.txt"
