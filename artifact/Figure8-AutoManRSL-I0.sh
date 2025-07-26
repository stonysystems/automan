#!/bin/bash

PORT1=4101
PORT2=4102
PORT3=4103
CPORT=7000

for port in $PORT1 $PORT2 $PORT3 $CPORT; do
  pid=$(lsof -ti udp:$port)
  if [ -n "$pid" ]; then
    echo "[!] UDP port $port is in use by PID(s): $pid, killing..."
    kill -9 $pid || true
    sleep 1
  fi
done


set -e


RESULT_DIR="Figure8"
CODE_DIR="RSL-I0"
Line="AutoManRSL-I0"
PARAM_FILE="$CODE_DIR/ironfleet/src/Dafny/Distributed/Impl/RSL/CParameters.i.dfy"
PROPOSER="$CODE_DIR/ironfleet/src/Dafny/Distributed/Impl/RSL/ProposerImpl.i.dfy"
CLIENT="$CODE_DIR/ironfleet/src/IronRSLClient/Program.cs"
IP1=127.0.0.1
IP2=127.0.0.1
IP3=127.0.0.1
mkdir -p $RESULT_DIR

echo -n "" > "$RESULT_DIR/$Line.txt"

sed -i -E "s/(int[[:space:]]+port1[[:space:]]*=[[:space:]]*)[0-9]+;/\1$PORT1;/" "$CLIENT"
sed -i -E "s/(int[[:space:]]+port2[[:space:]]*=[[:space:]]*)[0-9]+;/\1$PORT2;/" "$CLIENT"
sed -i -E "s/(int[[:space:]]+port3[[:space:]]*=[[:space:]]*)[0-9]+;/\1$PORT3;/" "$CLIENT"

rm -f throughput_log.txt

sed -i -E '/^[[:space:]]*print[[:space:]]*"I am leader\\n";/ s/^[[:space:]]*/  \/\/ /' "$PROPOSER"
sed -i -E 's/^([[:space:]]*)[0-9]+([[:space:]]*),([[:space:]]*\/\/ baseline view timeout period.*)$/\1100\2,\3/' "$PARAM_FILE"

for i in {0..7}; do
  batch_size=$((2 ** i))
  echo "=============================="
  echo ">>> Running experiment with max_batch_size = $batch_size"
  echo "=============================="

  sed -i -E "s/([ ]*)[0-9]+([ ]*),[ ]*\/\/ max_batch_size/\1$batch_size\2, \/\/ max_batch_size/" "$PARAM_FILE"

  rm -f $CODE_DIR/ironfleet/build_success.flag experiment_result.txt

  python3 $CODE_DIR/compile.py

  if [ ! -f $CODE_DIR/ironfleet/build_success.flag ]; then
    echo "✗ Build failed for batch_size = $batch_size"
    continue
  fi

  # dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll $IP1 4001 $IP2 4002 $IP3 4003 $IP1 4001 &
  # PID1=$!
  # dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll $IP1 4001 $IP2 4002 $IP3 4003 $IP2 4002 &
  # PID2=$!
  # dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll $IP1 4001 $IP2 4002 $IP3 4003 $IP3 4003 &
  # PID3=$!

  # sleep 3

  # dotnet $CODE_DIR/ironfleet/src/IronRSLClient/bin/Release/net6.0/IronRSLClient.dll nthreads=$batch_size duration=60 clientport=7000 initialseqno=0

  dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll $IP1 $PORT1 $IP2 $PORT2 $IP3 $PORT3 $IP1 $PORT1 &
  PID1=$!
  dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll $IP1 $PORT1 $IP2 $PORT2 $IP3 $PORT3 $IP2 $PORT2 &
  PID2=$!
  dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll $IP1 $PORT1 $IP2 $PORT2 $IP3 $PORT3 $IP3 $PORT3 &
  PID3=$!

  sleep 3

  dotnet $CODE_DIR/ironfleet/src/IronRSLClient/bin/Release/net6.0/IronRSLClient.dll nthreads=$batch_size duration=60 clientport=$CPORT initialseqno=0

  echo "[*] Waiting for experiment_result.txt..."
  while [ ! -f experiment_result.txt ]; do
    sleep 1
  done

  last_line=$(tail -n 1 experiment_result.txt)
  echo "clients num: $batch_size $last_line" >> "$RESULT_DIR/$Line.txt"
  echo "[✓] Appended result to $RESULT_DIR/$Line.txt"

  rm -f experiment_result.txt

  kill $PID1 $PID2 $PID3 2>/dev/null || true
  wait $PID1 $PID2 $PID3 2>/dev/null || true
  sleep 2
done
