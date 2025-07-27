#!/bin/bash
PORT1=5101
PORT2=5102
PORT3=5103
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

RESULT_DIR="Figure11"
CODE_DIR="IronKV"
Line="IronKV"
IP1=127.0.0.1
IP2=127.0.0.1
IP3=127.0.0.1
PARAM_FILE="$CODE_DIR/ironfleet/src/IronKVClient/Program.cs"

mkdir -p "$RESULT_DIR/$Line"

sed -i -E "s/(int[[:space:]]+port1[[:space:]]*=[[:space:]]*)[0-9]+;/\1$PORT1;/" "$PARAM_FILE"
sed -i -E "s/(int[[:space:]]+port2[[:space:]]*=[[:space:]]*)[0-9]+;/\1$PORT2;/" "$PARAM_FILE"
sed -i -E "s/(int[[:space:]]+port3[[:space:]]*=[[:space:]]*)[0-9]+;/\1$PORT3;/" "$PARAM_FILE"
sed -i -E "s/(int[[:space:]]+client_port[[:space:]]*=[[:space:]]*)[0-9]+;/\1$CPORT;/" "$PARAM_FILE"

workloads=("g" "s")
valuesizes=(128 1024 8192)
nthreads_list=(1 4 16 32)

rm -f $CODE_DIR/ironfleet/build_success.flag experiment_result.txt

python3 $CODE_DIR/compile.py

if [ ! -f $CODE_DIR/ironfleet/build_success.flag ]; then
  echo "✗ Build failed for kv"
  continue
fi

for workload in "${workloads[@]}"; do
  for valuesize in "${valuesizes[@]}"; do
    output_file="$RESULT_DIR/$Line/${workload}et-${valuesize}.txt"
    echo -n "" > "$output_file"

    for nthreads in "${nthreads_list[@]}"; do
      echo "========================================="
      echo ">>> Running workload=$workload, valuesize=$valuesize, nthreads=$nthreads"
      echo "========================================="

      # dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/SHT/build/IronfleetShell.dll $IP1 5001 $IP2 5002 $IP3 5003 $IP1 5001 &
      # PID1=$!
      # dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/SHT/build/IronfleetShell.dll $IP1 5001 $IP2 5002 $IP3 5003 $IP2 5002 &
      # PID2=$!
      # dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/SHT/build/IronfleetShell.dll $IP1 5001 $IP2 5002 $IP3 5003 $IP3 5003 &
      # PID3=$!


      # sleep 3

      # dotnet $CODE_DIR/ironfleet/src/IronKVClient/bin/Release/net6.0/IronKVClient.dll duration=30 workload=$workload numkeys=10000 clientport=7000 valuesize=$valuesize nthreads=$nthreads

      dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/SHT/build/IronfleetShell.dll $IP1 $PORT1 $IP2 $PORT2 $IP3 $PORT3 $IP1 $PORT1 &
      PID1=$!
      dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/SHT/build/IronfleetShell.dll $IP1 $PORT1 $IP2 $PORT2 $IP3 $PORT3 $IP2 $PORT2 &
      PID2=$!
      dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/SHT/build/IronfleetShell.dll $IP1 $PORT1 $IP2 $PORT2 $IP3 $PORT3 $IP3 $PORT3 &
      PID3=$!



      sleep 3

      dotnet $CODE_DIR/ironfleet/src/IronKVClient/bin/Release/net6.0/IronKVClient.dll duration=60 workload=$workload numkeys=10000 clientport=$CPORT valuesize=$valuesize nthreads=$nthreads
      
      echo "[*] Waiting for experiment_result.txt..."
      while [ ! -f experiment_result.txt ]; do
        sleep 1
      done

      last_line=$(tail -n 1 experiment_result.txt)
      echo "nthreads=$nthreads $last_line" >> "$output_file"
      echo "[✓] Appended to $output_file"

      rm -f experiment_result.txt
      kill $PID1 $PID2 $PID3 2>/dev/null || true
      sleep 2
    done
  done
done
