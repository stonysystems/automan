#!/bin/bash
set -e

RESULT_DIR="Figure12"
CODE_DIR="PaxosKV-I1"
Line="AutoMan-PaxosKV-I1"
PARAM_FILE="$CODE_DIR/ironfleet/src/Dafny/Distributed/Impl/RSL/CParameters.i.dfy"
CERT_DIR="$CODE_DIR/certs"
IP1=127.0.0.1
IP2=127.0.0.1
IP3=127.0.0.1
PORT1=4001
PORT2=4002
PORT3=4003
CPORT=7000

mkdir -p "$RESULT_DIR"
mkdir -p "$CERT_DIR"

echo -n "" > "$RESULT_DIR/$Line.txt"

for i in {1..7}; do
  batch_size=$i
  echo "=============================="
  echo ">>> Running experiment with max_batch_size = $batch_size"
  echo "=============================="

  # Update the batch size parameter
  # sed -i -E "s/([ ]*)[0-9]+([ ]*),[ ]*\/\/ max_batch_size/\1$batch_size\2, \/\/ max_batch_size/" "$PARAM_FILE"

  rm -f $CODE_DIR/ironfleet/build_success.flag experiment_result.txt

  # Recompile the system
  python3 $CODE_DIR/compile.py

  if [ ! -f $CODE_DIR/ironfleet/build_success.flag ]; then
    echo "✗ Build failed for batch_size = $batch_size"
    continue
  fi

  # Generate new certs
  # dotnet $CODE_DIR/ironfleet/bin/CreateIronServiceCerts.dll outputdir=$CERT_DIR name=MyKV type=IronRSLKV addr1=$IP1 port1=4001 addr2=$IP2 port2=4002 addr3=$IP3 port3=4003

  dotnet $CODE_DIR/ironfleet/bin/CreateIronServiceCerts.dll outputdir=$CERT_DIR name=MyKV type=IronRSLKV addr1=$IP1 port1=$PORT1 addr2=$IP2 port2=$PORT2 addr3=$IP3 port3=$PORT3



  # Start replicas
  dotnet $CODE_DIR/ironfleet/bin/IronRSLKVServer.dll $CERT_DIR/MyKV.IronRSLKV.service.txt $CERT_DIR/MyKV.IronRSLKV.server1.private.txt &
  PID1=$!
  dotnet $CODE_DIR/ironfleet/bin/IronRSLKVServer.dll $CERT_DIR/MyKV.IronRSLKV.service.txt $CERT_DIR/MyKV.IronRSLKV.server2.private.txt &
  PID2=$!
  dotnet $CODE_DIR/ironfleet/bin/IronRSLKVServer.dll $CERT_DIR/MyKV.IronRSLKV.service.txt $CERT_DIR/MyKV.IronRSLKV.server3.private.txt &
  PID3=$!

  sleep 3

  # Start client
  dotnet $CODE_DIR/ironfleet/bin/IronRSLKVClient.dll $CERT_DIR/MyKV.IronRSLKV.service.txt nthreads=$batch_size duration=60 setfraction=0.05 deletefraction=0 print=true

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
