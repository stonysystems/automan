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


RESULT_DIR="Figure9"
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

rm -f throughput_log.txt

sed -i -E "s/(int[[:space:]]+port1[[:space:]]*=[[:space:]]*)[0-9]+;/\1$PORT1;/" "$CLIENT"
sed -i -E "s/(int[[:space:]]+port2[[:space:]]*=[[:space:]]*)[0-9]+;/\1$PORT2;/" "$CLIENT"
sed -i -E "s/(int[[:space:]]+port3[[:space:]]*=[[:space:]]*)[0-9]+;/\1$PORT3;/" "$CLIENT"
sed -i -E "s/(int[[:space:]]+client_port[[:space:]]*=[[:space:]]*)[0-9]+;/\1$CPORT;/" "$PARAM_FILE"

batch_size=16

sed -i -E 's/^[[:space:]]*\/\/[[:space:]]*print[[:space:]]*"I am leader\\n";/  print "I am leader\\n";/' "$PROPOSER"
sed -i -E 's/^([[:space:]]*)[0-9]+([[:space:]]*),([[:space:]]*\/\/ baseline view timeout period.*)$/\160\2,\3/' "$PARAM_FILE"
sed -i -E "s/([ ]*)[0-9]+([ ]*),[ ]*\/\/ max_batch_size/\1$batch_size\2, \/\/ max_batch_size/" "$PARAM_FILE"

rm -f $CODE_DIR/ironfleet/build_success.flag experiment_result.txt

python3 $CODE_DIR/compile.py

if [ ! -f $CODE_DIR/ironfleet/build_success.flag ]; then
  echo "✗ Build failed for batch_size = $batch_size"
  continue
fi

# dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll $IP1 4001 $IP2 4002 $IP3 4003 $IP1 4001 > server1.log 2>&1 &
# PID1=$!
# dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll $IP1 4001 $IP2 4002 $IP3 4003 $IP2 4002 > server2.log 2>&1 &
# PID2=$!
# dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll $IP1 4001 $IP2 4002 $IP3 4003 $IP3 4003 > server3.log 2>&1 &
# PID3=$!

dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll $IP1 $PORT1 $IP2 $PORT2 $IP3 $PORT3 $IP1 $PORT1 > server1.log 2>&1 &
PID1=$!
dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll $IP1 $PORT1 $IP2 $PORT2 $IP3 $PORT3 $IP2 $PORT2 > server2.log 2>&1 &
PID2=$!
dotnet $CODE_DIR/ironfleet/src/Dafny/Distributed/Services/RSL/build/IronfleetShell.dll $IP1 $PORT1 $IP2 $PORT2 $IP3 $PORT3 $IP3 $PORT3 > server3.log 2>&1 &
PID3=$!

sleep 3

dotnet $CODE_DIR/ironfleet/src/IronRSLClient/bin/Release/net6.0/IronRSLClient.dll nthreads=$batch_size duration=30 clientport=$CPORT initialseqno=0 &

CLIENT_PID=$!

sleep 15

LEADER_PID=""
if grep -q "I am leader" server1.log; then
  LEADER_PID=$PID1
  echo "[*] Detected leader: server1 (port 4001)"
elif grep -q "I am leader" server2.log; then
  LEADER_PID=$PID2
  echo "[*] Detected leader: server2 (port 4002)"
elif grep -q "I am leader" server3.log; then
  LEADER_PID=$PID3
  echo "[*] Detected leader: server3 (port 4003)"
else
  echo "[!] No leader detected."
fi

# Kill leader process
if [ -n "$LEADER_PID" ]; then
  kill "$LEADER_PID" 2>/dev/null || true
  echo "[✗] Killed leader process PID=$LEADER_PID"
fi

wait $CLIENT_PID

echo "[*] Waiting for throughput_log.txt..."
while [ ! -f throughput_log.txt ]; do
  sleep 1
done

cat throughput_log.txt >> "$RESULT_DIR/$Line.txt"
echo "[✓] Appended all results to $RESULT_DIR/$Line.txt"

rm -f throughput_log.txt
rm -f experiment_result.txt

for pid in $PID1 $PID2 $PID3; do
  if [ "$pid" != "$LEADER_PID" ]; then
    kill "$pid" 2>/dev/null || true
    wait "$pid" 2>/dev/null || true
  fi
done

rm -f server1.log server2.log server3.log

sleep 2


