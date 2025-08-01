eval $(opam env)

rsl_files=(
  Acceptor.i.dfy 
  Configuration.i.dfy
  Parameters.i.dfy
  Constants.i.dfy
  Types.i.dfy
  Message.i.dfy
  Election.i.dfy
  Learner.i.dfy 
  Proposer.i.dfy
  StateMachine.i.dfy
  Executor.i.dfy
  Replica.i.dfy
)

kv_files=(
  Message.i.dfy
  SingleMessage.i.dfy
  Network.i.dfy
  Parameters.i.dfy
  Configuration.i.dfy
  Delegations.i.dfy
  SingleDelivery.i.dfy
  Host.i.dfy
)

byz_rsl_files=(
  Acceptor.i.dfy
  CheckValSafety.i.dfy
  Configuration.i.dfy
  Constants.i.dfy
  Election.i.dfy
  Executor.i.dfy
  Learner.i.dfy
  Message.i.dfy
  Parameters.i.dfy
  Proposer.i.dfy
  Replica.i.dfy
  StateMachine.i.dfy
  Types.i.dfy
)

Ng_examples_files=(
  Acceptor.i.dfy 
)

Add_examples_files=(
  Acceptor.i.dfy 
)

if [ $# -eq 0 ]; then
  echo "Usage: $0 <param>"
  exit 1
fi

if [ "$1" == "rsl" ]; then
  for file in "${rsl_files[@]}"
  do
    echo "[+] RSL/spec -> RSL/impl | "$file
    dune exe bin/main.exe ./asset/spec/RSL/$file asset/annotations/RSL.automan asset/remapping.json > \
      ./asset/impl/RSL/$file
  done
elif [ "$1" == "kv" ]; then
  for file in "${kv_files[@]}"
  do
    echo "[+] KV/spec -> KV/impl | "$file
    dune exe bin/main.exe ./asset/spec/KV/$file asset/annotations/SHT.automan asset/remapping.json > \
      ./asset/impl/KV/$file
  done
elif [ "$1" == "byz" ]; then
  for file in "${byz_rsl_files[@]}"
  do
    echo "[+] ByzRSL/spec -> ByzRSL/impl | "$file
    dune exe bin/main.exe ./asset/spec/ByzRSL/$file asset/annotations/ByzRSL.automan asset/remapping.json > \
      ./asset/impl/ByzRSL/$file
  done
elif [ "$1" == "ng" ]; then
  for file in "${Ng_examples_files[@]}"
  do
    echo "[+] NgExamples/spec -> NgExamples/impl | "$file
    dune exe bin/main.exe ./asset/spec/NgExamples/$file asset/annotations/RSL.automan asset/remapping.json > \
      ./asset/impl/NgExamples/$file
  done
elif [ "$1" == "add" ]; then
  for file in "${Add_examples_files[@]}"
  do
    echo "[+] AddExamples/spec -> AddExamples/impl | "$file
    dune exe bin/main.exe ./asset/spec/AddExamples/$file asset/annotations/RSL.automan asset/remapping.json > \
      ./asset/impl/AddExamples/$file
  done
else
  echo "Usage: $0 [rsl | kv | ng | add]"
fi

