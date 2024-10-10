# eval $(opam env)

rsl_files=(
  Acceptor.i.dfy 
  # Configuration.i.dfy
  # Parameters.i.dfy
  # Constants.i.dfy
  # Types.i.dfy
  # Message.i.dfy
  # Election.i.dfy
  # Learner.i.dfy 
  Proposer.i.dfy
  # StateMachine.i.dfy
  # Executor.i.dfy
  # Replica.i.dfy
)

kv_files=(
  # Message.i.dfy
  # SingleMessage.i.dfy
  # Network.i.dfy
  # Parameters.i.dfy
  # Configuration.i.dfy
  # Delegations.i.dfy
  # SingleDelivery.i.dfy
  # Host.i.dfy
)

if [ $# -eq 0 ]; then
  echo "Usage: $0 <param>"
  exit 1
fi

if [ "$1" == "rsl" ]; then
  for file in "${rsl_files[@]}"
  do
    echo "[+] rsl/spec -> rsl/impl | "$file
    dune exe ./_build/default/test/test_automan.exe ./asset/tmp/spec/rsl/$file asset/tmp/annotations/RSL.automan  > \
      ./asset/tmp/impl/rsl/$file
  done
elif [ "$1" == "kv" ]; then
  for file in "${kv_files[@]}"
  do
    echo "[+] kv/spec -> kv/impl | "$file
    dune exe test/test_automan.exe ./asset/tmp/spec/kv/$file > \
      ./asset/tmp/impl/kv/$file
  done
else
  echo "Usage: $0 [rsl | kv]"
fi

# dune exe test/test_annotator.exe asset/tmp/Acceptor.i.dfy asset/tmp/annotations/RSL.automan > ./tmp.ast
