# AutoMan

AutoMan is a tool for generating distributed system implementations from Dafny protocol specifications.

# Building

``` shell
opam switch create ./ 4.13.1
eval $(opam env)
opam install dune menhir ppx_deriving
opam install . --deps-only
dune build
```

# Quick Run

We provide two sets of specifications, both adapted from 
[IronFleet](https://github.com/microsoft/Ironclad/tree/main/ironfleet):
1. Multi-Paxos (rsl), available at  `./asset/spec/RSL`.
2. Key-Value Store (kv), available at `./asset/spec/KV`.

The necessary annotations (explained below) are available at `./asset/annotations`.

Run `bash run.sh [rsl | kv]` to apply the translation.

The generated codes can be found in `./asset/impl`.

