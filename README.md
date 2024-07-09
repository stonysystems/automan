# Building

``` shell
opam switch create ./ 4.13.1
eval $(opam env)
opam install dune menhir ppx_deriving
opam install . --deps-only
dune build
```
