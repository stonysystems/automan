(lang dune 3.14)
(using menhir 3.0)

(name automan)

(generate_opam_files true)

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name automan)
 (synopsis "Tool for generating distributed system implementations from Dafny protocol specifications.")
 (depends ocaml dune core core_unix async_unix)
 (tags
  ("distributed systems" "formal verification")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
