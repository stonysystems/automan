(lang dune 3.14)
(using menhir 3.0)

(name ballast)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Christa Jenkins" "Ti Zhou" "Omar Chowdhurry")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name ballast)
 (synopsis "Tool for generating IronFleet system implementations from protocol specifications.")
 ;; (description "A longer description")
 (depends ocaml dune core core_unix async_unix)
 (tags
  ("distributed systems" "formal verification")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
