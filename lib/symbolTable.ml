(*

Doc for Symbol Table in AutoMan. Authored by Ti Zhou.

-------------------------------------------------------------------------------

Ref : https://dafny.org/dafny/DafnyRef/DafnyRef.html#sec-importing-modules

Assume Dafny has an algorithm A for building its symbol table T.
We implement an algorithm A' for building a symbol table T', 
which is a subset of T. That is, 
the symbol table might lose track of some symbols defined in the language, 
but it will not include incorrect symbols.

We can improve A' step by step until T' = T.

-------------------------------------------------------------------------------

type symbol_object_t = 
  | DataTypeDeclSgl of Syntax.datatype_t
  | DataTypeDeclMul of Syntax.datatype_t 
  | Alias           of Synatx.synonym_type_t

For input file F:
  
  Global Table T1:

  Create a table T1 with 
    For each files included in F, apply:
      For each module:
        Create the key K = Module Name (String)
        Filter a list of symbol_object_t L from this module 
        Add (K, L) to T1; Abort if T1 already has a key = K

  T1 should only be initialized once and doesn't need to support for COPY.

  Syntax.TopDecl.t list ->
    t -> t' -> [ Import | ModuleDef | DataTypeDecl | Alias ]
    ModuleDef -> t list
  A layer is a t list

  For ** import ** :
    ``` 
      import A
      import opened B
      import A = B
      import A : B
      import A.B
      import A`E
      import X = A.B`{E,F}
    ```   
    Only 
      `import opened B` and 
      `import A.B`
    are supported at this version
    
  Create a empty list of symbol_object_t, T2 with 
    For each layer in the AST of F:
      T2' = T2.copy()

      for each module imported: T2' = T2' + F[module]
      for each symbol_object_t introduced:
        T2' = T2' + [symbol_object_t]

      Apply translation to this layer with T2'
      Enter next layer

*)
