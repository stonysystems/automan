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
  | DataTypeDeclMul of Syntax.datatype_t -> unknown
  | Alias           of Synatx.synonym_type_t

For input file F:
  
  ** Symbol Table T  **
    
    Data Member:
      T.DefTable : symbol_object_t list ;
        Contains definitions that can be directly accessed, come from:
          1. Definitions imported from "include" 
            /* The definitions outside of any modules (ignore) */
          2. Import module with keyword "opened"
            /* Import opened M; The definitions in M can be accessed */
            /* The definitions in M.M2 cannot be accessed (assume it cannot) */
          3. The definitions from the current file.
            /* Added during translation */

      T.ModTable : A key-value table with KEY = module name : string and
                    VALUE = T : Symbol Table for this module name

      T.OpenedTable : 
        A list of string indicates imported modules inside T.ModTable

      T.AliasTable :
        Used to handle alias for modules such as 
          1. import A = B
          2. import A : B
          3. import A`E
          4. import X = A.B`{E,F}
        We don't implement this at this moment (not used anyway).

    API:
      T.Build (F : string) -> None

      T.AddModule (key = name : String, value = table : T) -> None

      T.AddDef (def : TopDecl.t) -> None 

      T.Exist (string list) -> 
        bool, indicates whether this module exists in this table
        /* Example for input : M1.M2.D | D */ 

      T.Query (x : string list) -> symbol_object_t
      /* assert T.Exist (x); */

      T.Copy () -> T; Return a copy of its self

  ** Algorithms **
    Helpers:
      ** Path Checker ** :
        INPUT : A string get from "Include"
        OUTPUT : 
          A string indicates the dafny file to parse in.
          Empty if not found.
        
        Check whether there's a file in the same directory.
        Other directory such as "../x" or "x/.." will lead to empty.

      T.Build (F : string) : 
        For each file IncludedF included in F, apply:
          ```
          Note that here for T
            1. We ignore the modifiers for module, such as ABSTRACT.

          These issues will lead T' to be a sub-set of T, 
            but we can ** easily ** improve it later, as the arch allows it.
          ```

          IncludedT = new T and T.build IncludedF;
          For each module (name, table) in IncludedT.ModTable:
            self.AddMod (name, table)
          /* We don't add IncludedT.DefTable */

          For each defnitions d, self.AddDef (d);

-------------------------------------------------------------------------------

  The syntax indicates that 
    [ Import | ModuleDef | DataTypeDecl | Alias ] shares a same layer.
  ModuleDef can lead to a deeper layer.

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

*)

module SymbolTable = struct
  
  class symbol_table = 
  object 
    method build (file_path : string) : unit = 
      let _ = file_path in
      ()
    
    method query (name : string) : string list = 
      assert (name = "LAcceptor");
      [
        "constants" ; 
        "max_bal"   ;
        "votes"     ;
        "last_checkpointed_operation" ;
        "log_truncation_point" ;
      ]
  end

end
