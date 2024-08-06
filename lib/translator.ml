open Syntax


module Translator (M : MetaData) = struct 
  module AST = AST(M)


  let translate_includes _ = 
    [""]

  let translate (x : AST.t) = 
    let Dafny { includes = includes; decls = decls } =  x in
    let includes' = translate_includes includes in
    AST.Dafny { includes = includes'; decls = decls }
      
end

