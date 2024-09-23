open Syntax


module ModerAST = AST(Moder.ModingMetaData)
module TranslatorAST = AST(TranslatorMetadata.TranslationMetaData)

module HarmonyChecker = struct

  let check (x : ModerAST.t) : (ModerAST.t) = 
    let _ = x in
    assert false

end

