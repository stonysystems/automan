module AST = Syntax.AST(TranslatorMetadata.TranslationMetaData)
module TCommon = TranslatorCommon.TranslatorCommon


class name_remapper = 
object (self)

  val config = [
    ("seq<RslPacket>", (AST.Type.TpIdSeg {id = "OutboundPackets"; gen_inst = []}));
    ("NodeIdentity", (AST.Type.TpIdSeg {id = "EndPoint"; gen_inst = []}));
    ("KeyPlus", (AST.Type.TpIdSeg {id = "KeyPlus"; gen_inst = []}));
    ("KeyRange", (AST.Type.TpIdSeg {id = "KeyRange"; gen_inst = []}));
    ("KeyPlusLt", (AST.Type.TpIdSeg {id = "KeyPlusLt"; gen_inst = []}));
    ("KeyPlusLe", (AST.Type.TpIdSeg {id = "KeyPlusLe"; gen_inst = []}));
    ("Key", (AST.Type.TpIdSeg {id = "Key"; gen_inst = []}));
    ("Hashtable", (AST.Type.TpIdSeg {id = "Hashtable"; gen_inst = []}));
  ]

  method is_tp_in_config (x : string) = 
    let rec aux lst = 
      match lst with 
      | [] -> false
      | h :: rest -> let k, _ = h in (k = x) || (aux rest) 
    in
    aux config

  method get_from_config (x : string) = 
    let rec aux lst = 
      match lst with 
      | [] -> assert false
      | h :: rest -> let k, v = h in
        match k = x with 
        | true -> v
        | false -> aux rest
    in
    aux config

  method is_id_basic_type (id : string) = 
    List.exists (fun x -> x = id)
    [
      "seq"; "map"; "set"; "int"; "bool"; "nat"
    ]

  method id_remap (x : string) = 
    if TCommon.starts_with x "Rsl" then
      TCommon.replace_prefix x "Rsl" "C"
    else if self#is_id_basic_type x then
      x
    else if not (TCommon.starts_with x "Leq") && x.[0] = 'L' then
      "C" ^ (String.sub x 1 (String.length x - 1))
    else
    "C" ^ x

  method module_id_remap (x : string) = 
    "Impl_" ^ x

end
