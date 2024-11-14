open Yojson.Basic.Util


module AST = Syntax.AST(TranslatorMetadata.TranslationMetaData)
module TCommon = TranslatorCommon.TranslatorCommon

module NameRemapper = struct

  let config : (string, string) Hashtbl.t = Hashtbl.create 100

  let build (config_path : string) = 
    let json = Yojson.Basic.from_file config_path in
    json
    |> to_assoc  
    |> List.iter (fun (key, value) ->
      Hashtbl.add config key (to_string value)
    )

  let is_tp_in_config (x : string) = 
    Hashtbl.mem config x

  let get_from_config (x : string) = 
    let v = Hashtbl.find config x in
    AST.Type.TpIdSeg {id = v; gen_inst = []}

  let is_id_basic_type (id : string) = 
    List.exists (fun x -> x = id)
    [
      "seq"; "map"; "set"; "int"; "bool"; "nat"
    ]

  let id_remap (x : string) = 
    if TCommon.starts_with x "Rsl" then
      TCommon.replace_prefix x "Rsl" "C"
    else if is_id_basic_type x then
      x
    else if not (TCommon.starts_with x "Leq") && x.[0] = 'L' then
      "C" ^ (String.sub x 1 (String.length x - 1))
    else
    "C" ^ x

  let module_id_remap (x : string) = 
    "Impl_" ^ x

end
