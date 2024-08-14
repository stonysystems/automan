(* TRANSLATOR_TODO : It would be preferable to be able to read a config file. *)
class name_remapper = 
object (self)

  method is_id_kept_kw (id : string) = 
    List.exists (fun x -> x = id)
    [
      "seq"; "map"; "set"
    ]

  method id_remap (x : string) = 
    if self#is_id_kept_kw x then
      x
    else if x.[0] = 'L' then
      "C" ^ (String.sub x 1 (String.length x - 1))
    else
    "C" ^ x

  method module_id_remap (x : string) = 
    "Impl_" ^ x

end
