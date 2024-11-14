module Logger = struct 

  type t = string list
  let init : t = []

  let add_msg (x : t) (txt : string) : t = 
    x @ [txt]

  let sub s = 
    let len = 55 in
    if String.length s >= len then (String.sub s 0 len)  ^ " ... ... "
    else s

  let enter_module (x : t) (mod_name : string) : t =
    add_msg
      x
      (Printf.sprintf "[Module] %s\n" mod_name)

  let enter_action (x : t) (pred_name : string) : t = 
    add_msg 
      x 
      (Printf.sprintf "[Action] %s" pred_name)

  let error_then_else_not_assigning_same_set_of_vars
    (x : t) (expr_str : string) : t =
    add_msg
      x 
      (Printf.sprintf 
        "Then-branch and else-branch do not assign the same set of variables: \n\t%s\n"
        (sub expr_str))

  let error_lft_expr_not_output (x : t) (expr_str : string) : t = 
    add_msg
      x 
      (Printf.sprintf 
        "This expr on the left side of an equivalence is not an output-mode variable: %s\n"
        expr_str)

  let error_output_used_but_not_assigned
    (x : t) (expr_str : string) : t =
    add_msg 
      x 
      (Printf.sprintf
        "This expr contains an output-mode variable that is \n\tnot assigned in the previous context:\n\t%s\n"
        (sub expr_str))
    
  let error_saturation_check_failed
    (x : t) : t = 
    add_msg 
      x 
      "Saturation check failed: Output-mode variables are not fully assigned\n"

  let error_harmony_check_failed
    (x : t) (expr_str : string) : t = 
    add_msg 
      x 
      (Printf.sprintf
        "Harmony check failed: \n\tThis output-mode variable has been assigned multiple times: \n\t\t%s\n"
        expr_str)

  let error_none
    (x : t) : t = 
    add_msg x "Check passed\n"

  let print (x : t) : string = 
    "/**********************************************************************" ^ "\n" ^
    "AUTOMAN LOG" ^ "\n\n" ^
    (String.concat "\n" x) ^ 
    "**********************************************************************/" ^ "\n\n"

end
