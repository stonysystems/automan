open Syntax
open Internal
open Annotator

module Definitions = struct
  type predicate_decl_t =
    { vars_in:  AnnotationPass.TopDecl.formal_t list
    ; vars_out: AnnotationPass.TopDecl.formal_t list
    ; make_stub: bool }
  [@@deriving show, eq]

  type ite_t =
    { vars_then: Syntax.Common.member_qualified_name_t list
    ; vars_else: Syntax.Common.member_qualified_name_t list }
  [@@deriving show, eq]

  type match_t = (Syntax.Common.member_qualified_name_t list) list
  [@@deriving show, eq]

  type quantification_t = Syntax.Common.member_qualified_name_t list
  [@@deriving show, eq]

  type binary_op_t = Syntax.Common.member_qualified_name_t list
  [@@deriving show, eq]

  type arglist_t =
    { exprs_in:  ParserPass.Prog.expr_t list
    ; exprs_out: Syntax.Common.member_qualified_name_t list
    }
  [@@deriving show, eq]
end

module ModingMetaData : MetaData
  with type predicate_decl_t    = Definitions.predicate_decl_t
  with type datatype_decl_t     = AnnotationMetaData.datatype_decl_t
  with type synonym_type_decl_t = AnnotationMetaData.synonym_type_decl_t

  with type type_t = AnnotationMetaData.type_t

  with type ite_t = Definitions.ite_t
  with type match_t = Definitions.match_t
  with type quantification_t = Definitions.quantification_t
  with type binary_op_t = Definitions.binary_op_t

  with type arglist_t = Definitions.arglist_t
= struct
  type predicate_decl_t = Definitions.predicate_decl_t
  [@@deriving show, eq]
  type datatype_decl_t  = AnnotationMetaData.datatype_decl_t
  [@@deriving show, eq]
  type synonym_type_decl_t = AnnotationMetaData.synonym_type_decl_t
  [@@deriving show, eq]

  type type_t = AnnotationMetaData.type_t
  [@@deriving show, eq]

  type ite_t = Definitions.ite_t
  [@@deriving show, eq]
  type match_t = Definitions.match_t
  [@@deriving show, eq]
  type quantification_t = Definitions.quantification_t
  [@@deriving show, eq]
  type binary_op_t = Definitions.binary_op_t
  [@@deriving show, eq]

  type arglist_t = Definitions.arglist_t
  [@@deriving show, eq]
end

module ModePass = AST (ModingMetaData)

type 'a m = (('a * bool), string) Result.t

open struct
  let return (x: 'a): 'a m =
    Result.Ok (x, false)

  let ( let* ) (x: 'a m) (f: 'a -> 'b m): 'b m =
    let ( let*! ) = Result.bind in
    let*! (x', b1) = x in
    let*! (y, b2)  = f x' in
    Result.Ok (y, b1 || b2)

  let make_stub (): unit m =
    Result.Ok ((), true)
end

module Util = struct
  type partition_args_by_modes_t =
    | PositionalPartition of
        { args_in:  AnnotationPass.Prog.expr_t list
        ; args_out: AnnotationPass.Prog.expr_t list }
    | Unknown

  (** The additional `bool` return is for whether named args are used. These are
      not supported, so their presence means we should generate a stub.
  *)
  let partition_args_by_modes
      (args: AnnotationPass.Prog.arglist_t) (anns: Annotation.mode_t list option)
    : partition_args_by_modes_t * bool =
    let named_args_p = List.length args.named <> 0 in
    (* NOTE: The annotation pass assures us that the mode list has the same
       length as the argument list *)
    let ( let< ) = Option.bind in
    let res = begin
      let< anns = anns in
      let anns' = begin
        if not named_args_p then anns
        else List.(take (length args.positional) anns)
      end in
      let args_with_anns =
        List.map2 (fun arg mode -> (arg, mode)) args.positional anns' in
      let (in_args, out_args) =
        List.partition_map
          (function (arg, mode) ->
             if mode = Annotation.Input
             then Either.left arg
             else Either.right arg)
          args_with_anns
      in
      Option.Some
        (PositionalPartition
           {args_in = in_args; args_out = out_args})
    end in
    ( Option.fold ~none:Unknown ~some:(fun x -> x) res
    , named_args_p)
end

let mode_expr_conjunct_funcall
    (vars_in:  AnnotationPass.TopDecl.formal_t list)
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (args: AnnotationPass.TopDecl.arglist_t)
    (ann: AnnotationMetaData.arglist_t)
  : ModePass.Prog.expr_t m =
  let (pos_args_in, pos_args_out, named_args_p) = begin
    let (part, named) = begin
      Util.partition_args_by_modes args
        (Option.map (function (_, modes) -> modes) ann)
    end in
    let (pos_args_in, pos_args_out) = begin
      match part with
      | PositionalPartition {args_in = args_in; args_out = args_out} ->
        (args_in, args_out)
      | Unknown ->
        (* NOTE: calls without annotations are assumed to be all input-moded *)
        (args.positional, [])
    end in
    (pos_args_in, pos_args_out, named)
  end in
  (* TODO:
     1. check input arguments don't contain output variables

        NOTE: identifiers not declared in the formal parameter list are assumed
        to be input-moded (local variables, constructors)

     2. check output arguments are member-qualified output variables, and
        possibly including length

     3. if there are any named arguments, indicate that a stub should be generated *)
  let* _ =
    if named_args_p then make_stub ()
    else return ()
  in
  foo1

let mode_expr_conjunct
    (vars_in:  AnnotationPass.TopDecl.formal_t list)
    (vars_out: AnnotationPass.TopDecl.formal_t list)
    (e: AnnotationPass.Prog.expr_t)
  : ModePass.Prog.expr_t m =
  match e with
  | Suffixed (e_callee, suff) -> begin
      match suff with
      | ArgList (args, anns) ->
        let (pos_args_in, pos_args_out, named_args_p) = begin
          let (part, named) =
            Util.partition_args_by_modes args
              (Option.map (function (_, modes) -> modes) anns)
          in
          let (pos_args_in, pos_args_out) = begin
            match part with
            | PositionalPartition {args_in = args_in; args_out = args_out} ->
              (args_in, args_out)
            | Unknown ->
              (* NOTE: calls without annotations are assumed to be all input-moded *)
              (args.positional, [])
          end in
          (pos_args_in, pos_args_out, named)
        end in
        foo1
      | _ -> foo01
    end
  | _ -> foo1
