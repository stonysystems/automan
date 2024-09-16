open Automan
(* open Core *)
open Internal
(* open Lexing *)
(* open TestCommon *)

module AST = Syntax.AST (TranslatorMetadata.TranslationMetaData)

(* NOTE: the prefix "_" was added to suppress warnings for unused variables *)
let _rsl_acceptor_lacceptorproccess2a_body: AST.Prog.expr_t =
  (* Local name for a long (qualified) expression  *)
  let s_constants_all_config_replica_ids: AST.Prog.expr_t =
    AST.Prog.Suffixed
      ( AST.Prog.Suffixed
          ( AST.Prog.Suffixed
              ( AST.Prog.Suffixed
                  ( AST.Prog.NameSeg ("s", [])
                  , AST.Prog.AugDot(Syntax.Common.DSId "constants", []))
              , (AST.Prog.AugDot(Syntax.Common.DSId "all", [])))
          , AST.Prog.AugDot((Syntax.Common.DSId "config"), []))
      , (AST.Prog.AugDot((Syntax.Common.DSId "replica_ids"), [])))
  in
  (* The variables assigned in both branches (we ensure this is the same for both) *)
  let if_ann: TranslatorMetadata.Definitions.ite_functionalize_t =
    TranslatorMetadata.Definitions.(
      { assigned_vars =
          NonEmptyList.coerce
            [ Moder.Definitions.
                ({ mq_outvar = NonEmptyList.singleton "sent_packets"
                 ; fieldlike = None })
            ; Moder.Definitions.
                ({ mq_outvar = NonEmptyList.singleton "s'"
                 ; fieldlike = None}) ]
      ; branch_permutations =
          Moder.Definitions.(
            { vars_then =
                NonEmptyList.coerce
                  [ { mq_outvar = NonEmptyList.singleton "sent_packets"
                    ; fieldlike = None }
                  ; { mq_outvar = NonEmptyList.singleton "s'"
                    ; fieldlike = None} ]
            ; vars_else =
                (* NOTE: This is a permutation of `assigned_vars`; the order
                   variables are determined differs *)
                NonEmptyList.coerce
                  [ { mq_outvar = NonEmptyList.singleton "s'"
                    ; fieldlike = None }
                  ; { mq_outvar = NonEmptyList.singleton "sent_packets"
                    ; fieldlike = None} ]})})
  in
  let if_guard: AST.Prog.expr_t =
    (* NOTE: The binary op annotations are all None; everything here is
       input-moded and so does not need functionalization *)
    let if_guard_lreplicaconstantsvalid_arglist_ann
      : TranslatorMetadata.Definitions.arglist_functionalize_t =
      Moder.Definitions.(
        { callee = NonEmptyList.singleton "LReplicaConstantsValid"
        ; in_exprs =
            (* NOTE: These are unannotated (ParserPass) expressions *)
            [Syntax.ParserPass.Prog.Suffixed
               ( (Syntax.ParserPass.Prog.NameSeg ("s", []))
               , (Syntax.ParserPass.Prog.AugDot(Syntax.Common.DSId "constants", [])))]
        ; out_vars =
            (* NOTE: when out_vars is empty, it means this invocation does not
               need to be functionalized *)
            [] })
    in
    AST.Prog.Binary
      ( None, Syntax.Common.And
      , (AST.Prog.Binary
           ( None, Syntax.Common.In
           , AST.Prog.Suffixed
               ( (AST.Prog.NameSeg ("inp", []))
               , (AST.Prog.AugDot ((Syntax.Common.DSId "src"), [])))
           , s_constants_all_config_replica_ids))
      , (AST.Prog.Binary
           ( None, Syntax.Common.And
           , (AST.Prog.Suffixed
                ( (AST.Prog.NameSeg ("BalLt", []))
                , (AST.Prog.ArgList
                     ( {AST.Prog.positional
                        = [(AST.Prog.Suffixed
                              ( (AST.Prog.NameSeg ("s", []))
                              , (AST.Prog.AugDot
                                   ((Syntax.Common.DSId "max_bal"), []))))
                          ; (AST.Prog.Suffixed
                               ( (AST.Prog.NameSeg ("m", []))
                               , (AST.Prog.AugDot
                                    ((Syntax.Common.DSId "bal_1a"), []))))
                          ]
                       ; named = [] }
                     , None))))
           , (AST.Prog.Suffixed
                ( (AST.Prog.NameSeg("LReplicaConstantsValid", []))
                , (AST.Prog.ArgList
                     ({ AST.Prog.positional
                        = [AST.Prog.Suffixed
                             ( (AST.Prog.NameSeg ("s", []))
                             , (AST.Prog.AugDot(Syntax.Common.DSId "constants", [])))]
                      ; named = [] }
                     , Some if_guard_lreplicaconstantsvalid_arglist_ann)))))))
  in
  let if_then: AST.Prog.expr_t =
    let if_then_eq_sent_packets: AST.Prog.expr_t =
      let if_then_eq_sent_packets_lpacket: AST.Prog.expr_t =
        (AST.Prog.Suffixed
           ( AST.Prog.NameSeg("LPacket", [])
           , (AST.Prog.ArgList
                ({ AST.Prog.positional =
                     [ AST.Prog.Suffixed
                         ( AST.Prog.NameSeg("inp", [])
                         , AST.Prog.AugDot(Syntax.Common.DSId "src", []))
                     ; AST.Prog.Suffixed
                         ( s_constants_all_config_replica_ids
                         , AST.Prog.Sel
                             (AST.Prog.Suffixed
                                ( AST.Prog.Suffixed
                                    ( (AST.Prog.NameSeg("s", []))
                                    , (AST.Prog.AugDot(Syntax.Common.DSId "constants", [])))
                                , (AST.Prog.AugDot(Syntax.Common.DSId "my_index", [])))))
                     ; AST.Prog.Suffixed
                         ( AST.Prog.NameSeg("RslMessage_1b", [])
                         , AST.Prog.ArgList
                             ({ AST.Prog.positional =
                                  [ AST.Prog.Suffixed
                                      ( AST.Prog.NameSeg("m", [])
                                      , AST.Prog.AugDot(Syntax.Common.DSId "bal_1a", []))
                                  ; AST.Prog.Suffixed
                                      ( AST.Prog.NameSeg("s", [])
                                      , AST.Prog.AugDot(Syntax.Common.DSId "log_truncation_point", []))
                                  ; (AST.Prog.Suffixed
                                       ( AST.Prog.NameSeg("s", [])
                                       , AST.Prog.AugDot(Syntax.Common.DSId "votes", [])))]
                              ; named = [] }
                             (* NOTE: The annotation for the invocation of
                                `RslMessage_1b` (a constructor) is `None`, which
                                we by default assume means all arguments are
                                input-moded *)
                             , None))]
                 ; named = [] }
                (* NOTE: The annotation for the invocation of `LPacket` (a
                   constructor) is `None`, which we by default assume means all
                   arguments are input-moded *)
                , None ))))
      in
      let if_then_eq_sent_packets_ann =
        (* NOTE: You should first check the annotation (if present) to determine
           the binary operation; a guarantee of the earlier phases is that this
           always agrees with the binary op listed in the AST *)
        Moder.Definitions.(
          Eq
            { outvar_is_left = true
            ; outvar =
                { mq_outvar = NonEmptyList.singleton "sent_packets"
                ; fieldlike = None }})
      in
      (AST.Prog.Binary
         ( Some if_then_eq_sent_packets_ann
         , Syntax.Common.Eq
         , AST.Prog.NameSeg ("sent_packets", [])
         , AST.Prog.SeqDisplay
              (AST.Prog.SeqEnumerate [if_then_eq_sent_packets_lpacket])))
    in
    let if_then_eq_s': AST.Prog.expr_t =
      let if_then_eq_s'_ann =
        Moder.Definitions.(
          Eq
            { outvar_is_left = true
            ; outvar =
                { mq_outvar = NonEmptyList.singleton "s'"
                ; fieldlike = None }})
      in
      AST.Prog.Binary
        ( Some if_then_eq_s'_ann
        , Syntax.Common.Eq
        , (AST.Prog.NameSeg ("s'", []))
        , (AST.Prog.Suffixed
             ( (AST.Prog.NameSeg ("s", []))
             , (AST.Prog.DataUpd
                  (NonEmptyList.(::)
                     ( ( Either.left "max_bal"
                       , AST.Prog.Suffixed
                           ( AST.Prog.NameSeg ("m", [])
                           , AST.Prog.AugDot
                               ((Syntax.Common.DSId "bal_1a"), [])))
                     , []))))))
    in
    let if_then_conj_ann: Moder.Definitions.binary_op_functionalize_and_t =
      (* NOTE: You will probably not need to use these for translation, except
         to check if there are /any/ output-moded variables to be assigned (if
         not, then it is an input-moded expression that will be pushed to the
         requires clause) *)
      Moder.Definitions.(
        { conj_left =
            [{mq_outvar = NonEmptyList.singleton "sent_packets"; fieldlike = None}]
        ; conj_right =
            [{mq_outvar = NonEmptyList.singleton "s'"; fieldlike = None}] })
    in
    (AST.Prog.Binary
       (* NOTE: You should first check the annotation (if present) to determine
          the binary operation; a guarantee of the earlier phases is that this
          always agrees with the binary op listed in the AST *)
       ( Some (Moder.Definitions.(And if_then_conj_ann))
       , Syntax.Common.And
       , if_then_eq_sent_packets
       , if_then_eq_s' ))
  in
  let if_else: AST.Prog.expr_t =
    let if_else_conj_ann =
      Moder.Definitions.(
        And
          { conj_left =
              [{ mq_outvar = NonEmptyList.singleton "s'"
               ; fieldlike = None }]
          ; conj_right =
              [{ mq_outvar = NonEmptyList.singleton "sent_packets"
               ; fieldlike = None }]})
    in
    AST.Prog.Binary
      ( Some if_else_conj_ann
      , Syntax.Common.And
      , AST.Prog.Binary
          ( Some Moder.Definitions.(
                Eq
                  { outvar_is_left = true
                  ; outvar =
                      { mq_outvar = NonEmptyList.singleton "s'"
                      ; fieldlike = None }})
          , Syntax.Common.Eq
          , (AST.Prog.NameSeg ("s'", []))
          , (AST.Prog.NameSeg ("s", [])))
      , AST.Prog.Binary
          ( Some Moder.Definitions.(
                Eq
                  { outvar_is_left = true
                  ; outvar =
                      { mq_outvar = NonEmptyList.singleton "sent_packets"
                      ; fieldlike = None }})
          , Syntax.Common.Eq
          , (AST.Prog.NameSeg ("sent_packets", []))
          , (AST.Prog.SeqDisplay(AST.Prog.SeqEnumerate []))))
  in
  AST.Prog.Let
    { ghost = false
    ; pats =(NonEmptyList.(::) ((AST.Prog.PatVar ("m", None)), []))
    ; defs =
        (NonEmptyList.(::)
           ( (AST.Prog.Suffixed
                ( (AST.Prog.NameSeg ("inp", []))
                , (AST.Prog.AugDot((Syntax.Common.DSId "msg"), []))))
           , []))
    ; body =
        (AST.Prog.If (Some if_ann, if_guard, if_then, if_else)) }
