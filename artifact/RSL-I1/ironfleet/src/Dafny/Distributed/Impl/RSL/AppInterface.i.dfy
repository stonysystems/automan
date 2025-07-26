include "../../Common/Collections/Maps.i.dfy"
include "../../Protocol/RSL/Configuration.i.dfy"
include "../../Protocol/RSL/Message.i.dfy"
include "../../Protocol/RSL/Types.i.dfy"
include "../Common/GenericMarshalling.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Services/RSL/AppStateMachine.s.dfy"

module LiveRSL__AppInterface_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened Collections__Maps_i
  import opened LiveRSL__Configuration_i
  import opened LiveRSL__Message_i
  import opened LiveRSL__Types_i
  import opened Common__GenericMarshalling_i
  import opened Common__NodeIdentity_i
  import opened AppStateMachine_i
  import opened Math__mul_nonlinear_i
  import opened Math__mul_i

  type CAppState = uint64

  datatype CAppMessage = CAppIncrement() | CAppReply(response:uint64) | CAppInvalid()

  ////////////////////////////////////////////////
  //      CAppState
  ////////////////////////////////////////////////

  predicate CAppStateIsValid(appstate:CAppState)
  {
    true
  }


  predicate CAppStateIsAbstractable(appstate:CAppState)
  {
    true
  }

  function AbstractifyCAppStateToAppState(appstate:CAppState) : AppState
    requires CAppStateIsAbstractable(appstate)
  {
    appstate
  }

  function {:opaque} AbstractifyCAppStateSeqToAppStateSeq(s:seq<CAppState>) : seq<AppState>
    requires forall i :: i in s ==> CAppStateIsAbstractable(i)
    ensures |AbstractifyCAppStateSeqToAppStateSeq(s)| == |s|
    ensures forall i :: 0 <= i < |AbstractifyCAppStateSeqToAppStateSeq(s)| ==> AbstractifyCAppStateSeqToAppStateSeq(s)[i] == AbstractifyCAppStateToAppState(s[i])
  {
    if |s| == 0 then
    []
    else
    [AbstractifyCAppStateToAppState(s[0])] + AbstractifyCAppStateSeqToAppStateSeq(s[1..])
  }


  /////////////  CAppState parsing and marshalling

  function method CAppState_grammar() : G { GUint64 }

  function method parse_AppState(val:V) : CAppState
    requires ValInGrammar(val, CAppState_grammar())
    ensures  CAppStateIsAbstractable(parse_AppState(val))
  {
    val.u as CAppState
  }

  function method AppStateMarshallable(msg:CAppState) : bool
  {
    true
  }

  method MarshallAppState(c:CAppState) returns (val:V)
    requires AppStateMarshallable(c)
    ensures  ValInGrammar(val, CAppState_grammar())
    ensures  ValidVal(val)
    ensures  parse_AppState(val) == c
  {
    val := VUint64(c);
  }

  function max_app_state_size():int { 0x8000 } // 2^15  // 0xFEFF_FFCF_FFFF_FF00


  lemma lemma_AppStateBound(c:CAppState, val:V)
    requires ValInGrammar(val, CAppState_grammar())
    requires ValidVal(val)
    requires parse_AppState(val) == c
    ensures  SizeOfV(val) < max_app_state_size()
  {
  }

  ////////////////////////////////////////////////
  //      CAppMessage
  ////////////////////////////////////////////////

  // These trivial definitions are included here, since these functions
  // should be part of our interface with the app.  Future apps may have
  // more complex requirements

  predicate method CAppMessageIsValid(c:CAppMessage)
  {
    CAppMessageIsAbstractable(c)
  }

  predicate method CAppMessageIsAbstractable(c:CAppMessage)
  {
    true
  }

  function AbstractifyCAppMessageToAppMessage(c:CAppMessage) : AppMessage
    requires CAppMessageIsAbstractable(c)
  {
    match c {
      case CAppIncrement => AppIncrementRequest()
      case CAppReply(response) => AppIncrementReply(response)
      case CAppInvalid => AppInvalidReply()
    }
  }

  /////////////  CAppMessage parsing and marshalling

  function method CAppMessage_grammar() : G { GTaggedUnion([GTuple([]), GUint64, GTuple([])]) }

  function method parse_AppMessage(val:V) : CAppMessage
    requires ValInGrammar(val, CAppMessage_grammar())
  {
    if val.c == 0 then
      CAppIncrement()
    else if val.c == 1 then
      assert ValInGrammar(val.val, CAppMessage_grammar().cases[1]);
      CAppReply(val.val.u)
    else
      assert val.c == 2;
      CAppInvalid()
  }

  method MarshallCAppMessage(c:CAppMessage) returns (val:V)
    requires CAppMessageIsAbstractable(c)
    requires CAppMessageIsValid(c)
    ensures  ValInGrammar(val, CAppMessage_grammar())
    ensures  ValidVal(val)
    ensures  parse_AppMessage(val) == c
  {
    match c {
      case CAppIncrement       => val := VCase(0, VTuple([]));
      case CAppReply(response) => val := VCase(1, VUint64(response));
      case CAppInvalid         => val := VCase(2, VTuple([]));
    }
    assert parse_AppMessage(val) == c;
  }

  function method max_val_len() : int { 64 }  //{ 0x100_0000 }    // 2^24


  lemma lemma_AppMessageBound(c:CAppMessage, val:V)
    requires ValInGrammar(val, CAppMessage_grammar())
    requires CAppMessageIsValid(c)
    requires parse_AppMessage(val) == c
    ensures  ValidVal(val)
    ensures  SizeOfV(val) < max_val_len()   // 0x100_0000; // 2^24
  {
    forall ensures SeqSum([]) == 0
    {
      reveal SeqSum();
    }
  }


  ////////////////////////////////////////////////
  //     App State Machine
  ////////////////////////////////////////////////

  function method CAppStateInit() : CAppState
    ensures var s := CAppStateInit();
    CAppStateIsAbstractable(s)
    && AbstractifyCAppStateToAppState(s) == AppInitialize()
    && AppStateMarshallable(s)
  {
    0 as uint64
  }


  // method CappedIncrImpl(v:uint64) returns (v':uint64)
  //   requires 0 <= v <= 0xffff_ffff_ffff_ffff
  //   ensures v' == CappedIncr(v)
  // {
  //   if (v == 0xffff_ffff_ffff_ffff) {
  //     v' := v;
  //   } else {
  //     v' := v + 1;
  //   }
  // }

  function method CappedIncrImpl(v:uint64) : uint64
    requires 0 <= v <= 0xffff_ffff_ffff_ffff
    ensures var v' := CappedIncrImpl(v); v' == CappedIncr(v)
  {
    if (v == 0xffff_ffff_ffff_ffff) then
      v
    else
      v + 1
  }

  // method HandleAppRequest(appState:CAppState, request:CAppMessage) returns (appState':CAppState, reply:CAppMessage)
  //   requires CAppStateIsAbstractable(appState)
  //   requires CAppMessageIsAbstractable(request)
  //   ensures  CAppStateIsAbstractable(appState')
  //   ensures  CAppMessageIsAbstractable(reply)
  //   ensures  AppStateMarshallable(appState')
  //   ensures  AppHandleRequest(AbstractifyCAppStateToAppState(appState), AbstractifyCAppMessageToAppMessage(request)) ==
  //              (AbstractifyCAppStateToAppState(appState'), AbstractifyCAppMessageToAppMessage(reply))
  // {
  //   if request.CAppIncrement? {
  //     appState' := CappedIncrImpl(appState);
  //     reply := CAppReply(appState');
  //   } else {
  //     appState' := appState;
  //     reply := CAppInvalid();
  //   }
  // }

  function method HandleAppRequest(appState:CAppState, request:CAppMessage) : (CAppState, CAppMessage)
    requires CAppStateIsAbstractable(appState)
    requires CAppMessageIsAbstractable(request)
    ensures var (appState', reply) := HandleAppRequest(appState, request);
            && CAppStateIsAbstractable(appState')
            && CAppMessageIsAbstractable(reply)
            && AppStateMarshallable(appState')
            && AppHandleRequest(AbstractifyCAppStateToAppState(appState), AbstractifyCAppMessageToAppMessage(request)) ==
               (AbstractifyCAppStateToAppState(appState'), AbstractifyCAppMessageToAppMessage(reply))
  {
    if request.CAppIncrement? then
      (CappedIncrImpl(appState), CAppReply(CappedIncrImpl(appState)))
    else
      (appState, CAppInvalid())
  }
}
