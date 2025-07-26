include "CTypes.i.dfy"
include "AppInterface.i.dfy"
include "../../Protocol/RSL/StateMachine.i.dfy"
include "../../Common/Native/NativeTypes.i.dfy"

module LiveRSL__CStateMachine_i{
import opened LiveRSL__StateMachine_i
import opened LiveRSL__AppInterface_i
import opened AppStateMachine_s
import opened LiveRSL__CTypes_i
import opened Native__NativeTypes_i
import opened Native__NativeTypes_s

datatype CStateMachine = CStateMachine(
  app : AppStateMachine
)

method CStateMachineInit() returns (app:CStateMachine)
ensures app.app.Abstractify() == AppInitialize()
{
  var app_statemachine := AppStateMachine.Initialize();
  app := CStateMachine(app_statemachine);
}

// 注释里是我自己写的一个非递归实现
// function method CHandleRequestBatchHidden(app:AppStateMachine, batch:CRequestBatch) : (seq<AppState>, seq<CReply>)
// {
//   if |batch| == 0 then 
//     ([app.Abstractify()], [])
//   else
//     var (restStates, restReplies) := CHandleRequestBatchHidden(app.Abstractify(), batch[..|batch|-1]);
//     var (new_state, reply) := state.AppHandleRequest(restStates[|restStates|-1], batch[|batch|-1].request);
//     (restStates+[new_state], restReplies+[CReply(batch[|batch|-1].client, batch[|batch|-1].seqno, reply)])
    
//     // a more efficient implmentation
    
//     // var i:uint64 := 0;
//     // var stateArr := new AppState[|batch| as uint64];
//     // var repliesArr := new CReply[|batch| as uint64];

//     // while i < |batch| as uint64
//     // {
//     //   var state, reply := AppHandleRequest(batch[i].request);
//     //   var newReply := CReply(batch[i].client, batch[i].seqno, reply);

//     //   stateArr[i] := state;
//     //   repliesArr[i] := newReply;
//     //   i := i + 1;
//     // }
//     // states := stateArr[..];
//     // replies := repliesArr[..];
// }

method CHandleStateSupply(state:AppState) returns (app:CStateMachine)
{
  var app_statemachine := AppStateMachine.Deserialize(state);
  app := CStateMachine(app_statemachine);
}

method CStateSupply(state_machine:CStateMachine) returns (state:AppState)
{
  state := state_machine.app.Serialize();
}

method CHandleRequestBatch(app_statemachine:CStateMachine, batch:CRequestBatch) returns (replies:seq<CReply>)
requires CRequestBatchIsValid(batch)
ensures |replies| == |batch|
ensures forall i :: 0 <= i < |batch| ==> replies[i].CReply? && CReplyIsValid(replies[i])
{
  if |batch| == 0 {
    replies := [];
  }
  else{
    var i:uint64 := 0;
    var repliesArr := new CReply[|batch| as uint64];

    while i < |batch| as uint64
    {
      var reply := app_statemachine.app.HandleRequest(batch[i].request);
      var newReply := CReply(batch[i].client, batch[i].seqno, reply);

      repliesArr[i] := newReply;
      i := i + 1;
    }
    replies := repliesArr[..];
  }
  lemma_CHandleRequestBatch(app_statemachine, batch, replies);
}

lemma {:axiom} lemma_CHandleRequestBatch(app_statemachine:CStateMachine, batch:CRequestBatch, replies:seq<CReply>)
  requires CRequestBatchIsValid(batch)
  ensures |replies| == |batch|
  ensures forall i :: 0 <= i < |batch| ==> replies[i].CReply? && CReplyIsValid(replies[i])
}