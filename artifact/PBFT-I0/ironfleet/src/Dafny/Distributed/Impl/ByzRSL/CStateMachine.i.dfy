include "CTypes.i.dfy"
include "AppInterface.i.dfy"
include "../../Protocol/ByzRSL/StateMachine.i.dfy"
include "../../Common/Native/NativeTypes.i.dfy"

module LiveByzRSL__CStateMachine_i{
import opened LiveByzRSL__StateMachine_i
import opened LiveByzRSL__AppInterface_i
// import opened AppStateMachine_s
import opened LiveByzRSL__CTypes_i
import opened LiveByzRSL__Types_i
import opened Native__NativeTypes_i
import opened Native__NativeTypes_s
import opened GenericRefinement_i
import opened AppStateMachine_i

/************************** AutoMan Translation ************************/
  /** 5 + 3 + 1 */
  function method CHandleRequest(state: CAppState, request: CRequest) : (CAppState, CReply) 
		requires CAppStateIsValid(state)
		requires CRequestIsValid(request)
		ensures var (lr0, lr1) := HandleRequest(AbstractifyCAppStateToAppState(state), AbstractifyCRequestToRequest(request)); var (cr0, cr1) := CHandleRequest(state, request); CAppStateIsValid(cr0) && CReplyIsValid(cr1) && (AbstractifyCAppStateToAppState(cr0), AbstractifyCReplyToReply(cr1)) == (lr0, lr1)
	{
		var (new_state, reply) :=
			HandleAppRequest(state, request.request); 	
		(new_state, CReply(request.client, request.seqno, reply))
	}

  /** 12 + 5 + 21 */
  function method {:opaque} CHandleRequestBatchHidden(state: CAppState, batch: CRequestBatch) : (seq<CAppState>, seq<CReply>) 
		requires CAppStateIsValid(state)
		requires CRequestBatchIsValid(batch)
		ensures var (states, replies) := CHandleRequestBatchHidden(state, batch); |states| == |batch| + 1 && |replies| == |batch| && (forall i :: 0 <= i && i < |batch| ==> replies[i].CReply?)
		decreases |batch|
		ensures var (lr0, lr1) := HandleRequestBatchHidden(AbstractifyCAppStateToAppState(state), AbstractifyCRequestBatchToRequestBatch(batch)); var (cr0, cr1) := CHandleRequestBatchHidden(state, batch); (forall i :: i in cr0 ==> CAppStateIsValid(i)) && (forall i :: i in cr1 ==> CReplyIsValid(i)) && (AbstractifySeq(cr0, AbstractifyCAppStateToAppState), AbstractifySeq(cr1, AbstractifyCReplyToReply)) == (lr0, lr1)
	{
    reveal_HandleRequestBatchHidden();
		if |batch| == 0 then 
      /** Manually Added */
      var states := [state];
      var replies := [];
      ghost var s := AbstractifyCAppStateToAppState(state);
      ghost var b := AbstractifyCRequestBatchToRequestBatch(batch);
      ghost var (ss', rs') := HandleRequestBatchHidden(s, b);
      assert AbstractifySeq(states, AbstractifyCAppStateToAppState) == ss';
      assert AbstractifySeq(replies, AbstractifyCReplyToReply) == rs';
      assert HandleRequestBatchHidden(AbstractifyCAppStateToAppState(state), AbstractifyCRequestBatchToRequestBatch(batch)) ==
              (AbstractifySeq(states, AbstractifyCAppStateToAppState), AbstractifySeq(replies, AbstractifyCReplyToReply));
			([state], []) 
		else 
			var (restStates, restReplies) := 
				CHandleRequestBatchHidden(state, batch[ .. |batch| - 1]); 			
			var (new_state, reply) := 
				HandleAppRequest(restStates[|restStates| - 1], batch[|batch| - 1].request); 
      /** Manually Added */			
      var states := restStates+[new_state];
      var replies := restReplies+[CReply(batch[|batch|-1].client, batch[|batch|-1].seqno, reply)];

      ghost var s := AbstractifyCAppStateToAppState(state);
      ghost var b := AbstractifyCRequestBatchToRequestBatch(batch);
      ghost var (rs, rp) := HandleRequestBatchHidden(s, b[..|b|-1]);
      ghost var (s1, r) := AppHandleRequest(rs[|rs|-1], b[|b|-1].request);
      assert b[..|b|-1] == AbstractifyCRequestBatchToRequestBatch(batch[..|batch|-1]);
      ghost var (ss', rs') := HandleRequestBatchHidden(s, b);
      assert AbstractifySeq(states, AbstractifyCAppStateToAppState) == ss';
      assert AbstractifySeq(replies, AbstractifyCReplyToReply) == rs';
      assert HandleRequestBatchHidden(AbstractifyCAppStateToAppState(state), AbstractifyCRequestBatchToRequestBatch(batch)) ==
              (AbstractifySeq(states, AbstractifyCAppStateToAppState), AbstractifySeq(replies, AbstractifyCReplyToReply));
			(restStates + [new_state], restReplies + [CReply(batch[|batch| - 1].client, batch[|batch| - 1].seqno, reply)])
	}

  /** 6 + 4 + 1 */
  function method CHandleRequestBatch(state: CAppState, batch: CRequestBatch) : (seq<CAppState>, seq<CReply>) 
		requires CAppStateIsValid(state)
		requires CRequestBatchIsValid(batch)
		ensures var (states, replies) := CHandleRequestBatch(state, batch); states[0] == state && |states| == |batch| + 1 && |replies| == |batch| && (forall i :: 0 <= i && i < |batch| ==> replies[i].CReply? && (states[i + 1], replies[i].reply) == HandleAppRequest(states[i], batch[i].request) && replies[i].client == batch[i].client && replies[i].seqno == batch[i].seqno)
		ensures var (lr0, lr1) := HandleRequestBatch(AbstractifyCAppStateToAppState(state), AbstractifyCRequestBatchToRequestBatch(batch)); var (cr0, cr1) := CHandleRequestBatch(state, batch); (forall i :: i in cr0 ==> CAppStateIsValid(i)) && (forall i :: i in cr1 ==> CReplyIsValid(i)) && (AbstractifySeq(cr0, AbstractifyCAppStateToAppState), AbstractifySeq(cr1, AbstractifyCReplyToReply)) == (lr0, lr1)
	{
		var (states, replies) := 
			CHandleRequestBatchHidden(state, batch); 		
    /** Manually Added */
    lemma_CHandleRequestBatchHidden(state, batch, states, replies);
		(states, replies)
	}

/************************** AutoMan Translation End ************************/

/************************** Manual Code for I0 ************************/
/** 0 + 0 + 25 */
lemma{:timeLimitMultiplier 2} lemma_CHandleRequestBatchHidden(state:CAppState, batch:CRequestBatch, states:seq<CAppState>, replies:seq<CReply>)
  requires CAppStateIsValid(state)
  requires CRequestBatchIsValid(batch)
  requires (states, replies) == CHandleRequestBatchHidden(state, batch);
  ensures  && states[0] == state
           && |states| == |batch|+1 
           && |replies| == |batch|
           && (forall i :: 0 <= i < |batch| ==>
                    && replies[i].CReply? 
                    && ((states[i+1], replies[i].reply) == HandleAppRequest(states[i], batch[i].request))
                    && replies[i].client == batch[i].client
                    && replies[i].seqno == batch[i].seqno)
  decreases |batch|
{
  reveal CHandleRequestBatchHidden();
  if |batch| == 0 {
    assert && |states| == |batch|+1 
           && |replies| == |batch|
           && (forall i :: 0 <= i < |batch| ==> ((states[i+1], replies[i].reply) == HandleAppRequest(states[i], batch[i].request)));
  } else {
    var restBatch := CHandleRequestBatchHidden(state, batch[..|batch|-1]);
    var restStates := restBatch.0;
    var AHR_result := HandleAppRequest(restStates[|restStates|-1], batch[|batch|-1].request);
    lemma_CHandleRequestBatchHidden(state, batch[..|batch|-1], restStates, restBatch.1);
    assert replies[|batch|-1].reply == AHR_result.1;
  }
}
/************************** Manual Code for I0 End ************************/
}