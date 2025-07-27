/**********************************************************************
AUTOMAN LOG

[Module] LiveByzRSL__Election_i

[Action] ElectionStateInit
Check passed

[Action] ElectionStateProcessHeartbeat
Check passed

[Action] ElectionStateCheckForViewTimeout
Check passed

[Action] ElectionStateCheckForQuorumOfViewSuspicions
Check passed

[Action] ElectionStateReflectReceivedRequest
Check passed

[Action] ElectionStateReflectExecutedRequestBatch
Check passed
**********************************************************************/

include ""


module Impl_LiveByzRSL__Election_i 
{

	datatype CElectionState = 
	CElectionState(
		constants: CReplicaConstants, 
		current_view: CBallot, 
		current_view_suspectors: set<int>, 
		epoch_end_time: int, 
		epoch_length: int, 
		requests_received_this_epoch: seq<CRequest>, 
		requests_received_prev_epochs: seq<CRequest>
	)

	predicate CElectionStateIsValid(s: CElectionState) 
	{
		CElectionStateIsAbstractable(s) 
		&& 
		CReplicaConstantsIsValid(s.constants) 
		&& 
		CBallotIsValid(s.current_view) 
		&& 
		(forall i :: i in s.requests_received_this_epoch ==> CRequestIsValid(i)) 
		&& 
		(forall i :: i in s.requests_received_prev_epochs ==> CRequestIsValid(i))
	}

	predicate CElectionStateIsAbstractable(s: CElectionState) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		CBallotIsAbstractable(s.current_view) 
		&& 
		(forall i :: i in s.requests_received_this_epoch ==> CRequestIsAbstractable(i)) 
		&& 
		(forall i :: i in s.requests_received_prev_epochs ==> CRequestIsAbstractable(i))
	}

	function AbstractifyCElectionStateToElectionState(s: CElectionState) : ElectionState 
		requires CElectionStateIsAbstractable(s)
	{
		ElectionState(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.current_view), s.current_view_suspectors, s.epoch_end_time, s.epoch_length, AbstractifySeq(s.requests_received_this_epoch, AbstractifyCRequestToRequest), AbstractifySeq(s.requests_received_prev_epochs, AbstractifyCRequestToRequest))
	}

	function method CComputeSuccessorView(b: CBallot, c: CConstants) : CBallot 
		requires CBallotIsValid(b)
		requires CConstantsIsValid(c)
		ensures var lr := ComputeSuccessorView(AbstractifyCBallotToBallot(b), AbstractifyCConstantsToLConstants(c)); var cr := CComputeSuccessorView(b, c); CBallotIsValid(cr) && (AbstractifyCBallotToBallot(cr)) == (lr)
	{
		if b.proposer_id + 1 < |c.config.replica_ids| then 
			CBallot(b.seqno, b.proposer_id + 1) 
		else 
			CBallot(b.seqno + 1, 0)
	}

	function method CBoundRequestSequence(s: seq<CRequest>, lengthBound: CUpperBound) : seq<CRequest> 
		requires (forall i :: i in s ==> CRequestIsValid(i))
		requires CUpperBoundIsValid(lengthBound)
		ensures var lr := BoundRequestSequence(AbstractifySeq(s, AbstractifyCRequestToRequest), AbstractifyCUpperBoundToUpperBound(lengthBound)); var cr := CBoundRequestSequence(s, lengthBound); (forall i :: i in cr ==> CRequestIsValid(i)) && (AbstractifySeq(cr, AbstractifyCRequestToRequest)) == (lr)
	{
		if lengthBound.CUpperBoundFinite? && 0 <= lengthBound.n && lengthBound.n < |s| then 
			s[ .. lengthBound.n] 
		else 
			s
	}

	function method CRequestsMatch(r1: CRequest, r2: CRequest) : bool 
		requires CRequestIsValid(r1)
		requires CRequestIsValid(r2)
		ensures var lr := RequestsMatch(AbstractifyCRequestToRequest(r1), AbstractifyCRequestToRequest(r2)); var cr := CRequestsMatch(r1, r2); (cr) == (lr)
	{
		r1.CRequest? 
		&& 
		r2.CRequest? 
		&& 
		r1.client == r2.client 
		&& 
		r1.seqno == r2.seqno
	}

	function method CRequestSatisfiedBy(r1: CRequest, r2: CRequest) : bool 
		requires CRequestIsValid(r1)
		requires CRequestIsValid(r2)
		ensures var lr := RequestSatisfiedBy(AbstractifyCRequestToRequest(r1), AbstractifyCRequestToRequest(r2)); var cr := CRequestSatisfiedBy(r1, r2); (cr) == (lr)
	{
		r1.CRequest? 
		&& 
		r2.CRequest? 
		&& 
		r1.client == r2.client 
		&& 
		r1.seqno <= r2.seqno
	}

	function method CRemoveAllSatisfiedRequestsInSequence(s: seq<CRequest>, r: CRequest) : seq<CRequest> 
		requires (forall i :: i in s ==> CRequestIsValid(i))
		requires CRequestIsValid(r)
		ensures var lr := RemoveAllSatisfiedRequestsInSequence(AbstractifySeq(s, AbstractifyCRequestToRequest), AbstractifyCRequestToRequest(r)); var cr := CRemoveAllSatisfiedRequestsInSequence(s, r); (forall i :: i in cr ==> CRequestIsValid(i)) && (AbstractifySeq(cr, AbstractifyCRequestToRequest)) == (lr)
	{
		if |s| == 0 then 
			[] 
		else 
			if CRequestSatisfiedBy(s[0], r) then 
				CRemoveAllSatisfiedRequestsInSequence(s[1 .. ], r) 
			else 
				[s[0]] + CRemoveAllSatisfiedRequestsInSequence(s[1 .. ], r)
	}

	function method CCheckRequestValidInReqSeq(s: seq<CRequest>, r: CRequest) : bool 
		requires (forall i :: i in s ==> CRequestIsValid(i))
		requires CRequestIsValid(r)
		ensures var lr := CheckRequestValidInReqSeq(AbstractifySeq(s, AbstractifyCRequestToRequest), AbstractifyCRequestToRequest(r)); var cr := CCheckRequestValidInReqSeq(s, r); (cr) == (lr)
	{
		if |s| == 0 then 
			true 
		else 
			var v := 
				if CRequestsMatch(s[0], r) && s[0].request != r.request then 
					false 
				else 
					true; 			
			if v then 
				CCheckRequestValidInReqSeq(s[1 .. ], r) 
			else 
				v
	}

	function method CCheckRequestValid(s: CElectionState, r: CRequest) : bool 
		requires CElectionStateIsValid(s)
		requires CRequestIsValid(r)
		ensures var lr := CheckRequestValid(AbstractifyCElectionStateToElectionState(s), AbstractifyCRequestToRequest(r)); var cr := CCheckRequestValid(s, r); (cr) == (lr)
	{
		CCheckRequestValidInReqSeq(s.requests_received_this_epoch, r) 
		&& 
		CCheckRequestValidInReqSeq(s.requests_received_prev_epochs, r)
	}

	function method CElectionStateInit(c: CReplicaConstants) : CElectionState 
		requires CReplicaConstantsIsValid(c)
		requires |c.all.config.replica_ids| > 0
		ensures var es := CElectionStateInit(c); CElectionStateIsValid(es) && ElectionStateInit(AbstractifyCElectionStateToElectionState(es), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := 
			c; 		
		var t2 := 
			CBallot(1, 0); 		
		var t3 := 
			{}; 		
		var t4 := 
			0; 		
		var t5 := 
			c.all.params.baseline_view_timeout_period; 		
		var t6 := 
			[]; 		
		var t7 := 
			[]; 		
		CElectionState(t1, t2, t3, t4, t5, t6, t7)
	}

	function method CElectionStateProcessHeartbeat(es: CElectionState, p: CPacket, clock: int) : CElectionState 
		requires CElectionStateIsValid(es)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_Heartbeat?
		ensures var es' := CElectionStateProcessHeartbeat(es, p, clock); CElectionStateIsValid(es') && ElectionStateProcessHeartbeat(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCPacketToRslPacket(p), clock)
	{
		var t1 := 
			if p.src !in es.constants.all.config.replica_ids then 
				var t1 := 
					es; 				
				t1 
			else 
				var t1 := 
					var sender_index := 
						CGetReplicaIndex(p.src, es.constants.all.config); 					
					var t1 := 
						if p.msg.bal_heartbeat == es.current_view && p.msg.suspicious then 
							var t1 := 
								es.(current_view_suspectors := es.current_view_suspectors + {sender_index}); 							
							t1 
						else 
							var t1 := 
								if CBalLt(es.current_view, p.msg.bal_heartbeat) then 
									var t1 := 
										var new_epoch_length := 
											UpperBoundedAdditionImpl(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val); 										
										var t1 := 
											es.(current_view := p.msg.bal_heartbeat, current_view_suspectors := if p.msg.suspicious then {sender_index} else {}, epoch_length := new_epoch_length, epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), requests_received_this_epoch := []); 										
										t1; 									
									t1 
								else 
									var t1 := 
										es; 									
									t1; 							
							t1; 					
					t1; 				
				t1; 		
		t1
	}

	function method CElectionStateCheckForViewTimeout(es: CElectionState, clock: int) : CElectionState 
		requires CElectionStateIsValid(es)
		ensures var es' := CElectionStateCheckForViewTimeout(es, clock); CElectionStateIsValid(es') && ElectionStateCheckForViewTimeout(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), clock)
	{
		var t1 := 
			if clock < es.epoch_end_time then 
				var t1 := 
					es; 				
				t1 
			else 
				var t1 := 
					if |es.requests_received_prev_epochs| == 0 then 
						var t1 := 
							var new_epoch_length := 
								es.constants.all.params.baseline_view_timeout_period; 							
							var t1 := 
								es.(epoch_length := new_epoch_length, epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := es.requests_received_this_epoch, requests_received_this_epoch := []); 							
							t1; 						
						t1 
					else 
						var t1 := 
							es.(current_view_suspectors := es.current_view_suspectors + {es.constants.my_index}, epoch_end_time := UpperBoundedAdditionImpl(clock, es.epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), requests_received_this_epoch := []); 						
						t1; 				
				t1; 		
		t1
	}

	function method CElectionStateCheckForQuorumOfViewSuspicions(es: CElectionState, clock: int) : CElectionState 
		requires CElectionStateIsValid(es)
		ensures var es' := CElectionStateCheckForQuorumOfViewSuspicions(es, clock); CElectionStateIsValid(es') && ElectionStateCheckForQuorumOfViewSuspicions(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), clock)
	{
		var t1 := 
			if (|es.current_view_suspectors| < CMinQuorumSize(es.constants.all.config)) || (!(CtUpperBound(es.current_view.seqno, es.constants.all.params.max_integer_val))) then 
				var t1 := 
					es; 				
				t1 
			else 
				var t1 := 
					var new_epoch_length := 
						UpperBoundedAdditionImpl(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val); 					
					var t1 := 
						es.(current_view := CComputeSuccessorView(es.current_view, es.constants.all), current_view_suspectors := {}, epoch_length := new_epoch_length, epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), requests_received_this_epoch := []); 					
					t1; 				
				t1; 		
		t1
	}

	function method CElectionStateReflectReceivedRequest(es: CElectionState, req: CRequest) : CElectionState 
		requires CElectionStateIsValid(es)
		requires CRequestIsValid(req)
		ensures var es' := CElectionStateReflectReceivedRequest(es, req); CElectionStateIsValid(es') && ElectionStateReflectReceivedRequest(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCRequestToRequest(req))
	{
		var t1 := 
			if (exists earlier_req :: ((earlier_req in es.requests_received_prev_epochs) || (earlier_req in es.requests_received_this_epoch)) && CRequestsMatch(earlier_req, req)) then 
				var t1 := 
					es; 				
				t1 
			else 
				var t1 := 
					es.(requests_received_this_epoch := CBoundRequestSequence(es.requests_received_this_epoch + [req], es.constants.all.params.max_integer_val)); 				
				t1; 		
		t1
	}

	function method CRemoveExecutedRequestBatch(reqs: seq<CRequest>, batch: CRequestBatch) : seq<CRequest> 
		requires (forall i :: i in reqs ==> CRequestIsValid(i))
		requires CRequestBatchIsValid(batch)
		decreases |batch|
		ensures var lr := RemoveExecutedRequestBatch(AbstractifySeq(reqs, AbstractifyCRequestToRequest), AbstractifyCRequestBatchToRequestBatch(batch)); var cr := CRemoveExecutedRequestBatch(reqs, batch); (forall i :: i in cr ==> CRequestIsValid(i)) && (AbstractifySeq(cr, AbstractifyCRequestToRequest)) == (lr)
	{
		if |batch| == 0 then 
			reqs 
		else 
			CRemoveExecutedRequestBatch(CRemoveAllSatisfiedRequestsInSequence(reqs, batch[0]), batch[1 .. ])
	}

	function method CElectionStateReflectExecutedRequestBatch(es: CElectionState, batch: CRequestBatch) : CElectionState 
		requires CElectionStateIsValid(es)
		requires CRequestBatchIsValid(batch)
		ensures var es' := CElectionStateReflectExecutedRequestBatch(es, batch); CElectionStateIsValid(es') && ElectionStateReflectExecutedRequestBatch(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCRequestBatchToRequestBatch(batch))
	{
		var t1 := 
			es.(requests_received_prev_epochs := CRemoveExecutedRequestBatch(es.requests_received_prev_epochs, batch), requests_received_this_epoch := CRemoveExecutedRequestBatch(es.requests_received_this_epoch, batch)); 		
		t1
	}
}
