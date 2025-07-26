include "../../Protocol/RSL/Election.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "CConfiguration.i.dfy"
include "CConstants.i.dfy"
include "../Common/Util.i.dfy"
include "../Common/UpperBound.i.dfy"

module LiveRSL__ElectionModel_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened LiveRSL__CMessage_i
// import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__ConstantsState_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__Election_i
// import opened LiveRSL__ElectionState_i
// import opened LiveRSL__MinCQuorumSize_i
// import opened LiveRSL__ConstantsState_i
import opened LiveRSL__Types_i
import opened Common__NodeIdentity_i
import opened Common__SeqIsUnique_i
import opened Common__SeqIsUniqueDef_i
import opened Common__UpperBound_s
import opened Common__UpperBound_i
import opened Common__Util_i
import opened Collections__Seqs_s
import opened Collections__Sets_i
import opened GenericRefinement_i


  /************************** AutoMan Translation ************************/
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
		ensures 
      var lr := ComputeSuccessorView(AbstractifyCBallotToBallot(b), AbstractifyCConstantsToLConstants(c)); 
      var cr := CComputeSuccessorView(b, c); 
      CBallotIsValid(cr) 
      && (AbstractifyCBallotToBallot(cr)) == (lr)
	{
		if b.proposer_id + 1 < |c.config.replica_ids| then 
			CBallot(b.seqno, b.proposer_id + 1) 
		else 
			CBallot(b.seqno + 1, 0)
	}

  function method CBoundRequestSequence(s: seq<CRequest>, lengthBound: CUpperBound) : seq<CRequest> 
		requires (forall i :: i in s ==> CRequestIsValid(i))
		requires CUpperBoundIsValid(lengthBound)
		ensures 
      var lr := BoundRequestSequence(AbstractifySeq(s, AbstractifyCRequestToRequest), AbstractifyCUpperBoundToUpperBound(lengthBound)); 
      var cr := CBoundRequestSequence(s, lengthBound); 
      (forall i :: i in cr ==> CRequestIsValid(i)) 
      && (AbstractifySeq(cr, AbstractifyCRequestToRequest)) == (lr)
	{
		if lengthBound.CUpperBoundFinite? && 0 <= lengthBound.n && lengthBound.n < |s| then 
			s[ .. lengthBound.n] 
		else 
			s
	}

  function method CRequestsMatch(r1: CRequest, r2: CRequest) : bool 
		requires CRequestIsValid(r1)
		requires CRequestIsValid(r2)
		ensures CRequestsMatch(r1, r2) == RequestsMatch(AbstractifyCRequestToRequest(r1), AbstractifyCRequestToRequest(r2))
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
		ensures CRequestSatisfiedBy(r1, r2) == RequestSatisfiedBy(AbstractifyCRequestToRequest(r1), AbstractifyCRequestToRequest(r2))
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
    ensures (forall i :: i in CRemoveAllSatisfiedRequestsInSequence(s, r) ==> i.CRequest? && CRequestIsValid(i))
    ensures AbstractifySeq(CRemoveAllSatisfiedRequestsInSequence(s, r), AbstractifyCRequestToRequest) == RemoveAllSatisfiedRequestsInSequence(AbstractifySeq(s, AbstractifyCRequestToRequest), AbstractifyCRequestToRequest(r))
		// ensures CRemoveAllSatisfiedRequestsInSequence(s, r) == RemoveAllSatisfiedRequestsInSequence(AbstractifySeq(s, AbstractifyCRequestToRequest), AbstractifyCRequestToRequest(r))
	{
		if |s| == 0 then 
			[] 
		else 
			if CRequestSatisfiedBy(s[0], r) then 
        CRemoveAllSatisfiedRequestsInSequence(s[1..], r)
				// CRemoveAllSatisfiedRequestsInSequence(s[1 : ], r) 
			else 
        [s[0]] + CRemoveAllSatisfiedRequestsInSequence(s[1..], r)
				// [s[0]] + CRemoveAllSatisfiedRequestsInSequence(s[1 : ], r)
	}

	function method CElectionStateInit(c: CReplicaConstants) : CElectionState 
		requires CReplicaConstantsIsValid(c)
		requires |c.all.config.replica_ids| > 0
		ensures var es := CElectionStateInit(c); CElectionStateIsValid(es) && ElectionStateInit(AbstractifyCElectionStateToElectionState(es), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := c; 		
		var t2 := CBallot(1, 0); 		
		var t3 := {}; 		
		var t4 := 0; 		
		var t5 := c.all.params.baseline_view_timeout_period; 		
		var t6 := []; 		
		var t7 := []; 		
		CElectionState(t1, t2, t3, t4, t5, t6, t7)
	}

  function method CElectionStateProcessHeartbeat(es: CElectionState, p: CPacket, clock: int) : CElectionState 
		requires CElectionStateIsValid(es)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_Heartbeat?
		ensures var es' := CElectionStateProcessHeartbeat(es, p, clock); CElectionStateIsValid(es') && ElectionStateProcessHeartbeat(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCPacketToRslPacket(p), clock)
	{
		var t1 := if p.src !in es.constants.all.config.replica_ids then var t1 := es; t1 else var t1 := var sender_index := CGetReplicaIndex(p.src, es.constants.all.config); var t1 := if p.msg.bal_heartbeat == es.current_view && p.msg.suspicious then var t1 := es.(current_view_suspectors := es.current_view_suspectors + {sender_index}); t1 else var t1 := if CBalLt(es.current_view, p.msg.bal_heartbeat) then var t1 := var new_epoch_length := UpperBoundedAdditionImpl(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val); var t1 := es.(current_view := p.msg.bal_heartbeat, current_view_suspectors := if p.msg.suspicious then {sender_index} else {}, epoch_length := new_epoch_length, epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), requests_received_this_epoch := []); t1; t1 else var t1 := es; t1; t1; t1; t1; 		
		t1
	}

	function method CElectionStateCheckForViewTimeout(es: CElectionState, clock: int) : CElectionState 
		requires CElectionStateIsValid(es)
		ensures var es' := CElectionStateCheckForViewTimeout(es, clock); CElectionStateIsValid(es') && ElectionStateCheckForViewTimeout(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), clock)
	{
		var t1 := if clock < es.epoch_end_time then var t1 := es; t1 else var t1 := if |es.requests_received_prev_epochs| == 0 then var t1 := var new_epoch_length := es.constants.all.params.baseline_view_timeout_period; var t1 := es.(epoch_length := new_epoch_length, epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := es.requests_received_this_epoch, requests_received_this_epoch := []); t1; t1 else var t1 := es.(current_view_suspectors := es.current_view_suspectors + {es.constants.my_index}, epoch_end_time := UpperBoundedAdditionImpl(clock, es.epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), requests_received_this_epoch := []); t1; t1; 		
		t1
	}

  function method CElectionStateCheckForQuorumOfViewSuspicions(es: CElectionState, clock: int) : CElectionState 
		requires CElectionStateIsValid(es)
		ensures var es' := CElectionStateCheckForQuorumOfViewSuspicions(es, clock); CElectionStateIsValid(es') && ElectionStateCheckForQuorumOfViewSuspicions(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), clock)
	{
		var t1 := if |es.current_view_suspectors| < CMinQuorumSize(es.constants.all.config) || 
      // [Printer for ... hasn't been implemented.] 
      !CLtUpperBound(es.current_view.seqno, es.constants.all.params.max_integer_val)
      then var t1 := es; t1 else var t1 := var new_epoch_length := UpperBoundedAdditionImpl(es.epoch_length, es.epoch_length, es.constants.all.params.max_integer_val); var t1 := es.(current_view := CComputeSuccessorView(es.current_view, es.constants.all), current_view_suspectors := {}, epoch_length := new_epoch_length, epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, es.constants.all.params.max_integer_val), requests_received_prev_epochs := CBoundRequestSequence(es.requests_received_prev_epochs + es.requests_received_this_epoch, es.constants.all.params.max_integer_val), requests_received_this_epoch := []); t1; t1; 		
		t1
	}


	function method CElectionStateReflectReceivedRequest(es: CElectionState, req: CRequest) : CElectionState 
		requires CElectionStateIsValid(es)
		requires CRequestIsValid(req)
		ensures var es' := CElectionStateReflectReceivedRequest(es, req); CElectionStateIsValid(es') && ElectionStateReflectReceivedRequest(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCRequestToRequest(req))
	{
		var t1 := if (exists earlier_req :: earlier_req in es.requests_received_prev_epochs && CRequestsMatch(earlier_req, req)) then var t1 := es; t1 else var t1 := if (exists earlier_req :: earlier_req in es.requests_received_this_epoch && CRequestsMatch(earlier_req, req)) then var t1 := es; t1 else var t1 := es.(requests_received_this_epoch := CBoundRequestSequence(es.requests_received_this_epoch + [req], es.constants.all.params.max_integer_val)); t1; t1; 		
		t1
	}

  function method CRemoveExecutedRequestBatch(reqs: seq<CRequest>, batch: CRequestBatch) : seq<CRequest> 
		requires (forall i :: i in reqs ==> CRequestIsValid(i))
		requires CRequestBatchIsValid(batch)
		decreases |batch|

    ensures (forall i :: i in CRemoveExecutedRequestBatch(reqs, batch) ==> i.CRequest? && CRequestIsValid(i))
    ensures AbstractifySeq(CRemoveExecutedRequestBatch(reqs, batch), AbstractifyCRequestToRequest) == RemoveExecutedRequestBatch(AbstractifySeq(reqs, AbstractifyCRequestToRequest), AbstractifyCRequestBatchToRequestBatch(batch))
		// ensures CRemoveExecutedRequestBatch(reqs, batch) == RemoveExecutedRequestBatch(AbstractifySeq(reqs, AbstractifyCRequestToRequest), AbstractifyCRequestBatchToRequestBatch(batch))
	{
		if |batch| == 0 then 
			reqs 
		else 
			CRemoveExecutedRequestBatch(CRemoveAllSatisfiedRequestsInSequence(reqs, batch[0]), batch[1..])
	}

	function method CElectionStateReflectExecutedRequestBatch(es: CElectionState, batch: CRequestBatch) : CElectionState 
		requires CElectionStateIsValid(es)
		requires CRequestBatchIsValid(batch)
		ensures var es' := CElectionStateReflectExecutedRequestBatch(es, batch); CElectionStateIsValid(es') && ElectionStateReflectExecutedRequestBatch(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCRequestBatchToRequestBatch(batch))
	{
		var t1 := es.(requests_received_prev_epochs := CRemoveExecutedRequestBatch(es.requests_received_prev_epochs, batch), requests_received_this_epoch := CRemoveExecutedRequestBatch(es.requests_received_this_epoch, batch)); 		
		t1
	}

  //  function method {:opaque} CRemoveExecutedRequestBatch(
  //   reqs : seq<CRequest> ,
  //              batch : CRequestBatch) : seq<CRequest>
  //   decreases |batch|
  //   requires (forall i :: i in reqs ==> i.CRequest? && CRequestIsValid(i))
  //   requires CRequestBatchIsValid(batch)
  //   ensures var r' := CRemoveExecutedRequestBatch(reqs, batch); var r := RemoveExecutedRequestBatch(AbstractifySeq(reqs, AbstractifyCRequestToRequest), AbstractifyCRequestBatchToRequestBatch(batch)); (forall i :: i in r' ==> i.CRequest? && CRequestIsValid(i)) && r == AbstractifySeq(r', AbstractifyCRequestToRequest)
  // {
  //   if |batch| == 0
  //   then
  //     reqs
  //   else
  //     CRemoveExecutedRequestBatch(CRemoveAllSatisfiedRequestsInSequence(reqs, batch[0]), batch[1..])
  // }

  // function method {:opaque} CElectionStateReflectExecutedRequestBatch(
  //   es : CElectionState ,
  //   batch : CRequestBatch) : CElectionState
  //   requires CElectionStateIsValid(es)
  //   requires CRequestBatchIsValid(batch)
  //   ensures var es' := CElectionStateReflectExecutedRequestBatch(es, batch); CElectionStateIsValid(es') && ElectionStateReflectExecutedRequestBatch(AbstractifyCElectionStateToElectionState(es), AbstractifyCElectionStateToElectionState(es'), AbstractifyCRequestBatchToRequestBatch(batch))
  // {
  //   es.(
  //     requests_received_prev_epochs := CRemoveExecutedRequestBatch(es.requests_received_prev_epochs, batch),
  //                                                                  requests_received_this_epoch := CRemoveExecutedRequestBatch(es.requests_received_this_epoch, batch)
  //   )
  // }

  /************************** AutoMan Translation End ************************/

// datatype CElectionState = CElectionState(
//   constants:CReplicaConstants,

//   current_view:CBallot,

//   current_view_suspectors:set<uint64>,

//   epoch_end_time:uint64,

//   epoch_length:uint64,

//   requests_received_this_epoch:seq<CRequest>,

//   requests_received_prev_epochs:seq<CRequest>
//   )

//   // ghost cur_req_set:set<CRequestHeader>,
//   // ghost prev_req_set:set<CRequestHeader>

// function CElectionStateValid(s:CElectionState) : bool
// {
//   && CElectionStateIsAbstractable(s)
//   && CReplicaConstansValid(s.constants)
//   && CBallotValid(s.current_view)
//   && |s.current_view_suspectors| < 0x4000_0000_0000_0000
//   // && 0 <= s.epoch_end_time < 0xffff_ffff_ffff_ffff
//   // && 0 <= s.epoch_length < 0xffff_ffff_ffff_ffff
//   && |s.requests_received_this_epoch| < 0x8000_0000_0000_0000
//   && |s.requests_received_prev_epochs| < 0x8000_0000_0000_0000
//   && forall r :: r in s.requests_received_this_epoch ==> CRequestValid(r)
//   && forall r :: r in s.requests_received_prev_epochs ==> CRequestValid(r)
// }

// predicate CElectionStateIsAbstractable(election:CElectionState)
// {
//   && ReplicaConstantsStateIsAbstractable(election.constants)
//   && CBallotIsAbstractable(election.current_view)
//   // && SeqIsUnique(election.current_view_suspectors)
//   && CRequestsSeqIsAbstractable(election.requests_received_this_epoch)
//   && CRequestsSeqIsAbstractable(election.requests_received_prev_epochs)
// }

// function AbstractifyCElectionStateToElectionState(election:CElectionState) : ElectionState
//   requires CElectionStateIsAbstractable(election)
// {
//   ElectionState(AbstractifyReplicaConstantsStateToLReplicaConstants(election.constants),
//                 AbstractifyCBallotToBallot(election.current_view),
//                 set i | i in election.current_view_suspectors :: i as int,
//                 election.epoch_end_time as int,
//                 election.epoch_length as int,
//                 AbstractifyCRequestsSeqToRequestsSeq(election.requests_received_this_epoch), 
//                 AbstractifyCRequestsSeqToRequestsSeq(election.requests_received_prev_epochs))
// }

// // run-time check
// method CComputeSuccessorView(b:CBallot, c:CConstants) returns (b':CBallot)
// requires CConstantsVaild(c)
// requires CBallotValid(b)
// {
    
//     if b.proposer_id + 1 < |c.config.replica_ids| as uint64 {
//       b' := CBallot(b.seqno, b.proposer_id + 1);
//     }
//     else{ 
//       b' :=  CBallot(b.seqno + 1, 0);
//     }

//     print "increase ballot from ", b, " to ", b', "\n";
// }

// function method CBoundRequestSequence(s:seq<CRequest>, lengthBound:uint64) : (s':seq<CRequest>)
// requires |s| < 0x1_0000_0000_0000_0000
// {
//   // if |s| < 0x8000_0000_0000_0000 then
//     if 0 <= lengthBound < |s| as uint64 then
//       s[..lengthBound]
//     else 
//       s
//   // else
//   //   s
// }

// function method CRequestsMatch(r1:CRequest, r2:CRequest) : bool
// {
//   r1.client == r2.client && r1.seqno == r2.seqno
// }

// function method CRequestSatisfiedBy(r1:CRequest, r2:CRequest) : bool
// {
//   r1.client == r2.client && r1.seqno <= r2.seqno
// }

// // 递归改写为了loop
// method CRemoveAllSatisfiedRequestsInSequence(s:seq<CRequest>, r:CRequest) returns (s':seq<CRequest>)
// // requires 0 < |s| < 0xffff_ffff_ffff_ffff  
// // requires forall req :: req in s ==> CRequestValid(req)
// // requires CRequestValid(r)
// // ensures 0 < |s'| < 0xffff_ffff_ffff_ffff
// // ensures forall req :: req in s' ==> CRequestValid(req)  
// {
//   if |s| == 0 {
//     s' := [];
//   } 
//   else {
//     // 这里本来应该是uint64，先改成int吧，这样能verify过
//     var i:int := 0;
//     while i < |s|
//       // invariant forall r :: r in s' ==> r in s
//     {
//       if !CRequestSatisfiedBy(s[i], r){
//         s' := s' + [s[i]];
//       } else {
//         s' := s';
//       }
//       i := i + 1;
//     }
//   }
//   // if |s| == 0 then
//   //   []
//   // else if CRequestSatisfiedBy(s[0], r) then 
//   //   CRemoveAllSatisfiedRequestsInSequence(s[1..], r)
//   // else 
//   //   [s[0]] + CRemoveAllSatisfiedRequestsInSequence(s[1..], r)
// }

// method CElectionStateInit(constants:CReplicaConstants) returns (election:CElectionState)
// requires CReplicaConstansValid(constants)
// requires ReplicaConstantsStateIsAbstractable(constants)
//   // requires CPaxosConfigurationIsValid(constants.all.config)
//   ensures  CElectionStateIsAbstractable(election)
//   ensures  WellFormedLConfiguration(AbstractifyReplicaConstantsStateToLReplicaConstants(constants).all.config)
//   ensures  ElectionStateInit(AbstractifyCElectionStateToElectionState(election), AbstractifyReplicaConstantsStateToLReplicaConstants(constants))
//   ensures  CElectionStateValid(election)
// {
//   election := CElectionState(constants,
//                              CBallot(1, 0),
//                              {},
//                              0,
//                              constants.all.params.baseline_view_timeout_period,
//                              [],
//                              []);
// }

// // use some common library
// // impl/common/UpperBound.i.dfy
// method CElectionStateProcessHeartbeat(ces:CElectionState, p:CPacket, clock:uint64) returns (ces':CElectionState)
// requires CElectionStateValid(ces)
// requires p.msg.CMessage_Heartbeat?
// {
//   if p.src !in ces.constants.all.config.replica_ids {
//     ces' := ces;
//   } else {
//     var sender_index := CGetReplicaIndex(p.src, ces.constants.all.config);
//     if (p.msg.bal_heartbeat == ces.current_view && p.msg.suspicious){
//       // print "add1 ", sender_index, " to view suspector\n";
//       ces' := ces.(current_view_suspectors := ces.current_view_suspectors + {sender_index});
//     } else if (CBalLt(ces.current_view, p.msg.bal_heartbeat)) {
//       // print "add2 ", sender_index, " to view suspector\n";
//       var new_epoch_length := UpperBoundedAdditionImpl(ces.epoch_length, ces.epoch_length, ces.constants.all.params.max_integer_val);
//       ces' := ces.(
//         current_view := p.msg.bal_heartbeat,
//           current_view_suspectors := (if p.msg.suspicious then {sender_index} else {}),
//           epoch_length := new_epoch_length,
//           epoch_end_time := UpperBoundedAdditionImpl(clock, new_epoch_length, ces.constants.all.params.max_integer_val),
//           requests_received_prev_epochs := CBoundRequestSequence(ces.requests_received_prev_epochs + ces.requests_received_this_epoch, ces.constants.all.params.max_integer_val),
//           requests_received_this_epoch := []
//           );
//     } else {
//       ces' := ces;
//     }
//   }
// }

// method CElectionStateCheckForViewTimeout(ces:CElectionState, clock:uint64) returns (ces':CElectionState)
// requires CElectionStateValid(ces)
// {
//   if clock < ces.epoch_end_time {
//     ces' := ces;
//   } else if |ces.requests_received_prev_epochs| == 0 {
//     // print "reset timeout\n";
//     var cnewEpochLength := ces.constants.all.params.baseline_view_timeout_period;
//     ces' := ces.(epoch_length := cnewEpochLength,
//                  epoch_end_time := UpperBoundedAdditionImpl(clock, cnewEpochLength, ces.constants.all.params.max_integer_val),
//                  requests_received_prev_epochs := ces.requests_received_this_epoch,
//                  requests_received_this_epoch := []);
//   } else {
//     // print "add myself to view suspector\n";
//     ces' := ces.(current_view_suspectors :=ces.current_view_suspectors + {ces.constants.my_index},
//                  epoch_end_time := UpperBoundedAdditionImpl(clock, ces.epoch_length, ces.constants.all.params.max_integer_val),
//                  requests_received_prev_epochs := CBoundRequestSequence(ces.requests_received_prev_epochs + ces.requests_received_this_epoch, ces.constants.all.params.max_integer_val),
//                  requests_received_this_epoch := []);
//   }
// }

// method CElectionStateCheckForQuorumOfViewSuspicions(ces:CElectionState, clock:uint64) returns(ces':CElectionState)
// requires CElectionStateValid(ces)
// {
//   if |ces.current_view_suspectors| as uint64 < CMinQuorumSize(ces.constants.all.config) || !CLtUpperBound(ces.current_view.seqno, ces.constants.all.params.max_integer_val){
//     ces' := ces;
//   } else {
//     print "before: ", ces.current_view, "\n";
//     var cnewEpochLength := UpperBoundedAdditionImpl(ces.epoch_length, ces.epoch_length, ces.constants.all.params.max_integer_val);
//     var v := CComputeSuccessorView(ces.current_view, ces.constants.all);
//     ces' := ces.(
//             current_view := v,
//             current_view_suspectors := {},
//             epoch_length := cnewEpochLength,
//             epoch_end_time := UpperBoundedAdditionImpl(clock, cnewEpochLength, ces.constants.all.params.max_integer_val),
//             requests_received_prev_epochs := CBoundRequestSequence(ces.requests_received_prev_epochs + ces.requests_received_this_epoch, ces.constants.all.params.max_integer_val),
//             requests_received_this_epoch := []);
//     print "after: ", ces'.current_view, "\n";
//   }
//   // print "after: ", ces'.current_view, "\n";
// }

// // 翻译了exists 量词
// // 对应 protocol 里的 ElectionStateReflectReceivedRequest，包含exists 量词
// // 原本实现中更高效，借助了 cur_req_set 和 prev_req_set
// method CElectionStateReflectReceivedRequest(ces:CElectionState, creq:CRequest) returns (ces':CElectionState)
// requires CElectionStateValid(ces)
// {
//   // 这段是翻译了exists量词
//   // print "reflect request\n";
//   var find_earlier := false;
//   var i:int := 0;
//   var j:int := 0;
//   while i < |ces.requests_received_prev_epochs| 
//   {
//     if CRequestsMatch(ces.requests_received_prev_epochs[i], creq)
//     {
//       find_earlier := true;
//       break;
//     }
//     i := i + 1;
//   }

//   while j < |ces.requests_received_this_epoch|
//   {
//     if CRequestsMatch(ces.requests_received_this_epoch[j], creq)
//     {
//       find_earlier := true;
//       break;
//     }
//     j := j + 1;
//   }

//   if find_earlier {
//     ces' := ces;
//   } else {
//     ces' := ces.(requests_received_this_epoch := CBoundRequestSequence(ces.requests_received_this_epoch + [creq], ces.constants.all.params.max_integer_val));
//   }
// }

// method CRemoveExecutedRequestBatch(reqs:seq<CRequest>, batch:CRequestBatch) returns (reqs':seq<CRequest>)
//   decreases |batch|
// {
//   if |batch| == 0 {
//     reqs' := reqs;
//   } else {
//     var s := CRemoveAllSatisfiedRequestsInSequence(reqs, batch[0]);
//     reqs' := CRemoveExecutedRequestBatch(s, batch[1..]);
//   }
// }

// // ironfleet原本实现更高效，借助RemoveAllSatisfiedCRequestsInSequenceIter，把递归改为循环
// method CElectionStateReflectExecutedRequestBatch(ces:CElectionState, creqb:CRequestBatch) returns (ces':CElectionState)
// requires CElectionStateValid(ces)
// {
//   var s1 := CRemoveExecutedRequestBatch(ces.requests_received_prev_epochs, creqb);
//   var s2 := CRemoveExecutedRequestBatch(ces.requests_received_this_epoch, creqb);
//   ces' := ces.(requests_received_prev_epochs := s1,
//               requests_received_this_epoch := s2);
// }

} 

