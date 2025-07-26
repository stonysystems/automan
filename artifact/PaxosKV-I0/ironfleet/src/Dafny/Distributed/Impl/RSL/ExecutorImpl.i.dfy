include "AppInterface.i.dfy"
include "../../Protocol/RSL/Executor.i.dfy"
include "Broadcast.i.dfy"
include "CStateMachine.i.dfy"
include "../Common/Util.i.dfy"
include "../../Common/Native/IoLemmas.i.dfy"
include "../../Protocol/RSL/StateMachine.i.dfy"

module LiveRSL__ExecutorModel_i {
import opened Native__Io_s
import opened Native__IoLemmas_i
import opened Native__NativeTypes_s
import opened LiveRSL__AppInterface_i
import opened LiveRSL__CMessage_i
// import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__Environment_i
import opened LiveRSL__Executor_i
// import opened LiveRSL__ExecutorState_i
import opened LiveRSL__Message_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__ConstantsState_i
import opened LiveRSL__StateMachine_i
import opened LiveRSL__Types_i
import opened Impl__LiveRSL__Broadcast_i
import opened Common__NodeIdentity_i
import opened Common__NetClient_i
import opened Common__UpperBound_s
import opened Common__UpperBound_i
import opened Common__Util_i
import opened Concrete_NodeIdentity_i
import opened Collections__Maps_i
import opened Logic__Option_i
import opened Environment_s
import opened AppStateMachine_s
import opened Temporal__Temporal_s
import opened LiveRSL__CStateMachine_i
import opened GenericRefinement_i

/************************** AutoMan Translation ************************/
	datatype COutstandingOperation = 
	COutstandingOpKnown(
		v: CRequestBatch, 
		bal: CBallot
	)
	 | 
	COutstandingOpUnknown(
		
	)

	predicate COutstandingOperationIsValid(s: COutstandingOperation) 
	{
		match s
		case COutstandingOpKnown(v, bal) => COutstandingOperationIsAbstractable(s) && CRequestBatchIsValid(s.v) && CBallotIsValid(s.bal)
		case COutstandingOpUnknown() => COutstandingOperationIsAbstractable(s)

	}

	predicate COutstandingOperationIsAbstractable(s: COutstandingOperation) 
	{
		match s
		case COutstandingOpKnown(v, bal) => CRequestBatchIsAbstractable(s.v) && CBallotIsAbstractable(s.bal)
		case COutstandingOpUnknown() => true

	}

	function AbstractifyCOutstandingOperationToOutstandingOperation(s: COutstandingOperation) : OutstandingOperation 
		requires COutstandingOperationIsAbstractable(s)
	{
		match s
		case COutstandingOpKnown(v, bal) => OutstandingOpKnown(AbstractifyCRequestBatchToRequestBatch(s.v), AbstractifyCBallotToBallot(s.bal))
		case COutstandingOpUnknown() => OutstandingOpUnknown()

	}

	datatype CExecutor = 
	CExecutor(
		constants: CReplicaConstants, 
		app: CStateMachine, 
		ops_complete: int, 
		max_bal_reflected: CBallot, 
		next_op_to_execute: COutstandingOperation, 
		reply_cache: CReplyCache
	)

	predicate CExecutorIsValid(s: CExecutor) 
	{
		CExecutorIsAbstractable(s) 
		&& 
		CReplicaConstantsIsValid(s.constants) 
		// && 
		// CAppStateIsValid(s.app) 
		&& 
		CBallotIsValid(s.max_bal_reflected) 
		&& 
		COutstandingOperationIsValid(s.next_op_to_execute) 
		&& 
		CReplyCacheIsValid(s.reply_cache)
	}

	predicate CExecutorIsAbstractable(s: CExecutor) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		// && 
		// CAppStateIsAbstractable(s.app) 
		&& 
		CBallotIsAbstractable(s.max_bal_reflected) 
		&& 
		COutstandingOperationIsAbstractable(s.next_op_to_execute) 
		&& 
		CReplyCacheIsAbstractable(s.reply_cache)
	}

	function AbstractifyCExecutorToLExecutor(s: CExecutor) : LExecutor
    reads s.app.app 
		requires CExecutorIsAbstractable(s)
	{
		LExecutor(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), s.app.app.Abstractify(), s.ops_complete, AbstractifyCBallotToBallot(s.max_bal_reflected), AbstractifyCOutstandingOperationToOutstandingOperation(s.next_op_to_execute), AbstractifyCReplyCacheToReplyCache(s.reply_cache))
	}

	method CExecutorInit(c: CReplicaConstants) returns (s:CExecutor)
		requires CReplicaConstantsIsValid(c)
		// ensures var s := CExecutorInit(c); 
    ensures CExecutorIsValid(s) && LExecutorInit(AbstractifyCExecutorToLExecutor(s), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := 
			c; 		
		var t2 := 
			CStateMachineInit();		
		var t3 := 
			0; 		
		var t4 := 
			CBallot(0, 0); 		
		var t5 := 
			COutstandingOpUnknown(); 		
		var t6 := 
			map[]; 		
		s := CExecutor(t1, t2, t3, t4, t5, t6);
	}

	function method CExecutorGetDecision(s: CExecutor, bal: CBallot, opn: COperationNumber, v: CRequestBatch) : CExecutor 
		requires CExecutorIsValid(s)
		requires CBallotIsValid(bal)
		requires COperationNumberIsValid(opn)
		requires CRequestBatchIsValid(v)
		requires opn == s.ops_complete
		requires s.next_op_to_execute.COutstandingOpUnknown?
		ensures var s' := CExecutorGetDecision(s, bal, opn, v); CExecutorIsValid(s') && LExecutorGetDecision(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCBallotToBallot(bal), AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyCRequestBatchToRequestBatch(v))
	{
		var t1 := 
			s.(next_op_to_execute := COutstandingOpKnown(v, bal)); 		
		t1
	}

	function method CGetPacketsFromReplies(me: EndPoint, requests: seq<CRequest>, replies: seq<CReply>) : seq<CPacket> //OutboundPackets 
		requires EndPointIsValid(me)
		requires CRequestBatchIsValid(requests) /** Manually Added */
		requires (forall i :: i in requests ==> CRequestIsValid(i))
		requires (forall i :: i in replies ==> i.CReply? && CReplyIsValid(i))/** Manually Modified */
		requires |requests| == |replies|
		ensures (forall p :: p in CGetPacketsFromReplies(me, requests, replies) ==> p.src == me && p.msg.CMessage_Reply? && CPacketIsAbstractable(p))
		ensures 
			var lr := GetPacketsFromReplies(AbstractifyEndPointToNodeIdentity(me), AbstractifySeq(requests, AbstractifyCRequestToRequest), AbstractifySeq(replies, AbstractifyCReplyToReply)); 
			var cr := CGetPacketsFromReplies(me, requests, replies); 
			// (forall p :: p in cr ==> p.src == me && p.msg.CMessage_Reply? && CPacketIsAbstractable(p))
			// OutboundPacketsIsValid(cr) 
			&& AbstractifySeq(cr, AbstractifyCPacketToRslPacket) == (lr)
	{
		if |requests| == 0 then 
			[] 
		else 
			[CPacket(requests[0].client, me, CMessage_Reply(requests[0].seqno, replies[0].reply))] + CGetPacketsFromReplies(me, requests[1 .. ], replies[1 .. ])
	}

	function method CClientsInReplies(replies: seq<CReply>) : CReplyCache 
		requires (forall i :: i in replies ==> i.CReply? && CReplyIsValid(i))/** Manually Modified */
		ensures 
			var m := CClientsInReplies(replies); 
			(forall c :: c in m ==> m[c].client == c) 
			&& (forall c :: c in m ==> (exists req_idx :: 0 <= req_idx && req_idx < |replies| && replies[req_idx].client == c && m[c] == replies[req_idx]))
		ensures 
			var lr := LClientsInReplies(AbstractifySeq(replies, AbstractifyCReplyToReply)); 
			var cr := CClientsInReplies(replies); 
			CReplyCacheIsValid(cr) 
			&& (AbstractifyCReplyCacheToReplyCache(cr)) == (lr)
	{
		var r := 
		if |replies| == 0 then 
			map[] 
		else 
			CClientsInReplies(replies[1 .. ])[replies[0].client := replies[0]];
		lemma_ReplyCacheLen(r);/** Manually Added */
		r
	}

	function method {:timeLimitMultiplier 3} CUpdateNewCache(c: CReplyCache, replies: seq<CReply>) : CReplyCache 
		requires CReplyCacheIsValid(c)
		requires forall i :: 0 <= i < |replies| ==> CReplyIsValid(replies[i])/** Manually Added */
		// requires (forall i :: i in replies ==> CReplyIsValid(i))
		ensures var c' := CUpdateNewCache(c, replies); CReplyCacheIsValid(c') && UpdateNewCache(AbstractifyCReplyCacheToReplyCache(c), AbstractifyCReplyCacheToReplyCache(c'), AbstractifySeq(replies, AbstractifyCReplyToReply))
	{
		var t1 := 
			var nc := 
				CClientsInReplies(replies); 			
			var t1 := 
				(map client | client in c.Keys + nc.Keys :: if client in c then c[client] else nc[client]); 			
			t1; 		
		lemma_ReplyCacheLen(t1);/** Manually Added */
		lemma_CUpdateNewCache(c, replies, t1);
		t1
	}

	lemma {:axiom} lemma_CUpdateNewCache(c: CReplyCache, replies: seq<CReply>, c':CReplyCache)
		requires CReplyCacheIsValid(c)
		requires forall i :: 0 <= i < |replies| ==> CReplyIsValid(replies[i])/** Manually Added */
		ensures CReplyCacheIsValid(c') && UpdateNewCache(AbstractifyCReplyCacheToReplyCache(c), AbstractifyCReplyCacheToReplyCache(c'), AbstractifySeq(replies, AbstractifyCReplyToReply))

	// function method CExecutorExecute(s: CExecutor) : (CExecutor, OutboundPackets) 
	// 	requires CExecutorIsValid(s)
	// 	requires s.next_op_to_execute.COutstandingOpKnown?
	// 	requires CLtUpperBound(s.ops_complete, s.constants.all.params.max_integer_val)
	// 	requires CReplicaConstantsValid(s.constants)
	// 	ensures var (s', non_empty_sequential_sent_packets) := CExecutorExecute(s); CExecutorIsValid(s') && OutboundPacketsIsValid(non_empty_sequential_sent_packets) && LExecutorExecute(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(non_empty_sequential_sent_packets))
	// {
	// 	var t1 := 
	// 		var batch := 
	// 			s.next_op_to_execute.v; 			
	// 		var t1 := 
	// 			var temp := 
	// 				CHandleRequestBatch(s.app, batch); 				
	// 			var t1 := 
	// 				var new_state := 
	// 					temp.0[|temp.0| - 1]; 					
	// 				var t1 := 
	// 					var replies := 
	// 						temp.1; 						
	// 					var t1 := 
	// 						var clients := 
	// 							CClientsInReplies(replies); 							
	// 						var t1 := 
	// 							s.constants; 							
	// 						var t2 := 
	// 							new_state; 							
	// 						var t3 := 
	// 							s.ops_complete + 1; 							
	// 						var t4 := 
	// 							if CBalLeq(s.max_bal_reflected, s.next_op_to_execute.bal) then 
	// 								s.next_op_to_execute.bal 
	// 							else 
	// 								s.max_bal_reflected; 							
	// 						var t5 := 
	// 							COutstandingOpUnknown(); 							
	// 						var t6 := 
	// 							CUpdateNewCache(s.reply_cache, replies); 							
	// 						var t7 := 
	// 							PacketSequence(CGetPacketsFromReplies(s.constants.all.config.replica_ids[s.constants.my_index], batch, replies)); 							
	// 						(CExecutor(t1, t2, t3, t4, t5, t6), t7); 					
	// 					(t1.0, t1.1); 					
	// 				(t1.1, t1.0); 				
	// 			(t1.1, t1.0); 			
	// 		(t1.1, t1.0); 		
	// 	lemma_ReplyCacheLen(t1.1.reply_cache);	/** Manually Added */
	// 	(t1.1, t1.0)
	// }

  method CExecutorExecute(cs:CExecutor) returns(cs':CExecutor, cout:OutboundPackets)
    requires CExecutorIsValid(cs)
    requires cs.next_op_to_execute.COutstandingOpKnown?
    requires CLtUpperBound(cs.ops_complete, cs.constants.all.params.max_integer_val)
    requires CReplicaConstantsValid(cs.constants)
    ensures OutboundPacketsIsAbstractable(cout)
    ensures CExecutorIsValid(cs') && OutboundPacketsIsValid(cout) && LExecutorExecute(AbstractifyCExecutorToLExecutor(cs), AbstractifyCExecutorToLExecutor(cs'), AbstractifyOutboundCPacketsToSeqOfRslPackets(cout))
  {
    var batch := cs.next_op_to_execute.v;
    var replies := CHandleRequestBatch(cs.app, batch);

    // print "Execute req: ", batch[0].seqno, "\n";

    // translated from a exists
    var newReplyCache := cs.reply_cache;
    var i:uint64 := 0;
    while i as int < |batch|
    {
      if i as int < |replies|{
        newReplyCache := newReplyCache[replies[i].client := replies[i]];
      }
      i := i + 1;
    }

    cs' := cs.(
      ops_complete := cs.ops_complete + 1,
      max_bal_reflected := (if CBalLeq(cs.max_bal_reflected, cs.next_op_to_execute.bal) then cs.next_op_to_execute.bal else cs.max_bal_reflected),
      next_op_to_execute := COutstandingOpUnknown(),
      reply_cache := newReplyCache
    );
    var packets := CGetPacketsFromReplies(cs.constants.all.config.replica_ids[cs.constants.my_index], batch, replies);
    cout := PacketSequence(packets);
    lemma_CExecutorExecute(cs, cs', cout);
  }

  lemma {:axiom} lemma_CExecutorExecute(cs:CExecutor, cs':CExecutor, cout:OutboundPackets)
    requires CExecutorIsValid(cs)
    requires cs.next_op_to_execute.COutstandingOpKnown?
    requires CLtUpperBound(cs.ops_complete, cs.constants.all.params.max_integer_val)
    requires CReplicaConstantsValid(cs.constants)
    ensures OutboundPacketsIsAbstractable(cout)
    ensures CExecutorIsValid(cs') && OutboundPacketsIsValid(cout) && LExecutorExecute(AbstractifyCExecutorToLExecutor(cs), AbstractifyCExecutorToLExecutor(cs'), AbstractifyOutboundCPacketsToSeqOfRslPackets(cout))


	method CExecutorProcessAppStateSupply(s: CExecutor, inp: CPacket) returns (s':CExecutor) 
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_AppStateSupply?
		requires inp.src in s.constants.all.config.replica_ids && inp.msg.opn_state_supply > s.ops_complete
		// ensures var s' := CExecutorProcessAppStateSupply(s, inp); 
    ensures CExecutorIsValid(s') && LExecutorProcessAppStateSupply(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCPacketToRslPacket(inp))
	{
		// var t1 := 
			var m := 
				inp.msg; 			
      var state_machine := CHandleStateSupply(m.app_state);
			s' := 
				s.(app := state_machine, ops_complete := m.opn_state_supply, max_bal_reflected := m.bal_state_supply, next_op_to_execute := COutstandingOpUnknown()); 		
      lemma_CExecutorProcessAppStateSupply(s, inp, s');	
		// 	t1; 		
		// t1
	}

  lemma {:axiom} lemma_CExecutorProcessAppStateSupply(s: CExecutor, inp: CPacket, s':CExecutor)
    requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_AppStateSupply?
		requires inp.src in s.constants.all.config.replica_ids && inp.msg.opn_state_supply > s.ops_complete
    ensures CExecutorIsValid(s') && LExecutorProcessAppStateSupply(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCPacketToRslPacket(inp))

  method CExecutorProcessAppStateRequest(s: CExecutor, inp: CPacket) returns (s':CExecutor, sequential_sent_packets:OutboundPackets)
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_AppStateRequest?
		ensures OutboundPacketsIsAbstractable(sequential_sent_packets)
    ensures CExecutorIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LExecutorProcessAppStateRequest(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		// var t1 := 
			var m := 
				inp.msg; 			
			// var t1 := 
				if inp.src in s.constants.all.config.replica_ids && CBalLeq(s.max_bal_reflected, m.bal_state_req) && s.ops_complete >= m.opn_state_req && CReplicaConstantsValid(s.constants) { 
					s' := s;
          var state := CStateSupply(s.app); 					
					sequential_sent_packets := 
						PacketSequence([CPacket(inp.src, s.constants.all.config.replica_ids[s.constants.my_index], CMessage_AppStateSupply(s.max_bal_reflected, s.ops_complete, state))]); 					
					// (t1, t2) 
        } else { 
					s' := s; 					
					sequential_sent_packets := 
						PacketSequence([]);
        } 					
    lemma_CExecutorProcessAppStateRequest(s, inp, s', sequential_sent_packets);
		// 			(t1, t2); 			
		// 	(t1.1, t1.0); 		
		// (t1.1, t1.0)
	}

  lemma {:axiom} lemma_CExecutorProcessAppStateRequest(s: CExecutor, inp: CPacket, s':CExecutor, sequential_sent_packets:OutboundPackets)
    requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_AppStateRequest?
    ensures OutboundPacketsIsAbstractable(sequential_sent_packets)
    ensures CExecutorIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LExecutorProcessAppStateRequest(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))

	function method CExecutorProcessStartingPhase2(s: CExecutor, inp: CPacket) : (CExecutor, OutboundPackets) 
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_StartingPhase2?
		ensures var (s', broadcast_sent_packets) := CExecutorProcessStartingPhase2(s, inp); CExecutorIsValid(s') && OutboundPacketsIsValid(broadcast_sent_packets) && LExecutorProcessStartingPhase2(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(broadcast_sent_packets))
	{
		var t1 := 
			if inp.src in s.constants.all.config.replica_ids && inp.msg.logTruncationPoint_2 > s.ops_complete then 
				var t1 := 
					s; 				
				var t2 := 
					Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_AppStateRequest(inp.msg.bal_2, inp.msg.logTruncationPoint_2))); 				
				(t1, t2) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					Broadcast(CBroadcastNop); 				
				(t1, t2); 		
		(t1.0, t1.1)
	}

	function method CExecutorProcessRequest(s: CExecutor, inp: CPacket) : OutboundPackets 
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_Request?
		requires inp.src in s.reply_cache
		requires s.reply_cache[inp.src].CReply?
		requires inp.msg.seqno_req <= s.reply_cache[inp.src].seqno
		ensures var sequential_sent_packets := CExecutorProcessRequest(s, inp); OutboundPacketsIsValid(sequential_sent_packets) && LExecutorProcessRequest(AbstractifyCExecutorToLExecutor(s), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			if inp.msg.seqno_req == s.reply_cache[inp.src].seqno && CReplicaConstantsValid(s.constants) then 
				var t1 := 
					var r := 
						s.reply_cache[inp.src]; 					
					var t1 := 
						PacketSequence([CPacket(r.client, s.constants.all.config.replica_ids[s.constants.my_index], CMessage_Reply(r.seqno, r.reply))]); 					
					t1; 				
				t1 
			else 
				var t1 := 
					PacketSequence([]); 				
				t1; 		
      lemma_CExecutorProcessRequest(s, inp, t1);
		t1
	}

  lemma {:axiom} lemma_CExecutorProcessRequest(s: CExecutor, inp: CPacket, sequential_sent_packets:OutboundPackets)
    requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_Request?
		requires inp.src in s.reply_cache
		requires s.reply_cache[inp.src].CReply?
		requires inp.msg.seqno_req <= s.reply_cache[inp.src].seqno
    ensures OutboundPacketsIsAbstractable(sequential_sent_packets)
    ensures OutboundPacketsIsValid(sequential_sent_packets) && LExecutorProcessRequest(AbstractifyCExecutorToLExecutor(s), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))

  lemma {:axiom} lemma_ReplyCacheLen(cache:CReplyCache)
    ensures |cache| < max_reply_cache_size()

/************************** AutoMan Translation End ************************/
// datatype COutstandingOperation = COutstandingOpKnown(v:CRequestBatch,bal:CBallot) | COutstandingOpUnknown()

// predicate COutstandingOperationIsAbstractable(op:COutstandingOperation)
// {
//   || op.COutstandingOpUnknown?
//   || (CRequestBatchIsAbstractable(op.v) && CBallotIsAbstractable(op.bal))
// }

// function AbstractifyCOutstandingOperationToOutstandingOperation(op:COutstandingOperation):OutstandingOperation
//   requires COutstandingOperationIsAbstractable(op)
// {
//   match op
//     case COutstandingOpKnown(v,bal) => OutstandingOpKnown(AbstractifyCRequestBatchToRequestBatch(v),AbstractifyCBallotToBallot(bal))
//     case COutstandingOpUnknown => OutstandingOpUnknown()
// }

// // in protocol, the app is AppState, AppStateMachine is a class
// datatype ExecutorState = ExecutorState(
//   constants:CReplicaConstants,
//   app:CStateMachine,
//   ops_complete:COperationNumber,
//   max_bal_reflected:CBallot,
//   next_op_to_execute:COutstandingOperation,
//   reply_cache:CReplyCache)

// predicate ExecutorStateValid(cs:ExecutorState)
// {
//   && ExecutorState_IsAbstractable(cs)
//   && CReplicaConstansValid(cs.constants)
//   // && CBallotValid(cs.max_bal_reflected)
//   && cs.ops_complete < 0xffff_ffff_ffff_ffff
//   && (cs.next_op_to_execute.COutstandingOpKnown? ==> CRequestBatchValid(cs.next_op_to_execute.v))
//   && CReplyCacheValid(cs.reply_cache)
// }

// predicate ExecutorState_IsAbstractable(executor:ExecutorState)
// {
//   && ReplicaConstantsStateIsAbstractable(executor.constants)
//   && CBallotIsAbstractable(executor.max_bal_reflected)
//   && COutstandingOperationIsAbstractable(executor.next_op_to_execute)
//   && CReplyCacheIsAbstractable(executor.reply_cache)
// }

// function AbstractifyExecutorStateToLExecutor(executor:ExecutorState) : LExecutor
//   reads executor.app.app
//   requires ExecutorState_IsAbstractable(executor)
// {
//   LExecutor(
//     AbstractifyReplicaConstantsStateToLReplicaConstants(executor.constants),
//     executor.app.app.Abstractify(),
//     AbstractifyCOperationNumberToOperationNumber(executor.ops_complete),
//     AbstractifyCBallotToBallot(executor.max_bal_reflected),
//     AbstractifyCOutstandingOperationToOutstandingOperation(executor.next_op_to_execute),
//     AbstractifyCReplyCacheToReplyCache(executor.reply_cache))
// }

// predicate ExecutorState_CommonPreconditions(executor:ExecutorState)
// {
//   && ExecutorStateValid(executor)
//   && ExecutorState_IsAbstractable(executor)    // Can I have this too?
// }

// // // Same as x == y, but triggers extensional equality on fields and provides better error diagnostics
// // predicate Eq_ExecutorState(x:LExecutor, y:LExecutor)
// // {
// //   && x.constants == y.constants
// //   && x.app == y.app
// //   && x.ops_complete == y.ops_complete
// //   && x.next_op_to_execute == y.next_op_to_execute
// // }

// method CExecutorInit(ccons:CReplicaConstants) returns (cs:ExecutorState)
//   requires CReplicaConstansValid(ccons)
//   ensures  ExecutorStateValid(cs)
//   ensures  LExecutorInit(AbstractifyExecutorStateToLExecutor(cs), AbstractifyReplicaConstantsStateToLReplicaConstants(ccons))
//   ensures  cs.constants == ccons
// {
//     var app_state:=CStateMachineInit();
//     cs := ExecutorState(
//       ccons,
//       app_state,
//       0,
//       CBallot(0, 0),
//       COutstandingOpUnknown(),
//       map[]);
//     lemma_AbstractifyCReplyCacheToReplyCache_properties(cs.reply_cache);
// }

// method CExecutorGetDecision(cs:ExecutorState, cbal:CBallot, copn:COperationNumber, ca:CRequestBatch) returns(cs':ExecutorState)
// {
//   cs' := cs.(next_op_to_execute := COutstandingOpKnown(ca, cbal));
// }

// //原impl里有更高效的实现，用循环（下边注释的）
// method CGetPacketsFromReplies(me:EndPoint, requests:CRequestBatch, replies:seq<CReply>) returns (cout_seq:seq<CPacket>)
// requires |requests| == |replies|
// // requires forall r :: r in replies ==> r.CReply?
// // ensures forall p :: p in cout_seq ==> p.src == me && p.msg.CMessage_Reply?
// {
//   if |requests| == 0{
//     cout_seq := [];
//   }
//   else {
//       var p := CGetPacketsFromReplies(me, requests[1..], replies[1..]);
//       cout_seq := [CPacket(requests[0].client, me, CMessage_Reply(requests[0].seqno, replies[0].reply))]
//                   + p;
//   }
// }

// // method GetPacketsFromRepliesImpl(me:EndPoint, requests:CRequestBatch, replies:seq<CReply>) returns (cout_seq:seq<CPacket>)
// // {
// //   var i:uint64 := 0;
// //   ghost var cout := [];
// //   var coutArr := new CPacket[|replies| as uint64];

// //   while i < |replies| as uint64 
// //     invariant 0 <= i as int <= |replies|
// //     invariant |cout| == i as int
// //     invariant coutArr[..i] == cout
// //     invariant CPacketSeqIsAbstractable(cout)
// //     invariant forall p :: p in cout ==> p.src == me && p.msg.CMessage_Reply? && CPacketIsSendable(p)
// //     invariant forall j :: 0 <= j < i ==> cout[j] == CPacket(requests[j].client, me, CMessage_Reply(requests[j].seqno, replies[j].reply))
// //   {
// //     assert ValidRequest(requests[i]) && ValidReply(replies[i]);
// //     var cmsg := CMessage_Reply(requests[i].seqno, replies[i].reply);
// //     if PrintParams.ShouldPrintProgress() {
// //       print("Sending reply to client ");
// //       print(requests[i].client);
// //       print(" with sequence number ");
// //       print(requests[i].seqno);
// //       print("\n");
// //     }
// //     var cp := CPacket(requests[i].client, me, cmsg);
// //     cout := cout + [cp];
// //     coutArr[i] := cp;
// //     i := i + 1;
// //   }
// //   cout_seq := coutArr[..];
// // }

// // LExecutorExecute
// method CExecutorExecute(cs:ExecutorState) returns(cs':ExecutorState, cout:OutboundPackets)
// requires cs.next_op_to_execute.COutstandingOpKnown?
// requires ExecutorStateValid(cs)
// {
//   var batch := cs.next_op_to_execute.v;
//   var replies := CHandleRequestBatch(cs.app, batch);

//   // print "Execute req: ", batch[0].seqno, "\n";

//   // translated from a exists
//   var newReplyCache := cs.reply_cache;
//   var i:uint64 := 0;
//   while i as int < |batch|
//   {
//     if i as int < |replies|{
//       newReplyCache := newReplyCache[replies[i].client := replies[i]];
//     }
//     i := i + 1;
//   }

//   cs' := cs.(
//     ops_complete := cs.ops_complete + 1,
//     max_bal_reflected := (if CBalLeq(cs.max_bal_reflected, cs.next_op_to_execute.bal) then cs.next_op_to_execute.bal else cs.max_bal_reflected),
//     next_op_to_execute := COutstandingOpUnknown(),
//     reply_cache := newReplyCache
//   );
//   var packets := CGetPacketsFromReplies(cs.constants.all.config.replica_ids[cs.constants.my_index], batch, replies);
//   cout := PacketSequence(packets);
// }


// method CExecutorProcessAppStateSupply(cs:ExecutorState, cinp:CPacket) returns(cs':ExecutorState)
// requires cinp.msg.CMessage_AppStateSupply?
// {
//   var cm := cinp.msg;
//   var state_machine := CHandleStateSupply(cm.app_state);
//   cs' := cs.(app := state_machine,
//         ops_complete := cm.opn_state_supply,
//         max_bal_reflected := cm.bal_state_supply,
//         next_op_to_execute := COutstandingOpUnknown());
// }

// method CExecutorProcessAppStateRequest(cs:ExecutorState, cinp:CPacket) returns(cs':ExecutorState, cout:OutboundPackets)
// requires ExecutorStateValid(cs)
// requires cinp.msg.CMessage_AppStateRequest?
// {
//   var m := cinp.msg;
//   if cinp.src in cs.constants.all.config.replica_ids 
//       && CBalLeq(cs.max_bal_reflected, cinp.msg.bal_state_req)
//       && cs.ops_complete >= cinp.msg.opn_state_req
//       // && CReplicaConstansValid(cs.constants)
//   {
//     cs' := cs;
//     // 原impl里有个some，some是啥，好像是因为定义的OutboundPackets里有一个option
//     var state := CStateSupply(cs.app);
//     cout := OutboundPacket(Some(CPacket(cinp.src, cs.constants.all.config.replica_ids[cs.constants.my_index],
//                           CMessage_AppStateSupply(cs.max_bal_reflected, cs.ops_complete, state))));
//   } else {
//     cs' := cs;
//     cout := OutboundPacket(None());
//   }
// }

// method CExecutorProcessStartingPhase2(cs:ExecutorState, cinp:CPacket) returns(cs':ExecutorState, cout:CBroadcast)
// requires ExecutorStateValid(cs)
// requires cinp.msg.CMessage_StartingPhase2?
// {
//   if cinp.src in cs.constants.all.config.replica_ids && cinp.msg.logTruncationPoint_2 > cs.ops_complete {
//     cs' := cs;
//     var cmsg := CMessage_AppStateRequest(cinp.msg.bal_2, cinp.msg.logTruncationPoint_2);
//     cout := BuildBroadcastToEveryone(cs.constants.all.config, cs.constants.my_index, cmsg);
//   } else {
//     cs' := cs;
//     cout := CBroadcastNop;
//   }
// }

// // run-time check, map should check if the key is in the map
// method CExecutorProcessRequest(cs:ExecutorState, cinp:CPacket) returns (cout:OutboundPackets)
// requires ExecutorStateValid(cs)
// // requires cinp.msg.CMessage_Request?
// requires cinp.src in cs.reply_cache
// // requires cs.reply_cache[cinp.src].CReply?
// // requires cinp.msg.seqno <= cs.reply_cache[cinp.src].seqno
// {
//   // if(cinp.src in cs.reply_cache){
//   var r := cs.reply_cache[cinp.src];
//   cout := OutboundPacket(Some(CPacket(r.client, cs.constants.all.config.replica_ids[cs.constants.my_index],
//                         CMessage_Reply(r.seqno, r.reply))));

//     // print("Sending cached reply to client ");
//     // print(r.client);
//     // print(" with sequence number ");
//     // print(r.seqno);
//     // print("\n");
//   // }
// }

// // method CExecutorProcessRequest(cs:ExecutorState, cinp:CPacket) returns (cout:OutboundPackets)
// // requires cinp.msg.CMessage_Request?
// // {
// //   if CReplicaConstansValid(cs.constants){
// //     var r := cs.reply_cache[cinp.src];
// //     cout := OutboundPacket(Some(CPacket(r.client, cs.constants.all.config.replica_ids[cs.constants.my_index],
// //                           CMessage_Reply(r.seqno, r.reply))));
// //   } else {
// //     cout := OutboundPacket(None());
// //   }
// // }

} 
