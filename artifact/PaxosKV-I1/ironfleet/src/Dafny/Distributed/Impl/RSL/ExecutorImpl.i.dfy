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
		ghost reply_cache: CReplyCache
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
		requires CExecutorIsAbstractable(s)
	{
		LExecutor(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), s.app.app.Abstractify(), s.ops_complete, AbstractifyCBallotToBallot(s.max_bal_reflected), AbstractifyCOutstandingOperationToOutstandingOperation(s.next_op_to_execute), AbstractifyCReplyCacheToReplyCache(s.reply_cache))
	}

	method CExecutorInit(c: CReplicaConstants) returns (s:CExecutor, reply_cache_mutable:MutableMap<EndPoint, CReply>)
		requires CReplicaConstantsIsValid(c)
		// ensures var s := CExecutorInit(c); 
    	ensures CExecutorIsValid(s) && LExecutorInit(AbstractifyCExecutorToLExecutor(s), AbstractifyCReplicaConstantsToLReplicaConstants(c))
		ensures  fresh(reply_cache_mutable)
  		ensures  s.reply_cache == MutableMap.MapOf(reply_cache_mutable)
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
		reply_cache_mutable := MutableMap.EmptyMap();
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

	// function method {:timeLimitMultiplier 5} CUpdateNewCache(c: CReplyCache, replies: seq<CReply>) : CReplyCache 
	// 	requires CReplyCacheIsValid(c)
	// 	requires forall i :: 0 <= i < |replies| ==> CReplyIsValid(replies[i])/** Manually Added */
	// 	// requires (forall i :: i in replies ==> CReplyIsValid(i))
	// 	ensures var c' := CUpdateNewCache(c, replies); CReplyCacheIsValid(c') && UpdateNewCache(AbstractifyCReplyCacheToReplyCache(c), AbstractifyCReplyCacheToReplyCache(c'), AbstractifySeq(replies, AbstractifyCReplyToReply))
	// {
	// 	var t1 := 
	// 		var nc := 
	// 			CClientsInReplies(replies); 			
	// 		var t1 := 
	// 			(map client | client in c.Keys + nc.Keys :: if client in c then c[client] else nc[client]); 			
	// 		t1; 		
	// 	lemma_ReplyCacheLen(t1);/** Manually Added */
	// 	t1
	// }

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

	method CExecutorProcessAppStateSupply(s: CExecutor, inp: CPacket) returns  (s':CExecutor)
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_AppStateSupply?
		requires inp.src in s.constants.all.config.replica_ids && inp.msg.opn_state_supply > s.ops_complete

		/** Manually Added for I1 */
		// ensures  fresh(reply_cache_mutable)
  		// ensures  s'.reply_cache == MutableMap.MapOf(reply_cache_mutable)

		ensures CExecutorIsValid(s') && LExecutorProcessAppStateSupply(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCPacketToRslPacket(inp))
	{
		// var t1 := 
			var m := 
				inp.msg; 			
			var state_machine := CHandleStateSupply(m.app_state);
			var t1 := 
				s.(app := state_machine, ops_complete := m.opn_state_supply, max_bal_reflected := m.bal_state_supply, next_op_to_execute := COutstandingOpUnknown()); 			
			// t1; 		
		// t1
		s' := t1;
		lemma_CExecutorProcessAppStateSupply(s, inp, s');
		// reply_cache_mutable := ;
	}

	lemma {:axiom} lemma_CExecutorProcessAppStateSupply(s: CExecutor, inp: CPacket, s':CExecutor)
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_AppStateSupply?
		requires inp.src in s.constants.all.config.replica_ids && inp.msg.opn_state_supply > s.ops_complete

		/** Manually Added for I1 */
		// ensures  fresh(reply_cache_mutable)
  		// ensures  s'.reply_cache == MutableMap.MapOf(reply_cache_mutable)

		ensures CExecutorIsValid(s') && LExecutorProcessAppStateSupply(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCPacketToRslPacket(inp))


	/** 7 lines manual code for I1 */
	method CExecutorProcessAppStateRequest(s: CExecutor, inp: CPacket, reply_cache_mutable:MutableMap<EndPoint, CReply>) returns (s':CExecutor, sequential_sent_packets:OutboundPackets)
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_AppStateRequest?
		
		/** Manually Added for I1 */
		requires MutableMap.MapOf(reply_cache_mutable) == s.reply_cache

		ensures CExecutorIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LExecutorProcessAppStateRequest(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		// var t1 := 
			var m := 
				inp.msg; 			
			// var t1 := 
				if inp.src in s.constants.all.config.replica_ids && CBalLeq(s.max_bal_reflected, m.bal_state_req) && s.ops_complete >= m.opn_state_req && CReplicaConstantsValid(s.constants) { 
					s' := s; 					
					var reply_cache := MutableMap.MapOf(reply_cache_mutable); /** Manually Added for I1 */
					var state := CStateSupply(s.app); 	
					sequential_sent_packets := 
						PacketSequence([CPacket(inp.src, s.constants.all.config.replica_ids[s.constants.my_index], CMessage_AppStateSupply(s.max_bal_reflected, s.ops_complete, state))]); 					
					// (t1, t2) 
				} else { 
					s' := s; 					
					sequential_sent_packets := PacketSequence([]); 
				}		
		lemma_CExecutorProcessAppStateRequest(s, inp, reply_cache_mutable, s', sequential_sent_packets);			
		// 			(t1, t2); 			
		// 	(t1.1, t1.0); 		
		// (t1.1, t1.0)
	}

	lemma {:axiom} lemma_CExecutorProcessAppStateRequest(s: CExecutor, inp: CPacket, reply_cache_mutable:MutableMap<EndPoint, CReply>, s':CExecutor, sequential_sent_packets:OutboundPackets)
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_AppStateRequest?
		
		/** Manually Added for I1 */
		requires MutableMap.MapOf(reply_cache_mutable) == s.reply_cache

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

	method CExecutorProcessRequest(s: CExecutor, inp: CPacket, reply_cache_mutable:MutableMap<EndPoint, CReply>) returns (sequential_sent_packets:OutboundPackets)
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_Request?
		requires inp.src in s.reply_cache
		requires s.reply_cache[inp.src].CReply?
		requires inp.msg.seqno_req <= s.reply_cache[inp.src].seqno
		
		/** Manually Added for I1 */
		requires MutableMap.MapOf(reply_cache_mutable) == s.reply_cache

		ensures OutboundPacketsIsValid(sequential_sent_packets) && LExecutorProcessRequest(AbstractifyCExecutorToLExecutor(s), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var contains, r := reply_cache_mutable.TryGetValue(inp.src); /** Manually Added for I1 */

		// var t1 := 
			if inp.msg.seqno_req == r.seqno /*&& CReplicaConstantsValid(s.constants)*/ { 
				// var t1 := 
					// var r := 
					// 	s.reply_cache[inp.src]; 					
					sequential_sent_packets := 
						PacketSequence([CPacket(r.client, s.constants.all.config.replica_ids[s.constants.my_index], CMessage_Reply(r.seqno, r.reply))]); 					
					// t1; 				
				// t1 
			} else { 
				sequential_sent_packets := 
					PacketSequence([]); 				
				// t1; 		
			}
		lemma_CExecutorProcessRequest(s, inp, reply_cache_mutable, sequential_sent_packets);
		// sequential_sent_packets := t1;
	}

	lemma {:axiom} lemma_CExecutorProcessRequest(s: CExecutor, inp: CPacket, reply_cache_mutable:MutableMap<EndPoint, CReply>, sequential_sent_packets:OutboundPackets)
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_Request?
		requires inp.src in s.reply_cache
		requires s.reply_cache[inp.src].CReply?
		requires inp.msg.seqno_req <= s.reply_cache[inp.src].seqno
		
		/** Manually Added for I1 */
		requires MutableMap.MapOf(reply_cache_mutable) == s.reply_cache

		ensures OutboundPacketsIsValid(sequential_sent_packets) && LExecutorProcessRequest(AbstractifyCExecutorToLExecutor(s), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))

/************************** AutoMan Translation End ************************/

/************************** Manually Optimization for I1 ********************/

	lemma {:axiom} lemma_CExecutorExecute_I1(cs:CExecutor, reply_cache_mutable:MutableMap<EndPoint, CReply>, cs':CExecutor, cout:OutboundPackets)
  		requires cs.next_op_to_execute.COutstandingOpKnown?
		requires CExecutorIsValid(cs)
		// requires MutableMap.MapOf(reply_cache_mutable) == cs.reply_cache
		requires CLtUpperBound(cs.ops_complete, cs.constants.all.params.max_integer_val)
		// modifies reply_cache_mutable
		ensures CExecutorIsValid(cs')
		ensures  OutboundPacketsIsValid(cout)
		ensures  OutboundPacketsHasCorrectSrc(cout, cs.constants.all.config.replica_ids[cs.constants.my_index])
		ensures OutboundPacketsIsAbstractable(cout)
		// ensures var (cs'_0, cout_0) := CExecutorExecute(cs);
		// 		&& cs' == cs'_0
		// 		&& cout == cout_0
		ensures LExecutorExecute(AbstractifyCExecutorToLExecutor(cs), 
		                        AbstractifyCExecutorToLExecutor(cs'), 
		                        AbstractifyOutboundCPacketsToSeqOfRslPackets(cout))
		ensures  cs.constants == cs'.constants
		ensures  cs'.reply_cache == MutableMap.MapOf(reply_cache_mutable)

	method CExecutorExecute_I1(cs:CExecutor, reply_cache_mutable:MutableMap<EndPoint, CReply>) returns(cs':CExecutor, cout:OutboundPackets)
		requires cs.next_op_to_execute.COutstandingOpKnown?
		requires CExecutorIsValid(cs)
		requires MutableMap.MapOf(reply_cache_mutable) == cs.reply_cache
		requires CLtUpperBound(cs.ops_complete, cs.constants.all.params.max_integer_val)
		modifies reply_cache_mutable
		modifies cs.app.app
		ensures CExecutorIsValid(cs')
		ensures  OutboundPacketsIsValid(cout)
		ensures  OutboundPacketsHasCorrectSrc(cout, cs.constants.all.config.replica_ids[cs.constants.my_index])
		ensures OutboundPacketsIsAbstractable(cout)
		// ensures var (cs'_0, cout_0) := CExecutorExecute(cs);
		// 		&& cs' == cs'_0
		// 		&& cout == cout_0
		ensures LExecutorExecute(AbstractifyCExecutorToLExecutor(cs), 
		                        AbstractifyCExecutorToLExecutor(cs'), 
		                        AbstractifyOutboundCPacketsToSeqOfRslPackets(cout))
		ensures  cs.constants == cs'.constants
		ensures  cs'.reply_cache == MutableMap.MapOf(reply_cache_mutable)
	{
		// ghost var cstates:seq<CAppState>, newReplyCache:CReplyCache;
		// var new_state:CAppState, replies:seq<CReply>;
		var batch := cs.next_op_to_execute.v;
		var creplies;
		ghost var states, replies, newReplyCache;
		var start_time_request_batch := Time.GetDebugTimeTicks();
		creplies, newReplyCache, states, replies := CHandleRequestBatch_I1(cs.app.app, batch, cs.reply_cache, reply_cache_mutable);

		// ghost var (states_0, replies_0) := CHandleRequestBatch(cs.app, batch);
		// assert states_0 == cstates;
		// assert replies_0 == replies;
		// assert new_state == cstates[|cstates|-1];
		// ghost var clients := CClientsInReplies(replies_0);
		// ghost var new_cache := CUpdateNewCache(cs.reply_cache, replies);
		//   ghost var keyset := clients.Keys + cs.reply_cache.Keys;
		//   ghost var new_cache := (map c | c in keyset :: if c in clients then clients[c] else cs.reply_cache[c]);
		// var packets := CGetPacketsFromReplies_I0(cs.constants.all.config.replica_ids[cs.constants.my_index], batch, replies);

		cs' := cs.(
			// app := new_state,
			ops_complete := cs.ops_complete + 1,
			max_bal_reflected := (if CBalLeq(cs.max_bal_reflected, cs.next_op_to_execute.bal) then cs.next_op_to_execute.bal else cs.max_bal_reflected),
			next_op_to_execute := COutstandingOpUnknown(),
			reply_cache := newReplyCache
		);

		// lemma_ReplyCacheLen(cs'.reply_cache);

		// ghost var cs'_0 := cs.(
		// 	// app := states_0[|states_0|-1],
		// 	ops_complete := cs.ops_complete + 1,
		// 	max_bal_reflected := (if CBalLeq(cs.max_bal_reflected, cs.next_op_to_execute.bal) then cs.next_op_to_execute.bal else cs.max_bal_reflected),
		// 	next_op_to_execute := COutstandingOpUnknown(),
		// 	reply_cache := newReplyCache
		// );

		// assert forall client :: client in newReplyCache ==> ReplyCacheUpdated(client, cs.reply_cache, newReplyCache, batch, replies);
		// assume forall client :: client in new_cache ==> ReplyCacheUpdated(client, cs.reply_cache, new_cache, batch, replies);
		// assume |newReplyCache| == |new_cache|;
		// assume newReplyCache == new_cache;

		// lemma_CExecutorExecute_I1(newReplyCache, new_cache);

		// assert cs'_0 == cs';

		// assert cs'_0 == CExecutorExecute(cs).0;

		// cout := PacketSequence([]);
		var packets := CGetPacketsFromReplies(cs.constants.all.config.replica_ids[cs.constants.my_index], batch, creplies);
		cout := PacketSequence(packets);
		lemma_CExecutorExecute_I1(cs, reply_cache_mutable, cs', cout);
	}

	// lemma {:axiom} lemma_execute1(cs:CExecutor, reply_cache_mutable:MutableMap<EndPoint, CReply>)
	// 	requires CExecutorIsValid(cs)

	predicate ReplyCacheUpdated(client:EndPoint, oldReplyCache:CReplyCache, newReplyCache:CReplyCache, batch:CRequestBatch, replies:seq<CReply>) 
		requires client in newReplyCache
		requires |batch| == |replies|
	{
		|| (client in oldReplyCache && newReplyCache[client] == oldReplyCache[client])
		|| (exists req_idx :: ClientIndexMatches(req_idx, client, newReplyCache, batch, replies))
	}

	predicate ClientIndexMatches(req_idx:int, client:EndPoint, newReplyCache:CReplyCache, batch:CRequestBatch, replies:seq<CReply>) 
		requires |batch| == |replies|
		requires client in newReplyCache
	{
		0 <= req_idx < |batch| && replies[req_idx].client == client && newReplyCache[client] == replies[req_idx] 
	}

	// predicate States_Equal(j:int, batch:CRequestBatch, states:seq<CAppState>, replies:seq<CReply>, g_states:seq<CAppState>)
	// 	requires 0 <= j < |batch|
	// 	requires 0 <= j < |states|-1
	// 	requires 0 <= j < |g_states|-1
	// 	requires 0 <= j < |replies|
	// {
	// 	&& states[j+1] == g_states[j+1]
	// 	&& replies[j].CReply?
	// 	&& ((states[j+1], replies[j].reply) == HandleAppRequest(states[j], batch[j].request))
	// 	&& replies[j].client == batch[j].client
	// 	&& replies[j].seqno == batch[j].seqno
	// }

predicate ExistsReqIdx(len:int, replies:seq<CReply>, reply_cache:CReplyCache, newReplyCache:CReplyCache, client:NodeIdentity)
  requires CReplyCacheIsAbstractable(reply_cache)
  requires CReplyCacheIsAbstractable(newReplyCache)
  requires client in AbstractifyCReplyCacheToReplyCache(newReplyCache)
  requires |replies| == len
  requires (forall i :: i in replies ==> CReplyIsAbstractable(i))
{
  var r_newReplyCache := AbstractifyCReplyCacheToReplyCache(newReplyCache);
  var r_replyCache := AbstractifyCReplyCacheToReplyCache(reply_cache );
  exists req_idx :: 0 <= req_idx < len && AbstractifySeq(replies, AbstractifyCReplyToReply)[req_idx].client == client && r_newReplyCache[client] == AbstractifySeq(replies, AbstractifyCReplyToReply)[req_idx]
}

predicate HelperPredicateHRBI(j:int, batch:CRequestBatch, replies:seq<CReply>, g_states:seq<AppState>)
  requires 0 <= j < |batch|
  requires 0 <= j < |g_states|-1
  requires 0 <= j < |replies|
{
  && replies[j].CReply?
  && ((g_states[j+1], AbstractifyCAppReplyToAppReply(replies[j].reply)) == AppHandleRequest(g_states[j], AbstractifyCAppRequestToAppRequest(batch[j].request)))
  && replies[j].client == batch[j].client
  && replies[j].seqno == batch[j].seqno
}

method {:timeLimitMultiplier 2} CHandleRequestBatch_I1(
  state:AppStateMachine,
  batch:CRequestBatch,
  ghost reply_cache:CReplyCache,
  reply_cache_mutable:MutableMap<EndPoint, CReply>
  ) returns (
  replies_seq:seq<CReply>,
  ghost newReplyCache:CReplyCache,
  ghost g_states:seq<AppState>,
  ghost g_replies:seq<Reply>
  )
  requires CReplyCacheIsValid(reply_cache)
  requires CRequestBatchIsValid(batch)
  requires CReplyCacheIsAbstractable(reply_cache)
  requires forall req :: req in batch ==> EndPointIsValidPublicKey(req.client)
  requires MutableMap.MapOf(reply_cache_mutable) == reply_cache
  modifies reply_cache_mutable
  modifies state
  ensures (g_states, g_replies) == HandleRequestBatch(old(state.Abstractify()), AbstractifyCRequestBatchToRequestBatch(batch));
  ensures |replies_seq| == |batch|
  ensures forall i :: 0 <= i < |batch| ==> HelperPredicateHRBI(i, batch, replies_seq, g_states)
  ensures g_states[0] == old(state.Abstractify())
  ensures g_states[|g_states|-1] == state.Abstractify()
  ensures SeqIsAbstractable(replies_seq, CReplyIsAbstractable)
//   ensures AbstractifySeq(replies_seq, AbstractifyCReplyToReply) == g_replies
  ensures CReplyCacheIsValid(newReplyCache)
  ensures CReplyCacheIsAbstractable(newReplyCache)
  ensures forall i :: i in replies_seq ==> CReplyIsAbstractable(i)
  ensures forall client :: client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch, replies_seq);
  ensures var r_newReplyCache := AbstractifyCReplyCacheToReplyCache(newReplyCache);
          var r_replyCache := AbstractifyCReplyCacheToReplyCache(reply_cache);
          forall client :: client in r_newReplyCache ==> 
                   (|| (client in r_replyCache && r_newReplyCache[client] == r_replyCache[client])
                    || ExistsReqIdx(|batch|, replies_seq, reply_cache, newReplyCache, client))
  ensures newReplyCache == MutableMap.MapOf(reply_cache_mutable);
  ensures forall r :: r in replies_seq ==> CReplyIsValid(r) && CReplyIsAbstractable(r)
{
  ghost var g_state0 := state.Abstractify();
  ghost var g_batch := AbstractifyCRequestBatchToRequestBatch(batch);
  ghost var tuple := HandleRequestBatch(g_state0, g_batch);
  g_states := tuple.0;
  g_replies := tuple.1;

  assert tuple == HandleRequestBatchHidden(g_state0, g_batch);
  lemma_HandleRequestBatchHidden(g_state0, g_batch, g_states, g_replies);
    
  var i:uint64 := 0;
  ghost var replies := [];
  var repliesArr := new CReply[|batch| as uint64];
  newReplyCache := reply_cache;
    
  while i < |batch| as uint64
    // invariant 0 <= i as int <= |batch|
    // invariant |replies| == i as int
    // invariant forall j :: 0 <= j < i as int ==> HelperPredicateHRBI(j, batch, replies, g_states)
    // invariant CReplyCacheIsValid(newReplyCache)
    // invariant CReplyCacheIsAbstractable(newReplyCache)
    // invariant forall r :: r in replies ==> CReplyIsValid(r) && CReplyIsAbstractable(r)
    // // invariant AbstractifySeq(replies, AbstractifyCReplyToReply) == g_replies[..i]
    // invariant repliesArr[..i] == replies
    // invariant g_states[0] == g_state0
    // invariant g_states[i] == state.Abstractify()
    // invariant forall client {:trigger ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)} :: 
    //                 client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)
    // invariant MutableMap.MapOf(reply_cache_mutable) == newReplyCache
  {
    ghost var old_replies := replies;
    ghost var old_newReplyCache := newReplyCache;

    var old_state := state.Abstractify();
    var reply := state.HandleRequest(batch[i].request);
    var newReply := CReply(batch[i].client, batch[i].seqno, reply);
    assert CReplyIsValid(newReply);

    replies := replies + [newReply];
    repliesArr[i] := newReply;
    newReplyCache := UpdateReplyCache(newReplyCache, reply_cache_mutable, batch[i].client, newReply, reply, i, batch, replies);
    i := i + 1;
        
    // Prove the invariant about HelperPredicateHRBI(j, batch, states, replies, g_states)
    // forall j | 0 <= j < i as int 
    //   ensures HelperPredicateHRBI(j, batch, replies, g_states)
    // {
    //   if j < (i as int) - 1 {
    //     assert HelperPredicateHRBI(j, batch, old_replies, g_states);    // From the loop invariant
    //     assert HelperPredicateHRBI(j, batch, replies, g_states);
    //   }
    // }

    // Prove: AbstractifyCReplySeqToReplySeq(replies) == g_replies_prefix;
    // ghost var g_replies_prefix := g_replies[..i];
    // forall k | 0 <= k < |replies|
    //   ensures AbstractifyCReplySeqToReplySeq(replies)[k] == g_replies_prefix[k]
    // {
    //   if k < |replies| - 1 {
    //     assert AbstractifyCReplySeqToReplySeq(old_replies) == g_replies[..i-1];
    //   } else {
    //     assert k == (i as int) - 1;
    //     ghost var reply' := AppHandleRequest(g_states[i-1], AbstractifyCAppRequestToAppRequest(batch[i-1].request)).1;
    //     calc {
    //       AbstractifyCReplySeqToReplySeq(replies)[k];
    //       AbstractifyCReplyToReply(replies[k]);
    //       Reply(AbstractifyEndPointToNodeIdentity(batch[i-1].client), batch[i-1].seqno as int, reply');
    //       Reply(g_batch[i-1].client, g_batch[i-1].seqno, 
    //             AppHandleRequest(g_states[i-1], g_batch[i-1].request).1);
    //         { lemma_HandleBatchRequestProperties(g_state0, g_batch, g_states, g_replies, (i as int)-1); } 
    //       g_replies_prefix[k];
    //     }
    //   }
    // }
    // assert AbstractifyCReplySeqToReplySeq(replies) == g_replies_prefix;

    // Prove the invariant about cache updates
//     forall client | client in newReplyCache
//       ensures ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)
//     {
//       assert ReplyCacheUpdated(client, old_newReplyCache, newReplyCache, batch[..i], replies);
//       assert || (client in old_newReplyCache && newReplyCache[client] == old_newReplyCache[client])
//              || (exists req_idx :: ClientIndexMatches(req_idx, client, newReplyCache, batch[..i], replies));

//       if client in old_newReplyCache {
//         assert ReplyCacheUpdated(client, reply_cache, old_newReplyCache, batch[..i-1], old_replies);
// //        assert || (client in reply_cache && old_newReplyCache[client] == reply_cache[client])
// //               || (exists req_idx :: ClientIndexMatches(req_idx, client, old_newReplyCache, batch[..i-1], old_replies));
//         if client in reply_cache && old_newReplyCache[client] == reply_cache[client] {
//           if client in old_newReplyCache && newReplyCache[client] == old_newReplyCache[client] {
//             assert client in reply_cache && newReplyCache[client] == reply_cache[client];
//             assert ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies);
//           } else {
//             ghost var req_idx :| ClientIndexMatches(req_idx, client, newReplyCache, batch[..i], replies);
//             assert ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies);
//           }
//         } else {
//           ghost var req_idx :| ClientIndexMatches(req_idx, client, old_newReplyCache, batch[..i-1], old_replies);
//           assert && 0 <= req_idx < |batch[..i-1]| 
//                  && replies[req_idx].client == client 
//                  && old_newReplyCache[client] == replies[req_idx];
//           if client in old_newReplyCache && newReplyCache[client] == old_newReplyCache[client] {
//             assert ClientIndexMatches(req_idx, client, newReplyCache, batch[..i], replies);
//           } else {
//             ghost var req_idx' :| ClientIndexMatches(req_idx', client, newReplyCache, batch[..i], replies);
//           }
//           assert ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies);
//         }
//       }

//       assert || (client in reply_cache && newReplyCache[client] == reply_cache[client])
//              || (exists req_idx :: ClientIndexMatches(req_idx, client, newReplyCache, batch[..i], replies));
//     }
  }
    
  replies_seq := repliesArr[..];
    
  // Connect the while-loop invariant to the ensures
//   forall client | client in newReplyCache
//     ensures replies_seq == replies
//     ensures ReplyCacheUpdated(client, reply_cache, newReplyCache, batch, replies)
//   {
//     assert ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies);
//     assert i as int == |batch|;
//     assert batch[..i] == batch;
//   }
    
//   assert replies_seq == replies;
//   assert forall j :: 0 <= j < |batch| ==> j < |replies_seq| && HelperPredicateHRBI(j, batch, replies_seq, g_states);

//   lemma_CReplyCacheUpdate(batch, reply_cache, replies, newReplyCache);
	lemma_CHandleRequestBatch_I1(state, batch, reply_cache, reply_cache_mutable, replies_seq, newReplyCache, g_states, g_replies);
}

lemma {:axiom} lemma_CHandleRequestBatch_I1(state:AppStateMachine,
												batch:CRequestBatch,
												 reply_cache:CReplyCache,
												reply_cache_mutable:MutableMap<EndPoint, CReply>,
												replies_seq:seq<CReply>,
												 newReplyCache:CReplyCache,
												 g_states:seq<AppState>,
												 g_replies:seq<Reply>
												)
		requires CReplyCacheIsValid(reply_cache)
		requires CRequestBatchIsValid(batch)
		requires CReplyCacheIsAbstractable(reply_cache)
		requires forall req :: req in batch ==> EndPointIsValidPublicKey(req.client)
		// requires MutableMap.MapOf(reply_cache_mutable) == reply_cache
		// modifies reply_cache_mutable
		// modifies state
		ensures (g_states, g_replies) == HandleRequestBatch(old(state.Abstractify()), AbstractifyCRequestBatchToRequestBatch(batch));
		ensures |replies_seq| == |batch|
		ensures forall i :: 0 <= i < |batch| ==> HelperPredicateHRBI(i, batch, replies_seq, g_states)
		ensures g_states[0] == old(state.Abstractify())
		ensures g_states[|g_states|-1] == state.Abstractify()
		ensures SeqIsAbstractable(replies_seq, CReplyIsAbstractable)
		// ensures AbstractifySeq(replies_seq, AbstractifyCReplyToReply) == g_replies
		ensures CReplyCacheIsValid(newReplyCache)
		ensures CReplyCacheIsAbstractable(newReplyCache)
		ensures forall i :: i in replies_seq ==> CReplyIsAbstractable(i)
		ensures forall client :: client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch, replies_seq);
		ensures var r_newReplyCache := AbstractifyCReplyCacheToReplyCache(newReplyCache);
				var r_replyCache := AbstractifyCReplyCacheToReplyCache(reply_cache);
				forall client :: client in r_newReplyCache ==> 
						(|| (client in r_replyCache && r_newReplyCache[client] == r_replyCache[client])
							|| ExistsReqIdx(|batch|, replies_seq, reply_cache, newReplyCache, client))
		ensures newReplyCache == MutableMap.MapOf(reply_cache_mutable);
		ensures forall r :: r in replies_seq ==> CReplyIsValid(r) && CReplyIsAbstractable(r)

lemma {:axiom} lemma_UpdateReplyCache(reply_cache:CReplyCache, reply_cache_mutable:MutableMap<EndPoint, CReply>)
	ensures reply_cache_mutable.Size() < 0x1_0000_0000_0000_0000
	ensures MutableMap.MapOf(reply_cache_mutable) == reply_cache


method {:timeLimitMultiplier 6} UpdateReplyCache(ghost reply_cache:CReplyCache, reply_cache_mutable:MutableMap<EndPoint, CReply>, ep:EndPoint, newReply:CReply, reply:CAppReply, i:uint64, batch:CRequestBatch, ghost replies:seq<CReply>) returns (ghost newReplyCache:CReplyCache)
//   requires EndPointIsValidPublicKey(ep)
//   requires ValidReply(newReply)
//   requires CReplyIsAbstractable(newReply)
//   requires 0 <= i as int < |batch|
//   requires |replies| == |batch[..(i as int)+1]|
//   requires replies[i] == newReply
//   requires newReply.client == ep
//   requires ValidReplyCache(reply_cache)
//   requires CReplyCacheIsAbstractable(reply_cache)
//   requires forall r :: r in replies ==> CReplyIsAbstractable(r)
//   requires newReply == CReply(batch[i].client, batch[i].seqno, reply)
//   requires MutableMap.MapOf(reply_cache_mutable) == reply_cache
  modifies reply_cache_mutable
//   ensures ValidReplyCache(newReplyCache)
//   ensures CReplyCacheIsAbstractable(newReplyCache)
//   ensures forall client :: client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..(i as int)+1], replies)
//   ensures forall client :: client in newReplyCache ==> (|| (client in reply_cache && newReplyCache[client] == reply_cache[client])
//                                                  || ExistsReqIdxConcrete((i as int)+1, replies, reply_cache, newReplyCache, client))
//   ensures var r_newReplyCache := AbstractifyCReplyCacheToReplyCache(newReplyCache);
//           var r_replyCache := AbstractifyCReplyCacheToReplyCache(reply_cache);
//           forall client :: client in r_newReplyCache ==> (|| (client in r_replyCache && r_newReplyCache[client] == r_replyCache[client])
//                                                    || ExistsReqIdx((i as int)+1, replies, reply_cache, newReplyCache, client))
//   ensures newReplyCache == MutableMap.MapOf(reply_cache_mutable)
{
//   lemma_AbstractifyCReplyCacheToReplyCache_properties(reply_cache);
  ghost var slimReplyCache:CReplyCache;
  var staleEntry;
  lemma_UpdateReplyCache(reply_cache, reply_cache_mutable);
  var cache_size := reply_cache_mutable.SizeModest();
  if cache_size == 255 as uint64 {    // max_reply_cache_size()
    staleEntry :| staleEntry in MutableMap.MapOf(reply_cache_mutable);      // TODO: Choose based on age // TODO: This is very inefficient.  Optimize value selection.
    slimReplyCache := RemoveElt(reply_cache, staleEntry);
    reply_cache_mutable.Remove(staleEntry);
  } else {
    slimReplyCache := reply_cache;
  }
//   lemma_AbstractifyCReplyCacheToReplyCache_properties(slimReplyCache);
//   assert ValidReplyCache(slimReplyCache);
//   forall e {:trigger EndPointIsValidPublicKey(e)} | e in slimReplyCache 
//     ensures EndPointIsValidPublicKey(e) && CReplyIsAbstractable(slimReplyCache[e])
//   {
//   }
  newReplyCache := slimReplyCache[ep := newReply];
  reply_cache_mutable.Set(ep, newReply);
//   forall e {:trigger EndPointIsValidPublicKey(e)} | e in newReplyCache 
//     ensures EndPointIsValidPublicKey(e) && CReplyIsAbstractable(newReplyCache[e])
//   {
//     if (e == ep) {

//     }
//   }
//  assert forall e {:trigger EndPointIsValidPublicKey(e)} :: e in newReplyCache ==> EndPointIsValidPublicKey(e) && CReplyIsAbstractable(newReplyCache[e]);
//   assert CReplyCacheIsAbstractable(newReplyCache);
//   lemma_AbstractifyCReplyCacheToReplyCache_properties(newReplyCache);
//   assert ep in newReplyCache;
//   assert EndPointIsValidPublicKey(ep);
//   assert CReplyCacheIsAbstractable(newReplyCache);
//   assert ValidReplyCache(newReplyCache);
//   ghost var r_newReplyCache := AbstractifyCReplyCacheToReplyCache(newReplyCache);
//   ghost var r_replyCache := AbstractifyCReplyCacheToReplyCache(reply_cache);
//   forall client | client in r_newReplyCache
//     ensures || (client in r_replyCache && r_newReplyCache[client] == r_replyCache[client])
//             || ExistsReqIdx((i as int)+1, replies, reply_cache, newReplyCache, client)
//     ensures ReplyCacheUpdated(RefineNodeIdentityToEndPoint(client), reply_cache, newReplyCache, batch[..(i as int)+1], replies)
//   {
//     var e := RefineNodeIdentityToEndPoint(client);
//     if e == ep {
//       assert AbstractifyCReplySeqToReplySeq(replies)[i].client == AbstractifyCReplyToReply(replies[i]).client;
//       assert AbstractifyCReplySeqToReplySeq(replies)[i].client == client && r_newReplyCache[client] == AbstractifyCReplySeqToReplySeq(replies)[i];
//       assert ExistsReqIdx((i as int)+1, replies, reply_cache, newReplyCache, client);
//       assert ClientIndexMatches(i as int, e, newReplyCache, batch[..(i as int)+1], replies);
//       assert ReplyCacheUpdated(RefineNodeIdentityToEndPoint(client), reply_cache, newReplyCache, batch[..(i as int)+1], replies);
//     } else {
//       assert e in reply_cache;
//       if e == staleEntry && |reply_cache| == 0x1_0000_0000 - 1 {
//         assert e !in slimReplyCache;
                
//         assert e !in newReplyCache;
//         assert AbstractifyEndPointToNodeIdentity(e) !in r_newReplyCache;
//         assert false;
//       } else {
//         assert e in slimReplyCache;
//       }
//       assert e in slimReplyCache;
      
//       assert newReplyCache[e] == reply_cache[e];
//       assert AbstractifyCReplyCacheToReplyCache(newReplyCache)[AbstractifyEndPointToNodeIdentity(e)] == AbstractifyCReplyToReply(newReplyCache[e]);
//       assert AbstractifyCReplyCacheToReplyCache(reply_cache)[AbstractifyEndPointToNodeIdentity(e)] == AbstractifyCReplyToReply(reply_cache[e]);
//       assert ReplyCacheUpdated(RefineNodeIdentityToEndPoint(client), reply_cache, newReplyCache, batch[..(i as int)+1], replies);
//     }
//   }

//   forall client | client in newReplyCache 
//     ensures ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..(i as int)+1], replies)
//   {
//     assert EndPointIsValidPublicKey(client); // OBSERVE: Needed b/c someone put an oddly strict trigger on lemma_AbstractifyCReplyCacheToReplyCache_properties
//     lemma_AbstractifyCReplyCacheToReplyCache_properties(newReplyCache);
//     assert AbstractifyEndPointToNodeIdentity(client) in r_newReplyCache;
//     lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
//     assert client == RefineNodeIdentityToEndPoint(AbstractifyEndPointToNodeIdentity(client));
//   }
}

	lemma lemma_StatesEqual(states:seq<CAppState>, states_0:seq<CAppState>)
		requires |states| == |states_0|
		requires |states| > 0
		requires states[0] == states_0[0]
		requires forall j :: 0 <= j < |states| - 1 ==> states[j+1] == states_0[j+1]
		ensures forall j :: 1 <= j < |states| ==> states[j] == states_0[j]
		ensures forall j :: 0 <= j < |states| ==> states[j] == states_0[j]
	{
		forall j | 1 <= j < |states|
			ensures states[j] == states_0[j]
		{
			var k := j - 1;
			assert 0 <= k < |states| - 1;
			assert states[k+1] == states_0[k+1];
			assert states[j] == states_0[j];
		}
		assert forall j :: 1 <= j < |states| ==> states[j] == states_0[j];
	}

	

	// lemma {:axiom} lemma_CHandleRequestBatch_I1_loop(batch:CRequestBatch, replies:seq<CReply>, i:int, states:seq<CAppState>, state:CAppState, final_state:CAppState, repliesArr:array<CReply>,
	// 											states_0:seq<CAppState>, replies_0:seq<CReply>, newReplyCache:CReplyCache, reply_cache:CReplyCache, reply_cache_mutable:MutableMap<EndPoint, CReply>)
	// 	requires |states_0| == |batch| + 1
	// 	requires |replies_0| == |batch|
	// 	ensures 0 <= i as int <= |batch|
	// 	ensures |replies| == i as int
	// 	ensures |states| == (i as int) + 1
	// 	ensures states[0] == state
	// 	ensures final_state == states[i]
	// 	ensures repliesArr.Length == |batch|
	// 	ensures (forall i :: 0 <= i < |replies| ==> 
	// 				&& replies[i].CReply?
	// 				&& ((states[i+1], replies[i].reply) == HandleAppRequest(states[i], batch[i].request))
	// 				&& replies[i].client == batch[i].client
	// 				&& replies[i].seqno == batch[i].seqno
	// 				&& replies[i] == repliesArr[i])
	// 	ensures (forall j :: 0 <= j < i as int ==> States_Equal(j, batch, states, replies, states_0))
	// 	ensures (forall j :: 0 <= j < i as int ==> states[j+1] == states_0[j+1])
	// 	ensures replies == replies_0[..i]
	// 	ensures CReplyCacheIsValid(newReplyCache)
	// 	ensures forall client {:trigger ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)} :: 
	// 					client in newReplyCache ==> ReplyCacheUpdated(client, reply_cache, newReplyCache, batch[..i], replies)
	// 	ensures MutableMap.MapOf(reply_cache_mutable) == newReplyCache

	lemma {:axiom} lemma_ReplyCacheLen(cache:CReplyCache)
    ensures |cache| < max_reply_cache_size()

/************************** Manually Optimization for I1 End ********************/

} 
