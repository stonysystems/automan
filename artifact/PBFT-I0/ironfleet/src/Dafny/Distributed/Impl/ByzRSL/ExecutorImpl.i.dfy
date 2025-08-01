include "AppInterface.i.dfy"
include "../../Protocol/ByzRSL/Executor.i.dfy"
include "../../Protocol/ByzRSL/Message.i.dfy"
include "Broadcast.i.dfy"
include "CStateMachine.i.dfy"
include "../Common/Util.i.dfy"
  // include "../../Common/Native/IoLemmas.i.dfy"
include "../../Protocol/ByzRSL/StateMachine.i.dfy"

module LiveByzRSL__ExecutorModel_i {
  import opened Native__Io_s
    // import opened Native__IoLemmas_i
  import opened Native__NativeTypes_s
  import opened LiveByzRSL__AppInterface_i
  import opened LiveByzRSL__CMessage_i
//   import opened LiveRSL__CMessageRefinements_i
  import opened LiveByzRSL__CTypes_i
  import opened LiveByzRSL__CConfiguration_i
  import opened LiveByzRSL__Environment_i
  import opened LiveByzRSL__Executor_i
    // import opened LiveRSL__CExecutor_i
  import opened LiveByzRSL__Message_i
  import opened LiveByzRSL__PacketParsing_i
  import opened LiveByzRSL__ConstantsState_i
  import opened LiveByzRSL__StateMachine_i
  import opened LiveByzRSL__Types_i
  import opened Impl__LiveByzRSL__Broadcast_i
  import opened Common__NodeIdentity_i
  import opened Common__UdpClient_i
  import opened Common__UpperBound_s
  import opened Common__UpperBound_i
  import opened Common__Util_i
  import opened Concrete_NodeIdentity_i
  import opened Collections__Maps_i
  import opened Logic__Option_i
  import opened Environment_s
  import opened AppStateMachine_i
  import opened Temporal__Temporal_s
  import opened LiveByzRSL__CStateMachine_i
  import opened GenericRefinement_i

/************************** AutoMan Translation ************************/

	/** 9 + 0 */
	datatype COutstandingOperation = 
	COutstandingOpKnown(
		v: CRequestBatch, 
		bal: CBallot
	)
	 | 
	COutstandingOpUnknown(
	)

	/** 0 + 6 */
	predicate COutstandingOperationIsValid(s: COutstandingOperation) 
	{
		match s
		case COutstandingOpKnown(v, bal) => COutstandingOperationIsAbstractable(s) && CRequestBatchIsValid(s.v) && CBallotIsValid(s.bal)
		case COutstandingOpUnknown() => COutstandingOperationIsAbstractable(s)
	}

	/** 0 + 6 */
	predicate COutstandingOperationIsAbstractable(s: COutstandingOperation) 
	{
		match s
		case COutstandingOpKnown(v, bal) => CRequestBatchIsAbstractable(s.v) && CBallotIsAbstractable(s.bal)
		case COutstandingOpUnknown() => true
	}

	/** 0 + 7 */
	function AbstractifyCOutstandingOperationToOutstandingOperation(s: COutstandingOperation) : OutstandingOperation 
		requires COutstandingOperationIsAbstractable(s)
	{
		match s
		case COutstandingOpKnown(v, bal) => OutstandingOpKnown(AbstractifyCRequestBatchToRequestBatch(s.v), AbstractifyCBallotToBallot(s.bal))
		case COutstandingOpUnknown() => OutstandingOpUnknown()
	}

	/** 8 + 0 */
	datatype CExecutor = 
	CExecutor(
		constants: CReplicaConstants, 
		app: CAppState, 
		ops_complete: int, 
		max_bal_reflected: CBallot, 
		next_op_to_execute: COutstandingOperation, 
		reply_cache: CReplyCache
	)

	/** 0 + 13 */
	predicate CExecutorIsValid(s: CExecutor) 
	{
		CExecutorIsAbstractable(s) 
		&& 
		CReplicaConstantsIsValid(s.constants) 
		&& 
		CAppStateIsValid(s.app) 
		&& 
		CBallotIsValid(s.max_bal_reflected) 
		&& 
		COutstandingOperationIsValid(s.next_op_to_execute) 
		&& 
		CReplyCacheIsValid(s.reply_cache)
	}

	/** 0 + 12 */
	predicate CExecutorIsAbstractable(s: CExecutor) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		CAppStateIsAbstractable(s.app) 
		&& 
		CBallotIsAbstractable(s.max_bal_reflected) 
		&& 
		COutstandingOperationIsAbstractable(s.next_op_to_execute) 
		&& 
		CReplyCacheIsAbstractable(s.reply_cache)
	}

	/** 0 + 5 */
	function AbstractifyCExecutorToLExecutor(s: CExecutor) : LExecutor 
		requires CExecutorIsAbstractable(s)
	{
		LExecutor(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCAppStateToAppState(s.app), s.ops_complete, AbstractifyCBallotToBallot(s.max_bal_reflected), AbstractifyCOutstandingOperationToOutstandingOperation(s.next_op_to_execute), AbstractifyCReplyCacheToReplyCache(s.reply_cache))
	}

	/** 15 + 2 */
	function method CExecutorInit(c: CReplicaConstants) : CExecutor 
		requires CReplicaConstantsIsValid(c)
		ensures var s := CExecutorInit(c); CExecutorIsValid(s) && LExecutorInit(AbstractifyCExecutorToLExecutor(s), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := 
			c; 		
		var t2 := 
			CAppStateInit(); 		
		var t3 := 
			0; 		
		var t4 := 
			CBallot(0, 0); 		
		var t5 := 
			COutstandingOpUnknown(); 		
		var t6 := 
			map[]; 		
		CExecutor(t1, t2, t3, t4, t5, t6)
	}

	/** 6 + 7 */
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

	/** 7 + 10 + 3 */
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
			&& AbstractifySeq(cr, AbstractifyCPacketToRslPacket) == (lr)
	{
		if |requests| == 0 then 
			[] 
		else 
			[CPacket(requests[0].client, me, CMessage_Reply(requests[0].seqno, replies[0].reply))] + CGetPacketsFromReplies(me, requests[1 .. ], replies[1 .. ])
	}

	/** 10 + 10 + 2 */
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
		// lemma_ReplyCacheLen(r);/** Manually Added */
		r
	}

	/** 10 + 3 + 2 */
	function method CUpdateNewCache(c: CReplyCache, replies: seq<CReply>) : CReplyCache 
		requires CReplyCacheIsValid(c)
		requires forall i :: 0 <= i < |replies| ==> CReplyIsValid(replies[i])/** Manually Added */
		ensures var c' := CUpdateNewCache(c, replies); CReplyCacheIsValid(c') && UpdateNewCache(AbstractifyCReplyCacheToReplyCache(c), AbstractifyCReplyCacheToReplyCache(c'), AbstractifySeq(replies, AbstractifyCReplyToReply))
	{
		var t1 := 
			var nc := 
				CClientsInReplies(replies); 			
			var t1 := 
				(map client | client in c.Keys + nc.Keys :: if client in c then c[client] else nc[client]); 			
			t1; 		
			/** Manually Added */
			assert CReplyCacheIsValid(t1);
			assert UpdateNewCache(AbstractifyCReplyCacheToReplyCache(c), AbstractifyCReplyCacheToReplyCache(t1), AbstractifySeq(replies, AbstractifyCReplyToReply));
		t1
	}

	/** 41 + 5 + 1 */
	function method CExecutorExecute(s: CExecutor) : (CExecutor, OutboundPackets) 
		requires CExecutorIsValid(s)
		requires s.next_op_to_execute.COutstandingOpKnown?
		requires CLtUpperBound(s.ops_complete, s.constants.all.params.max_integer_val)
		requires CReplicaConstantsValid(s.constants)
		ensures var (s', non_empty_sequential_sent_packets) := CExecutorExecute(s); CExecutorIsValid(s') && OutboundPacketsIsValid(non_empty_sequential_sent_packets) && LExecutorExecute(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(non_empty_sequential_sent_packets))
	{
		var t1 := 
			var batch := 
				s.next_op_to_execute.v; 			
			var t1 := 
				var temp := 
					CHandleRequestBatch(s.app, batch); 				
				var t1 := 
					var new_state := 
						temp.0[|temp.0| - 1]; 					
					var t1 := 
						var replies := 
							temp.1; 						
						var t1 := 
							var clients := 
								CClientsInReplies(replies); 							
							var t1 := 
								s.constants; 							
							var t2 := 
								new_state; 							
							var t3 := 
								s.ops_complete + 1; 							
							var t4 := 
								if CBalLeq(s.max_bal_reflected, s.next_op_to_execute.bal) then 
									s.next_op_to_execute.bal 
								else 
									s.max_bal_reflected; 							
							var t5 := 
								COutstandingOpUnknown(); 							
							var t6 := 
								CUpdateNewCache(s.reply_cache, replies); 							
							var t7 := 
								PacketSequence(CGetPacketsFromReplies(s.constants.all.config.replica_ids[s.constants.my_index], batch, replies)); 							
							(CExecutor(t1, t2, t3, t4, t5, t6), t7); 					
						(t1.0, t1.1); 					
					(t1.1, t1.0); 				
				(t1.1, t1.0); 			
			(t1.1, t1.0); 		
		// lemma_ReplyCacheLen(t1.1.reply_cache);	/** Manually Added */
		(t1.1, t1.0)
	}

	/** 16 + 4 */
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
					Broadcast(CBroadcastNop);		
				(t1, t2) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					Broadcast(CBroadcastNop); 				
				(t1, t2); 		
		(t1.0, t1.1)
	}

	/** 16 + 7 */
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
		t1
	}

/************************** AutoMan Translation End ************************/

//   lemma {:axiom} lemma_ReplyCacheLen(cache:CReplyCache)
//     ensures |cache| < max_reply_cache_size()

}
