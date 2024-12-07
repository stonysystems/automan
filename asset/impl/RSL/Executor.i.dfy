/**********************************************************************
AUTOMAN LOG

[Module] LiveRSL__Executor_i

[Action] LExecutorInit
Check passed

[Action] LExecutorGetDecision
Check passed

[Action] UpdateNewCache
Check passed

[Action] LExecutorExecute
Check passed

[Action] LExecutorProcessAppStateSupply
Check passed

[Action] LExecutorProcessAppStateRequest
Check passed

[Action] LExecutorProcessStartingPhase2
Check passed

[Action] LExecutorProcessRequest
Check passed
**********************************************************************/

include ""


module Impl_LiveRSL__Executor_i 
{

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
		app: CAppState, 
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
		&& 
		CAppStateIsValid(s.app) 
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
		&& 
		CAppStateIsAbstractable(s.app) 
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
		LExecutor(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCAppStateToAppState(s.app), s.ops_complete, AbstractifyCBallotToBallot(s.max_bal_reflected), AbstractifyCOutstandingOperationToOutstandingOperation(s.next_op_to_execute), AbstractifyCReplyCacheToReplyCache(s.reply_cache))
	}

	function method CExecutorInit(c: CReplicaConstants) : CExecutor 
		requires CReplicaConstantsIsValid(c)
		ensures var s := CExecutorInit(c); CExecutorIsValid(s) && LExecutorInit(AbstractifyCExecutorToLExecutor(s), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := 
			c; 		
		var t2 := 
			CAppInitialize(); 		
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

	function method CGetPacketsFromReplies(me: EndPoint, requests: seq<CRequest>, replies: seq<CReply>) : OutboundPackets 
		requires EndPointIsValid(me)
		requires (forall i :: i in requests ==> CRequestIsValid(i))
		requires (forall i :: i in replies ==> CReplyIsValid(i))
		requires |requests| == |replies|
		requires (forall r :: r in replies ==> r.CReply?)
		ensures var lr := GetPacketsFromReplies(AbstractifyEndPointToNodeIdentity(me), AbstractifySeq(requests, AbstractifyCRequestToRequest), AbstractifySeq(replies, AbstractifyCReplyToReply)); var cr := CGetPacketsFromReplies(me, requests, replies); OutboundPacketsIsValid(cr) && (AbstractifyOutboundCPacketsToSeqOfRslPackets(cr)) == (lr)
	{
		if |requests| == 0 then 
			[] 
		else 
			[CPacket(requests[0].client, me, CMessage_Reply(requests[0].seqno, replies[0].reply))] + CGetPacketsFromReplies(me, requests[1 .. ], replies[1 .. ])
	}

	function method CClientsInReplies(replies: seq<CReply>) : CReplyCache 
		requires (forall i :: i in replies ==> CReplyIsValid(i))
		ensures var lr := LClientsInReplies(AbstractifySeq(replies, AbstractifyCReplyToReply)); var cr := CClientsInReplies(replies); CReplyCacheIsValid(cr) && (AbstractifyCReplyCacheToReplyCache(cr)) == (lr)
	{
		if |replies| == 0 then 
			map[] 
		else 
			CClientsInReplies(replies[1 .. ])[replies[0].client := replies[0]]
	}

	function method CUpdateNewCache(c: CReplyCache, replies: seq<CReply>) : CReplyCache 
		requires CReplyCacheIsValid(c)
		requires (forall i :: i in replies ==> CReplyIsValid(i))
		ensures var c' := CUpdateNewCache(c, replies); CReplyCacheIsValid(c') && UpdateNewCache(AbstractifyCReplyCacheToReplyCache(c), AbstractifyCReplyCacheToReplyCache(c'), AbstractifySeq(replies, AbstractifyCReplyToReply))
	{
		var t1 := 
			var nc := 
				CClientsInReplies(replies); 			
			var t1 := 
				(map client | client in c.Keys + nc.Keys :: if client in c then c[client] else nc[client]); 			
			t1; 		
		t1
	}

	function method CExecutorExecute(s: CExecutor) : (CExecutor, OutboundPackets) 
		requires CExecutorIsValid(s)
		requires s.next_op_to_execute.COutstandingOpKnown?
		requires CtUpperBound(s.ops_complete, s.constants.all.params.max_integer_val)
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
								CGetPacketsFromReplies(s.constants.all.config.replica_ids[s.constants.my_index], batch, replies); 							
							(CExecutor(t1, t2, t3, t4, t5, t6), t7); 						
						(t1.1, t1.0); 					
					(t1.1, t1.0); 				
				(t1.1, t1.0); 			
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	function method CExecutorProcessAppStateSupply(s: CExecutor, inp: CPacket) : CExecutor 
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_AppStateSupply?
		requires inp.src in s.constants.all.config.replica_ids && inp.msg.opn_state_supply > s.ops_complete
		ensures var s' := CExecutorProcessAppStateSupply(s, inp); CExecutorIsValid(s') && LExecutorProcessAppStateSupply(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCPacketToRslPacket(inp))
	{
		var t1 := 
			var m := 
				inp.msg; 			
			var t1 := 
				s.(app := m.app_state, ops_complete := m.opn_state_supply, max_bal_reflected := m.bal_state_supply, next_op_to_execute := COutstandingOpUnknown(), reply_cache := m.reply_cache); 			
			t1; 		
		t1
	}

	function method CExecutorProcessAppStateRequest(s: CExecutor, inp: CPacket) : (CExecutor, OutboundPackets) 
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_AppStateRequest?
		ensures var (s', sequential_sent_packets) := CExecutorProcessAppStateRequest(s, inp); CExecutorIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LExecutorProcessAppStateRequest(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			var m := 
				inp.msg; 			
			var t1 := 
				if inp.src in s.constants.all.config.replica_ids && CBalLeq(s.max_bal_reflected, m.bal_state_req) && s.ops_complete >= m.opn_state_req && CReplicaConstantsValid(s.constants) then 
					var t1 := 
						s; 					
					var t2 := 
						[CPacket(inp.src, s.constants.all.config.replica_ids[s.constants.my_index], CMessage_AppStateSupply(s.max_bal_reflected, s.ops_complete, s.app, s.reply_cache))]; 					
					(t1, t2) 
				else 
					var t1 := 
						s; 					
					var t2 := 
						[]; 					
					(t1, t2); 			
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

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
					BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_AppStateRequest(inp.msg.bal_2, inp.msg.logTruncationPoint_2)); 				
				(t1, t2) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					[]; 				
				(t1, t2); 		
		(t1.1, t1.0)
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
						[CPacket(r.client, s.constants.all.config.replica_ids[s.constants.my_index], CMessage_Reply(r.seqno, r.reply))]; 					
					t1; 				
				t1 
			else 
				var t1 := 
					[]; 				
				t1; 		
		t1
	}
}
