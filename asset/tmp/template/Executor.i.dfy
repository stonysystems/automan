include "Configuration.i.dfy"
include "Environment.i.dfy"
include "Types.i.dfy"
include "Constants.i.dfy"
include "ToBeFilled.i.dfy"
include "StateMachine.i.dfy"
include "Broadcast.i.dfy"
include "ToBeFilled.i.dfy"

module Impl_LiveRSL__Executor_i {
 	import opened Impl_LiveRSL__Configuration_i
	import opened Impl_LiveRSL__Environment_i
	import opened Impl_LiveRSL__Types_i
	import opened Impl_LiveRSL__Constants_i
	import opened Impl_LiveRSL__Message_i
	import opened Impl_LiveRSL__StateMachine_i
	import opened Impl_LiveRSL__Broadcast_i
	import opened ToBeFilled
	import opened ToBeFilled
	import opened ToBeFilled
	import opened ToBeFilled
	import opened ToBeFilled

	datatype COutstandingOperation = 
	COutstandingOpKnown
	(
		v : CRequestBatch ,
		bal : CBallot
	)
	|
	COutstandingOpUnknown
	(
		
	)

	predicate COutstandingOperationIsValid(
		s : COutstandingOperation)
		
	{
		match s
			case COutstandingOpKnown(v, bal) => COutstandingOperationIsAbstractable(s) && CRequestBatchIsValid(s.v) && CBallotIsValid(s.bal)
			case COutstandingOpUnknown() => COutstandingOperationIsAbstractable(s)

	}

	predicate COutstandingOperationIsAbstractable(
		s : COutstandingOperation)
		
	{
		match s
			case COutstandingOpKnown(v, bal) => CRequestBatchIsAbstractable(s.v) && CBallotIsAbstractable(s.bal)
			case COutstandingOpUnknown() => true

	}

	function AbstractifyCOutstandingOperationToOutstandingOperation(
		s : COutstandingOperation) : OutstandingOperation
		requires COutstandingOperationIsAbstractable(s)
	{
		match s
			case COutstandingOpKnown(v, bal) => OutstandingOpKnown(AbstractifyCRequestBatchToRequestBatch(s.v), AbstractifyCBallotToBallot(s.bal))
			case COutstandingOpUnknown() => OutstandingOpUnknown()

	}

	datatype CExecutor = 
	CExecutor
	(
		constants : CReplicaConstants ,
		app : CAppState ,
		ops_complete : int ,
		max_bal_reflected : CBallot ,
		next_op_to_execute : COutstandingOperation ,
		reply_cache : CReplyCache
	)

	predicate CExecutorIsValid(
		s : CExecutor)
		
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

	predicate CExecutorIsAbstractable(
		s : CExecutor)
		
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

	function AbstractifyCExecutorToLExecutor(
		s : CExecutor) : LExecutor
		requires CExecutorIsAbstractable(s)
	{
		LExecutor(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCAppStateToAppState(s.app), s.ops_complete, AbstractifyCBallotToBallot(s.max_bal_reflected), AbstractifyCOutstandingOperationToOutstandingOperation(s.next_op_to_execute), AbstractifyCReplyCacheToReplyCache(s.reply_cache))
	}

	function method CExecutorInit(
		c : CReplicaConstants) : CExecutor
		requires CReplicaConstantsIsValid(c)
		ensures var s := CExecutorInit(c); CExecutorIsValid(s) && LExecutorInit(AbstractifyCExecutorToLExecutor(s), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		CExecutor(app := CAppInitialize(), constants := c, max_bal_reflected := CBallot(0, 0), next_op_to_execute := COutstandingOpUnknown(), ops_complete := 0, reply_cache := map[])
	}

	function method CExecutorGetDecision(
		s : CExecutor ,
		bal : CBallot ,
		opn : COperationNumber ,
		v : CRequestBatch) : CExecutor
		requires CExecutorIsValid(s)
		requires CBallotIsValid(bal)
		requires COperationNumberIsValid(opn)
		requires CRequestBatchIsValid(v)
		requires opn == s.ops_complete
		requires s.next_op_to_execute.COutstandingOpUnknown?
		ensures var s' := CExecutorGetDecision(s, bal, opn, v); CExecutorIsValid(s') && LExecutorGetDecision(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCBallotToBallot(bal), AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyCRequestBatchToRequestBatch(v))
	{
		s.(
			next_op_to_execute := COutstandingOpKnown(v, bal)
		)
	}

	function method CGetPacketsFromReplies(
		me : EndPoint ,
		requests : seq<CRequest> ,
		replies : seq<CReply>) : seq<CPacket>
		requires EndPointIsValid(me)
		requires (forall i :: i in requests ==> i.CRequest? && CRequestIsValid(i))
		requires (forall i :: i in replies ==> i.CReply? && CReplyIsValid(i))
		requires |requests| == |replies|
		requires forall r :: r in replies ==> r.CReply?
		ensures var r' := CGetPacketsFromReplies(me, requests, replies); var r := GetPacketsFromReplies(AbstractifyEndPointToNodeIdentity(me), AbstractifySeq(requests, AbstractifyCRequestToRequest), AbstractifySeq(replies, AbstractifyCReplyToReply)); (forall i :: i in r' ==> i.CPacket? && CPacketIsValid(i)) && (r) == (AbstractifySeq(r', AbstractifyCPacketToRslPacket))
		ensures forall p :: p in CGetPacketsFromReplies(me, requests, replies) ==> p.src == me && p.msg.CMessage_Reply?
	{
		if |requests| == 0
		then 
			[]
		else 
			[CPacket(requests[0].client, me, CMessage_Reply(requests[0].seqno, replies[0].reply))] + CGetPacketsFromReplies(me, requests[1..], replies[1..])
	}

	function method CClientsInReplies(
		replies : seq<CReply>) : CReplyCache
		requires (forall i :: i in replies ==> i.CReply? && CReplyIsValid(i))
		ensures var r' := CClientsInReplies(replies); var r := LClientsInReplies(AbstractifySeq(replies, AbstractifyCReplyToReply)); CReplyCacheIsValid(r') && (r) == (AbstractifyCReplyCacheToReplyCache(r'))
		ensures var m := CClientsInReplies(replies);  && (forall c :: c in m ==> m[c].client == c) && (forall c :: c in m ==> exists req_idx ::  && 0 <= req_idx < |replies| && replies[req_idx].client == c && m[c] == replies[req_idx])
	{
		if |replies| == 0
		then 
			map[]
		else 
			CClientsInReplies(replies[1..])[replies[0].client := replies[0]]
	}

	function method CUpdateNewCache(
		c : CReplyCache ,
		replies : seq<CReply>) : CReplyCache
		requires CReplyCacheIsValid(c)
		requires (forall i :: i in replies ==> i.CReply? && CReplyIsValid(i))
		ensures var c' := CUpdateNewCache(c, replies); CReplyCacheIsValid(c') && UpdateNewCache(AbstractifyCReplyCacheToReplyCache(c), AbstractifyCReplyCacheToReplyCache(c'), AbstractifySeq(replies, AbstractifyCReplyToReply))
	{
		var nc := CClientsInReplies(replies); 
		map client | client in c.Keys + nc.Keys :: (if client in c then c[client] else nc[client])
	}

	function method CExecutorExecute(
		s : CExecutor) : (CExecutor, COutboundPackets)
		requires CExecutorIsValid(s)
		requires s.next_op_to_execute.COutstandingOpKnown?
		requires CLtUpperBound(s.ops_complete, s.constants.all.params.max_integer_val)
		requires CReplicaConstantsValid(s.constants)
		ensures var (s', non_empty_sequential_sent_packets) := CExecutorExecute(s); CExecutorIsValid(s') && (forall i :: i in non_empty_sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LExecutorExecute(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(non_empty_sequential_sent_packets))
	{
		var batch := s.next_op_to_execute.v; 
		var temp := CHandleRequestBatch(s.app, batch); 
		var new_state := temp.0[|temp.0| - 1]; 
		var replies := temp.1; 
		var clients := CClientsInReplies(replies); 
		(
			s.(
				app := new_state,
				constants := s.constants,
				max_bal_reflected := (if CBalLeq(s.max_bal_reflected, s.next_op_to_execute.bal) then s.next_op_to_execute.bal else s.max_bal_reflected),
				next_op_to_execute := COutstandingOpUnknown(),
				ops_complete := s.ops_complete + 1,
				reply_cache := CUpdateNewCache(s.reply_cache, replies)
			),
			CGetPacketsFromReplies(s.constants.all.config.replica_ids[s.constants.my_index], batch, replies)
		)
	}

	function method CExecutorProcessAppStateSupply(
		s : CExecutor ,
		inp : CPacket) : CExecutor
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_AppStateSupply?
		requires inp.src in s.constants.all.config.replica_ids && inp.msg.opn_state_supply > s.ops_complete
		ensures var s' := CExecutorProcessAppStateSupply(s, inp); CExecutorIsValid(s') && LExecutorProcessAppStateSupply(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCPacketToRslPacket(inp))
	{
		var m := inp.msg; 
		s.(
			app := m.app_state,
			ops_complete := m.opn_state_supply,
			max_bal_reflected := m.bal_state_supply,
			next_op_to_execute := COutstandingOpUnknown(),
			reply_cache := m.reply_cache
		)
	}

	function method CExecutorProcessAppStateRequest(
		s : CExecutor ,
		inp : CPacket) : (CExecutor, COutboundPackets)
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_AppStateRequest?
		ensures var (s', sequential_sent_packets) := CExecutorProcessAppStateRequest(s, inp); CExecutorIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LExecutorProcessAppStateRequest(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var m := inp.msg; 
		if  && inp.src in s.constants.all.config.replica_ids && CBalLeq(s.max_bal_reflected, m.bal_state_req) && s.ops_complete >= m.opn_state_req && CReplicaConstantsValid(s.constants)
		then 
			(
				s,
				CPacket(inp.src, s.constants.all.config.replica_ids[s.constants.my_index], CMessage_AppStateSupply(s.max_bal_reflected, s.ops_complete, s.app, s.reply_cache))
			)
		else 
			(
				s,
				OutboundPacket(None())
			)
	}

	function method CExecutorProcessStartingPhase2(
		s : CExecutor ,
		inp : CPacket) : (CExecutor, CBroadcast)
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_StartingPhase2?
		ensures var (s', broadcast_sent_packets) := CExecutorProcessStartingPhase2(s, inp); CExecutorIsValid(s') && (forall i :: i in broadcast_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LExecutorProcessStartingPhase2(AbstractifyCExecutorToLExecutor(s), AbstractifyCExecutorToLExecutor(s'), AbstractifyCPacketToRslPacket(inp), AbstractifyCBroadcastToRlsPacketSeq(broadcast_sent_packets))
	{
		if inp.src in s.constants.all.config.replica_ids && inp.msg.logTruncationPoint_2 > s.ops_complete
		then 
			(
				s,
				BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_AppStateRequest(inp.msg.bal_2, inp.msg.logTruncationPoint_2))
			)
		else 
			(
				s,
				CBroadcastNop
			)
	}

	function method CExecutorProcessRequest(
		s : CExecutor ,
		inp : CPacket) : COutboundPackets
		requires CExecutorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_Request?
		requires inp.src in s.reply_cache
		requires s.reply_cache[inp.src].CReply?
		requires inp.msg.seqno_req <= s.reply_cache[inp.src].seqno
		ensures var sequential_sent_packets := CExecutorProcessRequest(s, inp); (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LExecutorProcessRequest(AbstractifyCExecutorToLExecutor(s), AbstractifyCPacketToRslPacket(inp), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		if inp.msg.seqno_req == s.reply_cache[inp.src].seqno && CReplicaConstantsValid(s.constants)
		then 
			var r := s.reply_cache[inp.src]; 
			CPacket(r.client, s.constants.all.config.replica_ids[s.constants.my_index], CMessage_Reply(r.seqno, r.reply))
		else 
			OutboundPacket(None())
	}
 
}
