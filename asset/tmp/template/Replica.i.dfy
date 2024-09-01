include "Configuration.i.dfy"
include "Environment.i.dfy"
include "Types.i.dfy"
include "ClockReading.i.dfy"
include "Constants.i.dfy"
include "Proposer.i.dfy"
include "Acceptor.i.dfy"
include "Learner.i.dfy"
include "Executor.i.dfy"

module Impl_LiveRSL__Replica_i {
 	import opened Impl_LiveRSL__Configuration_i
	import opened Impl_LiveRSL__Environment_i
	import opened Impl_LiveRSL__Types_i
	import opened Impl_LiveRSL__ClockReading_i
	import opened Impl_LiveRSL__Constants_i
	import opened Impl_LiveRSL__Proposer_i
	import opened Impl_LiveRSL__Acceptor_i
	import opened Impl_LiveRSL__Learner_i
	import opened Impl_LiveRSL__Executor_i
	import opened Impl_LiveRSL__Broadcast_i
	import opened Impl_LiveRSL__Message_i
	import opened ToBeFilled
	import opened ToBeFilled

	datatype CReplica = 
	CReplica
	(
		constants : CReplicaConstants ,
		nextHeartbeatTime : int ,
		proposer : CProposer ,
		acceptor : CAcceptor ,
		learner : CLearner ,
		executor : CExecutor
	)

	predicate CReplicaIsValid(
		s : CReplica)
		
	{
		CReplicaIsAbstractable(s)
		&&
		CReplicaConstantsIsValid(s.constants)
		&&
		CProposerIsValid(s.proposer)
		&&
		CAcceptorIsValid(s.acceptor)
		&&
		CLearnerIsValid(s.learner)
		&&
		CExecutorIsValid(s.executor)
	}

	predicate CReplicaIsAbstractable(
		s : CReplica)
		
	{
		CReplicaConstantsIsAbstractable(s.constants)
		&&
		CProposerIsAbstractable(s.proposer)
		&&
		CAcceptorIsAbstractable(s.acceptor)
		&&
		CLearnerIsAbstractable(s.learner)
		&&
		CExecutorIsAbstractable(s.executor)
	}

	function AbstractifyCReplicaToLReplica(
		s : CReplica) : LReplica
		requires CReplicaIsAbstractable(s)
	{
		LReplica(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), s.nextHeartbeatTime, AbstractifyCProposerToLProposer(s.proposer), AbstractifyCAcceptorToLAcceptor(s.acceptor), AbstractifyCLearnerToLLearner(s.learner), AbstractifyCExecutorToLExecutor(s.executor))
	}

	function method CReplicaInit(
		c : CReplicaConstants) : CReplica
		requires CWellFormedLConfiguration(c.all.config)
		requires CReplicaConstantsIsValid(c)
		ensures var r := CReplicaInit(c); CReplicaIsValid(r) && LReplicaInit(AbstractifyCReplicaToLReplica(r), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		CReplica(acceptor := CAcceptorInit(c), constants := c, executor := CExecutorInit(c), learner := CLearnerInit(c), nextHeartbeatTime := 0, proposer := CProposerInit(c))
	}

	function method CReplicaNextProcessInvalid(
		s : CReplica ,
		received_packet : CPacket) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Invalid?
		ensures var (s', non_empty_sequential_sent_packets) := CReplicaNextProcessInvalid(s, received_packet); CReplicaIsValid(s') && (forall i :: i in non_empty_sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextProcessInvalid(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(non_empty_sequential_sent_packets))
	{
		(
			s,
			PacketSequence([])
		)
	}

	function method CReplicaNextProcessRequest(
		s : CReplica ,
		received_packet : CPacket) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Request?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessRequest(s, received_packet); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextProcessRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		if  && received_packet.src in s.executor.reply_cache && s.executor.reply_cache[received_packet.src].CReply? && received_packet.msg.seqno_req <= s.executor.reply_cache[received_packet.src].seqno
		then 
			(
				s,
				CExecutorProcessRequest(s.executor, received_packet)
			)
		else 
			(
				s.(
					proposer := CProposerProcessRequest(s.proposer, received_packet)
				),
				OutboundPacket(None())
			)
	}

	function method CReplicaNextProcess1a(
		s : CReplica ,
		received_packet : CPacket) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_1a?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcess1a(s, received_packet); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextProcess1a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var (t0_0, t1_0) := CAcceptorProcess1a(s.acceptor, received_packet); 
		(
			s.(
				acceptor := t0_0
			),
			Broadcast(t1_0)
		)
	}

	function method CReplicaNextProcess1b(
		s : CReplica ,
		received_packet : CPacket) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_1b?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcess1b(s, received_packet); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextProcess1b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		if  && received_packet.src in s.proposer.constants.all.config.replica_ids && received_packet.msg.bal_1b == s.proposer.max_ballot_i_sent_1a && s.proposer.current_state == 1 && (forall other_packet :: other_packet in s.proposer.received_1b_packets ==> other_packet.src != received_packet.src)
		then 
			(
				s.(
					proposer := CProposerProcess1b(s.proposer, received_packet),
					acceptor := CAcceptorTruncateLog(s.acceptor, received_packet.msg.log_truncation_point)
				),
				OutboundPacket(None())
			)
		else 
			(
				s,
				OutboundPacket(None())
			)
	}

	function method CReplicaNextProcessStartingPhase2(
		s : CReplica ,
		received_packet : CPacket) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_StartingPhase2?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessStartingPhase2(s, received_packet); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextProcessStartingPhase2(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var (t0_0, t1_0) := CExecutorProcessStartingPhase2(s.executor, received_packet); 
		(
			s.(
				executor := t0_0
			),
			Broadcast(t1_0)
		)
	}

	function method CReplicaNextProcess2a(
		s : CReplica ,
		received_packet : CPacket) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_2a?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcess2a(s, received_packet); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextProcess2a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var m := received_packet.msg; 
		if  && received_packet.src in s.acceptor.constants.all.config.replica_ids && CBalLeq(s.acceptor.max_bal, m.bal_2a) && CLeqUpperBound(m.opn_2a, s.acceptor.constants.all.params.max_integer_val)
		then 
			var (t0_0, t1_0) := CAcceptorProcess2a(s.acceptor, received_packet); 
			(
				s.(
					acceptor := t0_0
				),
				Broadcast(t1_0)
			)
		else 
			(
				s,
				OutboundPacket(None())
			)
	}

	function method CReplicaNextProcess2b(
		s : CReplica ,
		received_packet : CPacket) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_2b?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcess2b(s, received_packet); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextProcess2b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var opn := received_packet.msg.opn_2b; 
		var op_learnable := s.executor.ops_complete < opn || (s.executor.ops_complete == opn && s.executor.next_op_to_execute.COutstandingOpUnknown?); 
		if op_learnable
		then 
			(
				s.(
					learner := CLearnerProcess2b(s.learner, received_packet)
				),
				OutboundPacket(None())
			)
		else 
			(
				s,
				OutboundPacket(None())
			)
	}

	function method CReplicaNextProcessReply(
		s : CReplica ,
		received_packet : CPacket) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Reply?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessReply(s, received_packet); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextProcessReply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		(
			s,
			OutboundPacket(None())
		)
	}

	function method CReplicaNextProcessAppStateSupply(
		s : CReplica ,
		received_packet : CPacket) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_AppStateSupply?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessAppStateSupply(s, received_packet); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextProcessAppStateSupply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		if received_packet.src in s.executor.constants.all.config.replica_ids && received_packet.msg.opn_state_supply > s.executor.ops_complete
		then 
			(
				s.(
					learner := CLearnerForgetOperationsBefore(s.learner, received_packet.msg.opn_state_supply),
					executor := CExecutorProcessAppStateSupply(s.executor, received_packet)
				),
				OutboundPacket(None())
			)
		else 
			(
				s,
				OutboundPacket(None())
			)
	}

	function method CReplicaNextProcessAppStateRequest(
		s : CReplica ,
		received_packet : CPacket) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_AppStateRequest?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessAppStateRequest(s, received_packet); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextProcessAppStateRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var (t0_0, t1_1) := CExecutorProcessAppStateRequest(s.executor, received_packet); 
		(
			s.(
				executor := t0_0
			),
			t1_1
		)
	}

	function method CReplicaNextProcessHeartbeat(
		s : CReplica ,
		received_packet : CPacket ,
		clock : int) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Heartbeat?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessHeartbeat(s, received_packet, clock); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextProcessHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), clock, AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		(
			s.(
				proposer := CProposerProcessHeartbeat(s.proposer, received_packet, clock),
				acceptor := CAcceptorProcessHeartbeat(s.acceptor, received_packet)
			),
			OutboundPacket(None())
		)
	}

	function method CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(
		s : CReplica) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var (t0_0, t1_0) := CProposerMaybeEnterNewViewAndSend1a(s.proposer); 
		(
			s.(
				proposer := t0_0
			),
			Broadcast(t1_0)
		)
	}

	function method CReplicaNextSpontaneousMaybeEnterPhase2(
		s : CReplica) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeEnterPhase2(s); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextSpontaneousMaybeEnterPhase2(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var (t0_0, t1_0) := CProposerMaybeEnterPhase2(s.proposer, s.acceptor.log_truncation_point); 
		(
			s.(
				proposer := t0_0
			),
			Broadcast(t1_0)
		)
	}

	function method CReplicaNextReadClockMaybeNominateValueAndSend2a(
		s : CReplica ,
		clock : CClockReading) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CClockReadingIsValid(clock)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockMaybeNominateValueAndSend2a(s, clock); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextReadClockMaybeNominateValueAndSend2a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var (t0_0, t1_0) := CProposerMaybeNominateValueAndSend2a(s.proposer, clock.t, s.acceptor.log_truncation_point); 
		(
			s.(
				proposer := t0_0
			),
			Broadcast(t1_0)
		)
	}

	function method CReplicaNextSpontaneousMaybeMakeDecision(
		s : CReplica) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeMakeDecision(s); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextSpontaneousMaybeMakeDecision(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var opn := s.executor.ops_complete; 
		if  && s.executor.next_op_to_execute.COutstandingOpUnknown? && opn in s.learner.unexecuted_learner_state && |s.learner.unexecuted_learner_state[opn].received_2b_message_senders| >= CMinQuorumSize(s.learner.constants.all.config)
		then 
			(
				s.(
					executor := CExecutorGetDecision(s.executor, s.learner.max_ballot_seen, opn, s.learner.unexecuted_learner_state[opn].candidate_learned_value)
				),
				OutboundPacket(None())
			)
		else 
			(
				s,
				OutboundPacket(None())
			)
	}

	function method CReplicaNextSpontaneousMaybeExecute(
		s : CReplica) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeExecute(s); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextSpontaneousMaybeExecute(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		if  && s.executor.next_op_to_execute.COutstandingOpKnown? && CLtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val) && CReplicaConstantsValid(s.executor.constants)
		then 
			var v := s.executor.next_op_to_execute.v; 
			var (t0_0, t1_1) := CExecutorExecute(s.executor); 
			(
				s.(
					proposer := CProposerResetViewTimerDueToExecution(s.proposer, v),
					learner := CLearnerForgetDecision(s.learner, s.executor.ops_complete),
					executor := t0_0
				),
				t1_1
			)
		else 
			(
				s,
				OutboundPacket(None())
			)
	}

	function method CReplicaNextReadClockMaybeSendHeartbeat(
		s : CReplica ,
		clock : CClockReading) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CClockReadingIsValid(clock)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockMaybeSendHeartbeat(s, clock); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextReadClockMaybeSendHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		if clock.t < s.nextHeartbeatTime
		then 
			(
				s,
				OutboundPacket(None())
			)
		else 
			(
				s.(
					nextHeartbeatTime := UpperBoundedAdditionImpl(clock.t, s.constants.all.params.heartbeat_period, s.constants.all.params.max_integer_val)
				),
				BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_Heartbeat(s.proposer.election_state.current_view, s.constants.my_index in s.proposer.election_state.current_view_suspectors, s.executor.ops_complete))
			)
	}

	function method CReplicaNextReadClockCheckForViewTimeout(
		s : CReplica ,
		clock : CClockReading) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CClockReadingIsValid(clock)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockCheckForViewTimeout(s, clock); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextReadClockCheckForViewTimeout(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		(
			s.(
				proposer := CProposerCheckForViewTimeout(s.proposer, clock.t)
			),
			OutboundPacket(None())
		)
	}

	function method CReplicaNextReadClockCheckForQuorumOfViewSuspicions(
		s : CReplica ,
		clock : CClockReading) : (CReplica, COutboundPackets)
		requires CReplicaIsValid(s)
		requires CClockReadingIsValid(clock)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, clock); CReplicaIsValid(s') && (forall i :: i in sequential_sent_packets ==> i.CPacket? && CPacketIsValid(i)) && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		(
			s.(
				proposer := CProposerCheckForQuorumOfViewSuspicions(s.proposer, clock.t)
			),
			OutboundPacket(None())
		)
	}
 
}
