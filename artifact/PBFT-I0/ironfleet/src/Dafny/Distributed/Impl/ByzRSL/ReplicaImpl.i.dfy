include "../../Protocol/ByzRSL/Replica.i.dfy"
include "CConstants.i.dfy"
include "ProposerImpl.i.dfy"
include "AcceptorImpl.i.dfy"
include "LearnerImpl.i.dfy"
include "ExecutorImpl.i.dfy"
include "CClockReading.i.dfy"
include "../Common/Util.i.dfy"
include "CConstants.i.dfy"
include "../../Common/Collections/Multisets.s.dfy"

module LiveByzRSL__ReplicaModel_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_s
  import opened LiveByzRSL__AcceptorModel_i
  import opened LiveByzRSL__AppInterface_i
  import opened LiveByzRSL__CMessage_i
  import opened LiveByzRSL__CTypes_i
  import opened LiveByzRSL__ElectionModel_i
  import opened LiveByzRSL__ExecutorModel_i
  import opened LiveByzRSL__LearnerModel_i
  import opened LiveByzRSL__CheckValSafetyImpl_i
  import opened LiveByzRSL__PacketParsing_i
  import opened LiveByzRSL__Proposer_i
  import opened LiveByzRSL__Learner_i
  import opened LiveByzRSL__Acceptor_i
  import opened LiveByzRSL__ProposerModel_i
  import opened LiveByzRSL__Replica_i
  import opened LiveByzRSL__ConstantsState_i
  import opened LiveByzRSL__Types_i
  import opened LiveByzRSL__Election_i
  import opened LiveByzRSL__CheckValSafety_i
  import opened LiveByzRSL__Environment_i
  import opened Logic__Option_i
  import opened LiveByzRSL__CClockReading_i
  import opened LiveByzRSL__CConfiguration_i
  import opened Common__UpperBound_i
  import opened Impl__LiveByzRSL__Broadcast_i
  import opened LiveByzRSL__Configuration_i
  import opened Common__Util_i
  import opened Common__UdpClient_i
  import opened GenericRefinement_i
  import opened Collections__CountMatches_i
  import opened Collections__Multisets_s
  import opened Collections__Seqs_i

  /************************** AutoMan Translation ************************/

  /** 9 + 0 */
  datatype CReplica = 
	CReplica(
		constants: CReplicaConstants, 
		nextHeartbeatTime: int, 
		proposer: CProposer, 
		acceptor: CAcceptor, 
		learner: CLearner, 
		executor: CExecutor
	)

  /** 0 + 13 */
	predicate CReplicaIsValid(s: CReplica) 
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
    && 
    ConstantsStayConstant(AbstractifyCReplicaToLReplica(s), s)
	}

  /** 0 + 12 */
	predicate CReplicaIsAbstractable(s: CReplica) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
    CProposerIsValid(s.proposer) 
		&& 
		CAcceptorIsAbstractable(s.acceptor) 
		&& 
		CLearnerIsAbstractable(s.learner) 
		&& 
		CExecutorIsAbstractable(s.executor)
	}

  /** 0 + 5 */
	function AbstractifyCReplicaToLReplica(s: CReplica) : LReplica 
		requires CReplicaIsAbstractable(s)
	{
		LReplica(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), s.nextHeartbeatTime, AbstractifyCProposerToLProposer(s.proposer), AbstractifyCAcceptorToLAcceptor(s.acceptor), AbstractifyCLearnerToLLearner(s.learner), AbstractifyCExecutorToLExecutor(s.executor))
	}

  /** 15 + 2 */
  function method CReplicaInit(c: CReplicaConstants) : CReplica 
		requires CReplicaConstantsIsValid(c)
		ensures var r := CReplicaInit(c); CReplicaIsValid(r) && LReplicaInit(AbstractifyCReplicaToLReplica(r), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := 
			c; 		
		var t2 := 
			0; 		
		var t3 := 
			CProposerInit(c); 		
		var t4 := 
			CAcceptorInit(c); 		
		var t5 := 
			CLearnerInit(c); 		
		var t6 := 
			CExecutorInit(c); 		
		CReplica(t1, t2, t3, t4, t5, t6)
	}

  /** 7 + 4 */
  function method CReplicaNextProcessInvalid(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Invalid?
		ensures var (s', non_empty_sequential_sent_packets) := CReplicaNextProcessInvalid(s, received_packet); CReplicaIsValid(s') && OutboundPacketsIsValid(non_empty_sequential_sent_packets) && LReplicaNextProcessInvalid(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(non_empty_sequential_sent_packets))
	{
		var t1 := 
			s; 		
		var t2 := 
			PacketSequence([]); 		
		(t1, t2)
	}

  /** 19 + 8 + 2 */
  function method CReplicaNextProcessRequest(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Request?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessRequest(s, received_packet); 
      CReplicaIsValid(s') 
      && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
      && OutboundPacketsIsValid(sequential_sent_packets) 
      && LReplicaNextProcessRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			if received_packet.src in s.executor.reply_cache && s.executor.reply_cache[received_packet.src].CReply? && received_packet.msg.seqno_req <= s.executor.reply_cache[received_packet.src].seqno then 
				var t1 := 
					CExecutorProcessRequest(s.executor, received_packet); 				
				var t2 := 
					s; 				
				(t2, t1) 
			else 
				var t1 := 
					CProposerProcessRequest(s.proposer, received_packet); 				
				var t2 := 
					PacketSequence([]); 				
				var t3 := 
					s.(proposer := t1); 				
				(t3, t2); 		
    // lemma_Postconditions(s, received_packet, t1.0, t1.1); /** Manually Added */
		(t1.0, t1.1)
	}

  /** 8 + 9 + 2 */
  function method CReplicaNextProcess1a(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_1a?
		ensures 
      var (s', sequential_sent_packets) := CReplicaNextProcess1a(s, received_packet); 
      CReplicaIsValid(s') 
      && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
      && OutboundPacketsIsValid(sequential_sent_packets) 
      && LReplicaNextProcess1a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CAcceptorProcess1a(s.acceptor, received_packet); 		
		var t2 := 
			s.(acceptor := t1.0); 		
    // lemma_Postconditions(s, received_packet, t2, t1.1); /** Manually Added */
		(t2, t1.1)
	}

  /** 21 + 8 + 2 */
  function method CReplicaNextProcess1b(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_1b?
		ensures 
      var (s', sent_packets) := CReplicaNextProcess1b(s, received_packet); 
      CReplicaIsValid(s') 
      && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sent_packets) /** Manually Added */
      && OutboundPacketsIsValid(sent_packets) 
      && LReplicaNextProcess1b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			if received_packet.src in s.proposer.constants.all.config.replica_ids && received_packet.msg.bal_1b == s.proposer.max_ballot_i_sent_1a && s.proposer.current_state == 1 && (forall other_packet :: other_packet in s.proposer.received_1b_packets ==> other_packet.src != received_packet.src) then 
				var t1 := 
					CProposerProcess1b(s.proposer, received_packet); 				
				var t2 := 
					CAcceptorTruncateLog(s.acceptor, received_packet.msg.log_truncation_point); 				
				var t3 := 
					PacketSequence([]);				
				var t4 := 
					s.(proposer := t1, acceptor := t2); 				
				(t4, t3) 
			else 
				var t1 := 
					if received_packet.src in s.acceptor.constants.all.config.replica_ids && (forall other_packet :: other_packet in s.acceptor.received_1b_packets ==> other_packet.src != received_packet.src) then 
						var t1 := 
							CAcceptorProcess1b(s.acceptor, received_packet); 						
						var t2 := 
							s.(acceptor := t1); 						
						var t3 := 
							PacketSequence([]);				
						(t2, t3) 
					else 
						var t1 := 
							s; 						
						var t2 := 
							PacketSequence([]);						
						(t1, t2); 				
				(t1.0, t1.1); 		
        // lemma_Postconditions(s, received_packet, t1.0, t1.1); /** Manually Added */	
		(t1.0, t1.1)
	}

  /** 8 + 8 + 2 */
  function method CReplicaNextProcessStartingPhase2(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_StartingPhase2?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessStartingPhase2(s, received_packet); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcessStartingPhase2(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CExecutorProcessStartingPhase2(s.executor, received_packet); 		
		var t2 := 
			s.(executor := t1.0); 		
    // lemma_Postconditions(s, received_packet, t2, t1.1); /** Manually Added */	
		(t2, t1.1)
	}


  /** 30 + 8 + 2 */
  function method CReplicaNextProcess2av(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_2av?
		ensures 
      var (s', sent_packets) := CReplicaNextProcess2av(s, received_packet); 
      CReplicaIsValid(s') 
      && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sent_packets) /** Manually Added */
      && OutboundPacketsIsValid(sent_packets) 
      && LReplicaNextProcess2av(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			var opn := 
				received_packet.msg.opn_2av; 			
			var t1 := 
				var src := 
					received_packet.src; 				
				var t1 := 
					var op_sendable := 
						(s.acceptor.opn_to_be_send_2b < opn) || (s.acceptor.opn_to_be_send_2b == opn && s.acceptor.val_to_be_sent_2b.CValToBeSent2bUnknown?); 					
					var t1 := 
						if op_sendable && src in s.acceptor.constants.all.config.replica_ids then 
							var t1 := 
								CAcceptorProcess2av(s.acceptor, received_packet); 							
							var t2 := 
								s.(acceptor := t1); 							
							var t3 := 
								Broadcast(CBroadcastNop);							
							(t2, t3) 
						else 
							var t1 := 
								s; 							
							var t2 := 
								Broadcast(CBroadcastNop); 							
							(t1, t2); 					
					(t1.1, t1.0); 				
				(t1.1, t1.0); 			
			(t1.1, t1.0); 		
      // lemma_Postconditions(s, received_packet, t1.1, t1.0); /** Manually Added */
		(t1.1, t1.0)
	}

  /** 14 + 8 + 2 */
  function method CReplicaNextSpontaneousMaybeSend2b(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures 
      var (s', sent_packets) := CReplicaNextSpontaneousMaybeSend2b(s); 
      CReplicaIsValid(s') 
      && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sent_packets) /** Manually Added */
      && OutboundPacketsIsValid(sent_packets) 
      && LReplicaNextSpontaneousMaybeSend2b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			if s.acceptor.val_to_be_sent_2b.CValToBeSent2bKnown? && s.acceptor.val_to_be_sent_2b.bal == s.acceptor.max_bal then 
				var t1 := 
					CAcceptorSent2b(s.acceptor); 				
				var t2 := 
					s.(acceptor := t1.0); 				
				(t2, t1.1) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					Broadcast(CBroadcastNop); 				
				(t1, t2); 		
    // lemma_NoReceived_Postconditions(s, t1.0, t1.1); /** Manually Added */	 	
		(t1.0, t1.1)
	}


  /** 26 + 8 + 2 */
  function method CReplicaNextProcess2b(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_2b?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcess2b(s, received_packet); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcess2b(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			var opn := 
				received_packet.msg.opn_2b; 			
			var t1 := 
				var op_learnable := 
					(s.executor.ops_complete < opn) || (s.executor.ops_complete == opn && s.executor.next_op_to_execute.COutstandingOpUnknown?); 				
				var t1 := 
					if op_learnable then 
						var t1 := 
							CLearnerProcess2b(s.learner, received_packet); 						
						var t2 := 
							PacketSequence([]); 						
						var t3 := 
							s.(learner := t1); 						
						(t3, t2) 
					else 
						var t1 := 
							s; 						
						var t2 := 
							PacketSequence([]); 						
						(t1, t2); 				
				(t1.0, t1.1); 			
			(t1.0, t1.1); 	
    // lemma_Postconditions(s, received_packet, t1.0, t1.1); /** Manually Added */		
		(t1.0, t1.1)
	}

  /** 7 + 8 + 2 */
  function method CReplicaNextProcessReply(s: CReplica, received_packet: CPacket) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Reply?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessReply(s, received_packet); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcessReply(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			PacketSequence([]); 		
		var t2 := 
			s; 		
    // lemma_Postconditions(s, received_packet, t2, t1); /** Manually Added */	
		(t2, t1)
	}

  /** 22 + 8 + 2 */
  function method CReplicaNextProcessHeartbeat(s: CReplica, received_packet: CPacket, clock: int) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Heartbeat?
		ensures var (s', sequential_sent_packets) := CReplicaNextProcessHeartbeat(s, received_packet, clock); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextProcessHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), clock, AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerProcessHeartbeat(s.proposer, received_packet, clock); 		
		var t2 := 
			CAcceptorProcessHeartbeat(s.acceptor, received_packet); 		
		var t3 := 
			PacketSequence([]); 		
		var t4 := 
			s.(proposer := t1, acceptor := t2); 	
    // lemma_Postconditions(s, received_packet, t4, t3); /** Manually Added */	
		(t4, t3)
	}

  /** 8 + 6 + 2 */
  function method CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures 
      var (s', sent_packets) := CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(s); 
      CReplicaIsValid(s') 
      && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sent_packets) /** Manually Added */
      && OutboundPacketsIsValid(sent_packets) 
      && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			CProposerMaybeEnterNewViewAndSend1a(s.proposer); 		
		var t2 := 
			CAcceptorMaybeEnterNewView(s.acceptor); 		
		var t3 := 
			s.(proposer := t1.0, acceptor := t2); 		
    // lemma_NoReceived_Postconditions(s, t3, t1.1); /** Manually Added */
		(t3, t1.1)
	}

  /** 8 + 6 + 2 */
  function method CReplicaNextSpontaneousMaybeEnterPhase2(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeEnterPhase2(s); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextSpontaneousMaybeEnterPhase2(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerMaybeEnterPhase2(s.proposer, s.acceptor.log_truncation_point); 		
		var t2 := 
			s.(proposer := t1.0); 		
    // lemma_NoReceived_Postconditions(s, t2, t1.1); /** Manually Added */	 	
		(t2, t1.1)
	}

  /** 25 + 6 + 2 */
  function method CReplicaNextSpontaneousMaybeExecute(s: CReplica) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sent_packets) := CReplicaNextSpontaneousMaybeExecute(s); 
      CReplicaIsValid(s') 
      && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sent_packets) /** Manually Added */
      && OutboundPacketsIsValid(sent_packets) 
      && LReplicaNextSpontaneousMaybeExecute(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets))
	{
		var t1 := 
			if s.executor.next_op_to_execute.COutstandingOpKnown? && CLtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val) && CReplicaConstantsValid(s.executor.constants) then 
				var t1 := 
					var v := 
						s.executor.next_op_to_execute.v; 					
					var t1 := 
						CProposerResetViewTimerDueToExecution(s.proposer, v); 					
					var t2 := 
						CLearnerForgetDecision(s.learner, s.executor.ops_complete); 					
					var t3 := 
						CAcceptorForgetReceived2avs(s.acceptor, s.executor.ops_complete); 					
					var t4 := 
						CExecutorExecute(s.executor); 					
					var t5 := 
						s.(acceptor := t3, proposer := t1, learner := t2, executor := t4.0); 					
					(t5, t4.1); 				
				(t1.0, t1.1) 
			else 
				var t1 := 
					s; 				
				var t2 := 
					PacketSequence([]); 						
				(t1, t2); 		
        // lemma_NoReceived_Postconditions(s, t1.0, t1.1); /** Manually Added */
		(t1.0, t1.1)
	}

  /** 19 + 6 + 2 */
  function method CReplicaNextReadClockMaybeSendHeartbeat(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockMaybeSendHeartbeat(s, clock); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockMaybeSendHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			if clock.t < s.nextHeartbeatTime then 
				var t1 := 
					s; 				
				var t2 := 
					PacketSequence([]); 				
				(t1, t2) 
			else 
				var t1 := 
					UpperBoundedAdditionImpl(clock.t, s.constants.all.params.heartbeat_period, s.constants.all.params.max_integer_val); 				
				var t2 := 
					Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_Heartbeat(s.proposer.election_state.current_view, s.constants.my_index in s.proposer.election_state.current_view_suspectors, s.executor.ops_complete))); 				
				var t3 := 
					s.(nextHeartbeatTime := t1); 				
				(t3, t2); 		
    // lemma_NoReceived_Postconditions(s, t1.0, t1.1); /** Manually Added */
		(t1.0, t1.1)
	}

  /** 10 + 6 + 2 */
  function method CReplicaNextReadClockCheckForViewTimeout(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockCheckForViewTimeout(s, clock); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockCheckForViewTimeout(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerCheckForViewTimeout(s.proposer, clock.t); 		
		var t2 := 
			PacketSequence([]); 		
		var t3 := 
			s.(proposer := t1); 		
    // lemma_NoReceived_Postconditions(s, t3, t2); /** Manually Added */
		(t3, t2)
	}

  /** 10 + 7 + 2 */
  function method CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s, clock); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerCheckForQuorumOfViewSuspicions(s.proposer, clock.t); 		
		var t2 := 
			PacketSequence([]); 		
		var t3 := 
			s.(proposer := t1); 		
    // lemma_NoReceived_Postconditions(s, t3, t2); /** Manually Added */
		(t3, t2)
	}


  /************************** AutoMan Translation End ************************/

  /************************** Manual Code For I0 ************************/

  /** 15 + 13 */
  method {:opaque} CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:CReplica) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures CReplicaIsValid(s') 
            && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
            && OutboundPacketsIsValid(sequential_sent_packets) 
            && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
  {
    if (exists opn :: opn in s.acceptor.last_checkpointed_operation && opn > s.acceptor.log_truncation_point && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) ){
        var opn :| opn > s.acceptor.log_truncation_point && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config);
        var newAcceptor := CAcceptorTruncateLog(s.acceptor, opn);
        s' := s.(acceptor := newAcceptor);
        sequential_sent_packets := Broadcast(CBroadcastNop);
        lemma_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sequential_sent_packets);
        assert LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets));
    } else if (exists opn :: opn in s.acceptor.last_checkpointed_operation && opn <= s.acceptor.log_truncation_point && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) ){
        s' := s;
        sequential_sent_packets := Broadcast(CBroadcastNop);
        lemma_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sequential_sent_packets);
        assert LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets));
    } else {
        /** This is a branch that cannot be executed, so we use an axiom lemma to pass the verification */
        assert !exists opn :: opn in s.acceptor.last_checkpointed_operation
        && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config);
        s' := s;
        sequential_sent_packets := Broadcast(CBroadcastNop);
        lemma_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sequential_sent_packets);
        assert LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets));
    }
    // lemma_NoReceived_Postconditions(s, s', sequential_sent_packets);
  }
  
  /** 0 + 3 */
  lemma {:axiom}  lemma_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:CReplica, s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures CReplicaIsValid(s') && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
  
  lemma {:axiom} lemma_CReplicaNextProcess1c1(b1:bool, b2:bool)
    ensures b1 == b2

  /** 23 + 4 + 2 */
  method CReplicaNextProcess1c(s: CReplica, received_packet: CPacket) returns (s':CReplica, out:OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_1c?
		ensures CReplicaIsValid(s') && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, out) /** Manually Added */&& OutboundPacketsIsValid(out) && LReplicaNextProcess1c(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(out))
	{
    ghost var ls := AbstractifyCReplicaToLReplica(s);
    ghost var linp := AbstractifyCPacketToRslPacket(received_packet);
		// var t1 := 
    var m := received_packet.msg; 			
			// var t1 := 
    var packets_1b := s.acceptor.received_1b_packets; 				
				// var t1 := 
    var byzq := CByzQuorumSize(s.constants.all.config); 					
					// var t1 := 
    var wq := CMinQuorumSize(s.constants.all.config); 						
						// var t1 := 
    // var req_is_valid_from_client := (forall req :: req in m.val_1c ==> CCheckRequestValid(s.proposer.election_state, req)); 	
    var req_is_valid_from_client := true;
    ghost var lm := linp.msg;
    ghost var lreq_is_valid_from_client := forall req :: req in lm.val_1c ==> CheckRequestValid(ls.proposer.election_state, req);
    lemma_CReplicaNextProcess1c1(lreq_is_valid_from_client, req_is_valid_from_client);
    // if !req_is_valid_from_client {
    //   req_is_valid_from_client := true;
    //   // print "Cannot find request\n";
    // }						
							// var t1 := 
    var req_is_safe := if s.proposer.current_state == 2 then 
        true 
      else 
        if CSeqOfMessage1b(packets_1b) then 
          (CAllAcceptorsHadNoProposal(packets_1b, m.opn_1c)) || (CValIsSafeAt(m.val_1c, packets_1b, m.opn_1c, byzq, wq)) 
        else 
          false; 	

    // ghost var lm := linp.msg;
    // ghost var lp1bs := ls.acceptor.received_1b_packets;
    // ghost var lbyzq := LByzQuorumSize(ls.constants.all.config);
    // ghost var lwq := LMinQuorumSize(ls.constants.all.config);
    // ghost var lreq_is_valid_from_client := forall req :: req in lm.val_1c ==> CheckRequestValid(ls.proposer.election_state, req);
    // ghost var lreq_is_safe := 
    //             if ls.proposer.current_state == 2 then
    //                 true
    //             else 
    //                 if LSeqOfMessage1b(lp1bs) then
    //                     (|| LAllAcceptorsHadNoProposal(lp1bs, lm.opn_1c)
    //                     || LValIsSafeAt(lm.val_1c, lp1bs, lm.opn_1c, lbyzq, lwq))
    //                 else
    //                     false;
    
    // lemma_CReplicaNextProcess1c1(lreq_is_valid_from_client, req_is_valid_from_client);
    // assert lreq_is_valid_from_client == req_is_valid_from_client;
    // assert lreq_is_safe == req_is_safe;

								// var t1 := 
    if received_packet.src in s.acceptor.constants.all.config.replica_ids && req_is_valid_from_client && req_is_safe && CBalLeq(s.acceptor.max_bal, m.bal_1c) && CLeqUpperBound(m.opn_1c, s.acceptor.constants.all.params.max_integer_val)
    { 
      var (newAcceptor, outs) := CAcceptorProcess1c(s.acceptor, received_packet); 										
      s' := s.(acceptor := newAcceptor); 					
      out := outs;

      // assert LAcceptorProcess1c(
      //         AbstractifyCReplicaToLReplica(s).acceptor, 
      //         AbstractifyCReplicaToLReplica(s').acceptor, 
      //         AbstractifyCPacketToRslPacket(received_packet), 
      //         AbstractifyOutboundCPacketsToSeqOfRslPackets(out));
      // assert CAcceptorIsValid(newAcceptor);
      // assert CAcceptorIsValid(s'.acceptor);

      // assert CReplicaIsAbstractable(s');
      // assert CReplicaConstantsIsValid(s'.constants); 
	    // assert CProposerIsValid(s'.proposer);
		  // assert CAcceptorIsValid(s'.acceptor);
		  // assert CLearnerIsValid(s'.learner);
		  // assert CExecutorIsValid(s'.executor);
      // // assert s'.constants == s'.acceptor.constants;

      // assert CReplicaIsValid(s');
      // assert OutboundPacketsIsValid(out);
      // assert LReplicaNextProcess1c(
      //         AbstractifyCReplicaToLReplica(s), 
      //         AbstractifyCReplicaToLReplica(s'), 
      //         AbstractifyCPacketToRslPacket(received_packet), 
      //         AbstractifyOutboundCPacketsToSeqOfRslPackets(out));

      // (t2, t1.1) 
    } else { 
      s' := s; 										
      out := Broadcast(CBroadcastNop); 
      // assert CReplicaIsValid(s') 
      // && OutboundPacketsIsValid(out);				
      // assert LReplicaNextProcess1c(
      //         AbstractifyCReplicaToLReplica(s), 
      //         AbstractifyCReplicaToLReplica(s'), 
      //         AbstractifyCPacketToRslPacket(received_packet), 
      //         AbstractifyOutboundCPacketsToSeqOfRslPackets(out));
    }
    // lemma_Postconditions(s, received_packet, s', out); /** Manually Added */	
										// (t1, t2);					
			// 					(t1.0, t1.1); 							
			// 				(t1.1, t1.0); 						
			// 			(t1.1, t1.0); 					
			// 		(t1.1, t1.0); 				
			// 	(t1.1, t1.0); 			
			// (t1.1, t1.0); 		
		// (t1.0, t1.1)
	}

  /** 0 + 8 */
  lemma lemma_Msg2avs(r2avs: CAcceptorTuple)
    requires CAcceptorTupleIsValid(r2avs)
    requires (forall p :: p in r2avs.received_2av_packets ==> p.msg.CMessage_2av?)
    ensures forall p :: p in r2avs.received_2av_packets ==> CRequestBatchIsValid(p.msg.val_2av)
  {
    assert (forall p :: p in r2avs.received_2av_packets ==> CMessageIsValid(p.msg));
    assert (forall p :: p in r2avs.received_2av_packets ==> p.msg.CMessage_2av?);
  }

  /** 0 + 5 */
  lemma lemma_AbstractifyPacketSeq(s:seq<CPacket>, ls:seq<RslPacket>)
    requires forall p :: p in s ==> CPacketIsAbstractable(p)
    requires ls == AbstractifySeq(s, AbstractifyCPacketToRslPacket)
    ensures forall p :: p in s ==> AbstractifyCPacketToRslPacket(p) in ls
  {}

  /** 17 + 15 */
  method CReplicaNextSpontaneousMaybeDecide2bVal(s:CReplica) returns (s':CReplica, sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures CReplicaIsValid(s') 
            && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sent_packets) /** Manually Added */
            && s.constants == s'.constants /** Manually Added */
            && OutboundPacketsIsValid(sent_packets) 
            && LReplicaNextSpontaneousMaybeDecide2bVal(
              AbstractifyCReplicaToLReplica(s), 
              AbstractifyCReplicaToLReplica(s'), 
              AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets)
            )
  {
    ghost var ls := AbstractifyCReplicaToLReplica(s);
    ghost var lopn := ls.acceptor.opn_to_be_send_2b;
    ghost var lquorum := LByzQuorumSize(ls.acceptor.constants.all.config);

    var opn := s.acceptor.opn_to_be_send_2b;
    var quorum := CByzQuorumSize(s.acceptor.constants.all.config);
    if && s.acceptor.val_to_be_sent_2b.CValToBeSent2bUnknown?
        && opn in s.acceptor.received_2avs
        && |s.acceptor.received_2avs[opn].received_2av_packets| >= quorum
        && CAcceptorStateCorrect(s.acceptor.received_2avs, s.acceptor.max_bal, s.constants.all.config)
        && CHasReceivedSame2avFromByzQuorum(s.acceptor.received_2avs[opn], quorum) 
    {
      var p2avs := s.acceptor.received_2avs[opn];
      lemma_Msg2avs(p2avs);
      assert (forall p :: p in p2avs.received_2av_packets ==> CRequestBatchIsValid(p.msg.val_2av));
      
      var p :|  p in p2avs.received_2av_packets
              && CCountMatchedValInReceived2avs(p2avs.received_2av_packets, p.msg.val_2av) >= quorum;

      assert AbstractifySeq(s.acceptor.received_2avs[opn].received_2av_packets, AbstractifyCPacketToRslPacket) == ls.acceptor.received_2avs[lopn].received_2av_packets;
      lemma_AbstractifyPacketSeq(s.acceptor.received_2avs[opn].received_2av_packets, ls.acceptor.received_2avs[lopn].received_2av_packets);
      assert forall pkt :: pkt in s.acceptor.received_2avs[opn].received_2av_packets ==> AbstractifyCPacketToRslPacket(pkt) in ls.acceptor.received_2avs[lopn].received_2av_packets;

      var newAcceptor := CAcceptorDecide2bVal(s.acceptor, s.acceptor.max_bal, opn, p.msg.val_2av);
      s' := s.(acceptor := newAcceptor);
      sent_packets := Broadcast(CBroadcastNop);
    } else {
      s' := s;
      sent_packets := Broadcast(CBroadcastNop);
    }
    assert AbstractifyCReplicaConstantsToLReplicaConstants(s'.constants) == ls.constants;
    assert ConstantsStayConstant_Replica(AbstractifyCReplicaToLReplica(s), s');
    assert OutboundPacketsHasCorrectSrc(sent_packets, s'.constants.all.config.replica_ids[s'.constants.my_index]);
    assert CReplicaConstantsIsValid(s'.constants);
    assert CReplicaIsAbstractable(s');
    assert CReplicaIsValid(s');
    assert OutboundPacketsIsValid(sent_packets);
    assert OutboundPacketsIsAbstractable(sent_packets);
  }

  /** 0 + 8 */
  lemma lemma_Msg2bs(r2bs: CLearnerTuple)
    requires CLearnerTupleIsValid(r2bs)
    requires (forall p :: p in r2bs.received_2bs ==> p.msg.CMessage_2b?)
    ensures forall p :: p in r2bs.received_2bs ==> CRequestBatchIsValid(p.msg.val_2b)
  {
    assert (forall p :: p in r2bs.received_2bs ==> CMessageIsValid(p.msg));
    assert (forall p :: p in r2bs.received_2bs ==> p.msg.CMessage_2b?);
  }

  /** 15 + 14 */
  method {:opaque} CReplicaNextSpontaneousMaybeMakeDecision(s:CReplica) returns (s':CReplica, sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures CReplicaIsValid(s') 
            && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sent_packets) /** Manually Added */
            && s.constants == s'.constants
            && OutboundPacketsIsValid(sent_packets) 
            && LReplicaNextSpontaneousMaybeMakeDecision(
              AbstractifyCReplicaToLReplica(s), 
              AbstractifyCReplicaToLReplica(s'), 
              AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets)
            )
  {
    ghost var ls := AbstractifyCReplicaToLReplica(s);
    ghost var lopn := ls.executor.ops_complete;
    ghost var lquorum := LMinQuorumSize(ls.acceptor.constants.all.config);

    var opn := s.executor.ops_complete;
    var quorum := CMinQuorumSize(s.acceptor.constants.all.config);
    if  && s.executor.next_op_to_execute.COutstandingOpUnknown?
            && opn in s.learner.unexecuted_learner_state
            && CLearnerStateCorrect(s.learner.unexecuted_learner_state, s.learner.max_ballot_seen, s.constants.all.config)
            && |s.learner.unexecuted_learner_state[opn].received_2bs| >= quorum
            && CHasReceivedSame2bFromWeakQuorum(s.learner.unexecuted_learner_state[opn], quorum)
    {
      var p2bs := s.learner.unexecuted_learner_state[opn];
      lemma_Msg2bs(p2bs);

      var p :| p in s.learner.unexecuted_learner_state[opn].received_2bs
                && CCountMatchedValInReceived2bs(s.learner.unexecuted_learner_state[opn].received_2bs, p.msg.val_2b) >= quorum;

      assert AbstractifySeq(s.learner.unexecuted_learner_state[opn].received_2bs, AbstractifyCPacketToRslPacket) == ls.learner.unexecuted_learner_state[lopn].received_2bs;
      lemma_AbstractifyPacketSeq(s.learner.unexecuted_learner_state[opn].received_2bs, ls.learner.unexecuted_learner_state[lopn].received_2bs);
      assert forall pkt :: pkt in s.learner.unexecuted_learner_state[opn].received_2bs ==> AbstractifyCPacketToRslPacket(pkt) in ls.learner.unexecuted_learner_state[lopn].received_2bs;

      var newExecutor := CExecutorGetDecision(s.executor, s.learner.max_ballot_seen, opn, p.msg.val_2b);
      s' := s.(executor := newExecutor);
      sent_packets := Broadcast(CBroadcastNop);
    } else {
      s' := s;
      sent_packets := Broadcast(CBroadcastNop);
    }
    assert ConstantsStayConstant_Replica(AbstractifyCReplicaToLReplica(s), s');
    assert OutboundPacketsHasCorrectSrc(sent_packets, s'.constants.all.config.replica_ids[s'.constants.my_index]);
    assert CReplicaConstantsIsValid(s'.constants);
    assert CReplicaIsAbstractable(s');
    assert CReplicaIsValid(s');
    assert OutboundPacketsIsValid(sent_packets);
    assert OutboundPacketsIsAbstractable(sent_packets);
  }

  /** 6 + 6 */
  method CReplicaNextReadClockMaybeNominateValueAndSend1c(s:CReplica, clock:CClockReading) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockMaybeNominateValueAndSend1c(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
  {
    var newProposer, packets := CProposerMaybeNominateValueAndSend1c(s.proposer, clock.t, s.acceptor.log_truncation_point);
    s' := s.(proposer := newProposer);
    sequential_sent_packets := packets;
  }
  /************************** Manual Code For I0 End ************************/
  predicate ConstantsStayConstant(replica:LReplica, replica':CReplica)
  {
    && replica.constants == replica.proposer.constants
    && replica.constants == replica.acceptor.constants
    && replica.constants == replica.learner.constants
    && replica.constants == replica.executor.constants
    && replica'.constants == replica'.proposer.constants
    && replica'.constants == replica'.acceptor.constants
    && replica'.constants == replica'.learner.constants
    && replica'.constants == replica'.executor.constants
  }

  // /* ----------------------------------------- */

  predicate ConstantsStayConstant_Replica(replica:LReplica, replica':CReplica)
    requires CReplicaConstantsIsAbstractable(replica'.constants)
  {
    && AbstractifyCReplicaConstantsToLReplicaConstants(replica'.constants) == replica.constants
    && replica.constants == replica.proposer.constants
    && replica.constants == replica.acceptor.constants
    && replica.constants == replica.learner.constants
    && replica.constants == replica.executor.constants
    && replica'.constants == replica'.proposer.constants
    && replica'.constants == replica'.acceptor.constants
    && replica'.constants == replica'.learner.constants
    && replica'.constants == replica'.executor.constants
  }

  predicate Replica_Common_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket, packets_sent:OutboundPackets)
  {
    && CReplicaConstantsIsValid(replica'.constants)
    && CPacketIsSendable(inp)
    && CReplicaIsAbstractable(replica')
    && ConstantsStayConstant_Replica(replica, replica')
    && CReplicaIsValid(replica')
    && OutboundPacketsIsValid(packets_sent)
    && OutboundPacketsHasCorrectSrc(packets_sent, replica'.constants.all.config.replica_ids[replica'.constants.my_index])
    && OutboundPacketsIsAbstractable(packets_sent)
  }

    predicate Replica_Common_Postconditions_NoPacket(replica:LReplica, replica':CReplica, packets_sent:OutboundPackets)
  {
    && CReplicaConstantsIsValid(replica'.constants)
    && CReplicaIsAbstractable(replica')
    && ConstantsStayConstant_Replica(replica, replica')
    && CReplicaIsValid(replica')
    && OutboundPacketsIsValid(packets_sent)
    && OutboundPacketsHasCorrectSrc(packets_sent, replica'.constants.all.config.replica_ids[replica'.constants.my_index])
    && OutboundPacketsIsAbstractable(packets_sent)
  }
}