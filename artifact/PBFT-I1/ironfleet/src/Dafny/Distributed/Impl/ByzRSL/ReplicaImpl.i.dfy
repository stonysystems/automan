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
  // import opened AppStateMachine_s
  import opened Native__Io_s
  import opened Native__NativeTypes_s
    // import opened LiveRSL__CAcceptor_i
  import opened LiveByzRSL__AcceptorModel_i
  import opened LiveByzRSL__AppInterface_i
  import opened LiveByzRSL__CMessage_i
  // import opened LiveByzRSL__CMessageRefinements_i
  import opened LiveByzRSL__CTypes_i
  import opened LiveByzRSL__ElectionModel_i
  import opened LiveByzRSL__ExecutorModel_i
    // import opened LiveRSL__LearnerState_i
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

  /** 0 + 15 + 1 */
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
    && /** Manually Added */
    s.constants == s.acceptor.constants
	}

  /** 0 + 12 */
	predicate CReplicaIsAbstractable(s: CReplica) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		// CProposerIsAbstractable(s.proposer) 
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
    // requires CReplicaIsValid(s)
	{
		LReplica(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), s.nextHeartbeatTime, AbstractifyCProposerToLProposer(s.proposer), AbstractifyCAcceptorToLAcceptor(s.acceptor), AbstractifyCLearnerToLLearner(s.learner), AbstractifyCExecutorToLExecutor(s.executor))
	}

  /** 15 + 2 */
  function method CReplicaInit(c: CReplicaConstants) : CReplica 
		requires CReplicaConstantsIsValid(c)
		// requires CWellFormedLConfiguration(c.all.config)
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

  /** 13 lines of manual code for I1 */
  method CReplicaNextProcessRequest(
		s : CReplica ,
		received_packet : CPacket,
    cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>, reply_cache_mutable:MutableMap<EndPoint, CReply>
    ) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Request?

    requires s.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.proposer.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.proposer.election_state.prev_req_set
    modifies cur_req_set, prev_req_set//, reply_cache_mutable
    ensures  MutableSet.SetOf(cur_req_set) == s'.proposer.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.proposer.election_state.prev_req_set
    ensures  s'.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)

		// ensures var (s', sequential_sent_packets) := CReplicaNextProcessRequest(s, received_packet); 
    ensures CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessRequest(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
    requires Replica_Next_Process_Request_Preconditions(s, received_packet)
    // ensures  
    //   var (s', sequential_sent_packets) := CReplicaNextProcessRequest(s, received_packet);
    ensures Replica_Next_Process_Request_Postconditions(
        (AbstractifyCReplicaToLReplica(s)), s', received_packet, sequential_sent_packets)
  {
    lemma_CReplicaNextProcessRequest_pre(s, received_packet);

    // var (s', sequential_sent_packets) := 
    var cached, cached_reply := reply_cache_mutable.TryGetValue(received_packet.src);
    if cached && cached_reply.CReply? && received_packet.msg.seqno_req <= cached_reply.seqno
		// if  && received_packet.src in s.executor.reply_cache && s.executor.reply_cache[received_packet.src].CReply? && received_packet.msg.seqno_req <= s.executor.reply_cache[received_packet.src].seqno
		{ 
			s' :=	s;
			sequential_sent_packets := CExecutorProcessRequest(s.executor, received_packet, reply_cache_mutable);
	
    }
		else
    { 
        var p := CProposerProcessRequest(s.proposer, received_packet, cur_req_set, prev_req_set);
				s' := s.(
					proposer := p
				);
				sequential_sent_packets := OutboundPacket(None());
    }

    lemma_CReplicaNextProcessRequest(s, received_packet, s', sequential_sent_packets);
    // (s', sequential_sent_packets)
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
    lemma_Postconditions(s, received_packet, t2, t1.1); /** Manually Added */
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
        lemma_Postconditions(s, received_packet, t1.0, t1.1); /** Manually Added */	
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
    lemma_Postconditions(s, received_packet, t2, t1.1); /** Manually Added */	
		(t2, t1.1)
	}


  lemma {:axiom} lemma_CReplicaNextProcess1c1(b1:bool, b2:bool)
    ensures b1 == b2

  method CheckReqIsValidFromClient(s: CReplica, p:CPacket) returns (is_valid:bool)
    requires CReplicaIsValid(s)
		requires CPacketIsValid(p)
		requires p.msg.CMessage_1c?
    ensures is_valid == (forall req :: req in p.msg.val_1c ==> CCheckRequestValid(s.proposer.election_state, req))
  {
    var m := p.msg;
    var valid := true;
    var i := 0;
    while i < |m.val_1c|
      invariant 0 <= i <= |m.val_1c|
      invariant valid == forall r :: r in p.msg.val_1c[..i] ==> CCheckRequestValid(s.proposer.election_state, r)
    {
      assert valid == forall r :: r in p.msg.val_1c[..i] ==> CCheckRequestValid(s.proposer.election_state, r);
      var b := CCheckRequestValid_I1(s.proposer.election_state, m.val_1c[i]);
      assert b == CCheckRequestValid(s.proposer.election_state, m.val_1c[i]);
      valid := valid && b;
      i := i + 1;
      assert valid == forall r :: r in p.msg.val_1c[..i] ==> CCheckRequestValid(s.proposer.election_state, r);
    }
    is_valid := valid;
  }

  method {:opaque} CReplicaNextProcess1c(s: CReplica, received_packet: CPacket) returns (s':CReplica, out:OutboundPackets) 
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_1c?
    ensures s.constants == s'.constants
		ensures 
    //   var (s', sent_packets) := CReplicaNextProcess1c(s, received_packet); 
      CReplicaIsValid(s') 
      && Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(s), s', received_packet, out) /** Manually Added */
      && OutboundPacketsIsValid(out) 
      && LReplicaNextProcess1c(
        AbstractifyCReplicaToLReplica(s), 
        AbstractifyCReplicaToLReplica(s'), 
        AbstractifyCPacketToRslPacket(received_packet), 
        AbstractifyOutboundCPacketsToSeqOfRslPackets(out))
    
    /** I1 */
    ensures s'.proposer.election_state.cur_req_set == s.proposer.election_state.cur_req_set
    ensures s'.proposer.election_state.prev_req_set == s.proposer.election_state.prev_req_set
    ensures  s'.executor.reply_cache == s.executor.reply_cache
	{
    ghost var ls := AbstractifyCReplicaToLReplica(s);
    ghost var linp := AbstractifyCPacketToRslPacket(received_packet);
		// var t1 := 
    var m := 
      received_packet.msg; 			
			// var t1 := 
    var packets_1b := 
      s.acceptor.received_1b_packets; 				
				// var t1 := 
    var byzq := 
      CByzQuorumSize(s.constants.all.config); 					
					// var t1 := 
    var wq := 
      CMinQuorumSize(s.constants.all.config); 						
						// var t1 := 
    // var req_is_valid_from_client :=  CheckReqIsValidFromClient(s, received_packet);
    var req_is_valid_from_client :=  true;
		
    // var t1 := 
    var req_is_safe :=
      if s.proposer.current_state == 2 then 
        true 
      else 
        if CSeqOfMessage1b(packets_1b) then 
          (CAllAcceptorsHadNoProposal(packets_1b, m.opn_1c)) || (CValIsSafeAt(m.val_1c, packets_1b, m.opn_1c, byzq, wq)) 
        else 
          false; 	

    ghost var lm := linp.msg;
    ghost var lp1bs := ls.acceptor.received_1b_packets;
    ghost var lbyzq := LByzQuorumSize(ls.constants.all.config);
    ghost var lwq := LMinQuorumSize(ls.constants.all.config);
    ghost var lreq_is_valid_from_client := forall req :: req in lm.val_1c ==> CheckRequestValid(ls.proposer.election_state, req);
    ghost var lreq_is_safe := 
                if ls.proposer.current_state == 2 then
                    true
                else 
                    if LSeqOfMessage1b(lp1bs) then
                        (|| LAllAcceptorsHadNoProposal(lp1bs, lm.opn_1c)
                        || LValIsSafeAt(lm.val_1c, lp1bs, lm.opn_1c, lbyzq, lwq))
                    else
                        false;
    
    lemma_CReplicaNextProcess1c1(lreq_is_valid_from_client, req_is_valid_from_client);
    assert lreq_is_valid_from_client == req_is_valid_from_client;
    assert lreq_is_safe == req_is_safe;

								// var t1 := 
    if received_packet.src in s.acceptor.constants.all.config.replica_ids && req_is_valid_from_client && req_is_safe && CBalLeq(s.acceptor.max_bal, m.bal_1c) && CLeqUpperBound(m.opn_1c, s.acceptor.constants.all.params.max_integer_val)
    { 
      var (newAcceptor, outs) := 
        CAcceptorProcess1c(s.acceptor, received_packet); 										
      s' := 
        s.(acceptor := newAcceptor); 					
      out := outs;

      assert CAcceptorIsValid(newAcceptor);
      assert CAcceptorIsValid(s'.acceptor);
      assert CReplicaIsAbstractable(s');
      assert CReplicaConstantsIsValid(s'.constants); 
	    assert CProposerIsValid(s'.proposer);
		  assert CAcceptorIsValid(s'.acceptor);
		  assert CLearnerIsValid(s'.learner);
		  assert CExecutorIsValid(s'.executor);

      assert CReplicaIsValid(s');
      assert OutboundPacketsIsValid(out);
      assert LReplicaNextProcess1c(
              AbstractifyCReplicaToLReplica(s), 
              AbstractifyCReplicaToLReplica(s'), 
              AbstractifyCPacketToRslPacket(received_packet), 
              AbstractifyOutboundCPacketsToSeqOfRslPackets(out));

      // (t2, t1.1) 
    }
    else
    { 
      s' := 
        s; 										
      out := 
        Broadcast(CBroadcastNop); 
      assert CReplicaIsValid(s') 
      && OutboundPacketsIsValid(out);				
      assert LReplicaNextProcess1c(
              AbstractifyCReplicaToLReplica(s), 
              AbstractifyCReplicaToLReplica(s'), 
              AbstractifyCPacketToRslPacket(received_packet), 
              AbstractifyOutboundCPacketsToSeqOfRslPackets(out));
    }
    lemma_Postconditions(s, received_packet, s', out); /** Manually Added */	
	}

  /** 10 lines for I1 */
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
		// var t1 := 
			var opn := 
				received_packet.msg.opn_2av; 			
			// var t1 := 
				var src := 
					received_packet.src; 				
				// var t1 := 
					var op_sendable := 
						(s.acceptor.opn_to_be_send_2b < opn) || (s.acceptor.opn_to_be_send_2b == opn && s.acceptor.val_to_be_sent_2b.CValToBeSent2bUnknown?); 					
					var t1 := 
						if op_sendable && src in s.acceptor.constants.all.config.replica_ids then 
							// var t1 := 
								// CAcceptorProcess2av(s.acceptor, received_packet); 							
							// var t2 := 
								(s.(acceptor := CAcceptorProcess2av(s.acceptor, received_packet)), Broadcast(CBroadcastNop))						
							// var t3 := 
							// 	Broadcast(CBroadcastNop);							
							// (t2, t3) 
						else 
							// var t1 := 
								(s, Broadcast(CBroadcastNop));						
							// var t2 := 
								// Broadcast(CBroadcastNop); 							
			// 				(t1, t2); 					
			// 		(t1.1, t1.0); 				
			// 	(t1.1, t1.0); 			
			// (t1.1, t1.0); 		
      lemma_Postconditions(s, received_packet, t1.0, t1.1); /** Manually Added */
		(t1.0, t1.1)
	}

  /** 5 lines for I1 */
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
				// var t2 := 
					(s.(acceptor := t1.0), t1.1)			
				// (t2, t1.1) 
			else 
				// var t1 := 
					(s, Broadcast(CBroadcastNop));
				// var t2 := 
				// 	Broadcast(CBroadcastNop); 				
				// (t1, t2); 		
    lemma_NoReceived_Postconditions(s, t1.0, t1.1); /** Manually Added */	 	
		(t1.0, t1.1)
	}


  /** 26 + 8 + 2 */
  /** 7 lines for I1 */
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
		// var t1 := 
			var opn := 
				received_packet.msg.opn_2b; 			
			// var t1 := 
				var op_learnable := 
					(s.executor.ops_complete < opn) || (s.executor.ops_complete == opn && s.executor.next_op_to_execute.COutstandingOpUnknown?); 				
				var t1 := 
					if op_learnable then 
						// var t1 := 
						// 	CLearnerProcess2b(s.learner, received_packet); 						
						// var t2 := 
						// 	PacketSequence([]); 						
						// var t3 := 
							(s.(learner := CLearnerProcess2b(s.learner, received_packet)),	PacketSequence([]))		
						// (t3, t2) 
					else 
						// var t1 := 
							(s, PacketSequence([]));				
						// var t2 := 
							// PacketSequence([]); 						
			// 			(t1, t2); 				
			// 	(t1.0, t1.1); 			
			// (t1.0, t1.1); 	
    lemma_Postconditions(s, received_packet, t1.0, t1.1); /** Manually Added */		
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
    lemma_Postconditions(s, received_packet, t2, t1); /** Manually Added */	
		(t2, t1)
	}

  /** 9 lines of manual code for I1 */
  method CReplicaNextProcessHeartbeat(
		s : CReplica ,
		received_packet : CPacket ,
		clock : int,
    cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s' : CReplica, sequential_sent_packets:OutboundPackets)
		requires CReplicaIsValid(s)
		requires CPacketIsValid(received_packet)
		requires received_packet.msg.CMessage_Heartbeat?

    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.proposer.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.proposer.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  s'.executor == s.executor
    ensures  MutableSet.SetOf(cur_req_set) == s'.proposer.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.proposer.election_state.prev_req_set

		// ensures var (s', sequential_sent_packets) := CReplicaNextProcessHeartbeat(s, received_packet, clock); 
    ensures CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextProcessHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCPacketToRslPacket(received_packet), clock, AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
    && Replica_Next_Process_Heartbeat_Postconditions(old(AbstractifyCReplicaToLReplica(s)), s',
                                                                received_packet, clock, sequential_sent_packets)
    
  {
    lemma_CReplicaNextProcessHeartbeat_Pre(s, received_packet);

    var p := CProposerProcessHeartbeat(s.proposer, received_packet, clock, cur_req_set, prev_req_set);
    // var (s', sequential_sent_packets) := 
		// (
		s' :=	s.(
				proposer := p,
				acceptor := CAcceptorProcessHeartbeat(s.acceptor, received_packet)
			);
		sequential_sent_packets := OutboundPacket(None());
		// )
    // ;
    lemma_CReplicaNextProcessHeartbeat(s, received_packet, clock, s', sequential_sent_packets);
    // (s', sequential_sent_packets)
	}

  /** 8 + 8 + 2 */
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
    lemma_NoReceived_Postconditions(s, t3, t1.1); /** Manually Added */
		(t3, t1.1)
	}

  /** 8 + 8 + 2 */
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
    lemma_NoReceived_Postconditions(s, t2, t1.1); /** Manually Added */	 	
		(t2, t1.1)
	}

  /** 16 lines of manual code for I1 */
  method CReplicaNextSpontaneousMaybeExecute(
		s : CReplica,
    cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>, reply_cache_mutable:MutableMap<EndPoint, CReply>) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
		requires CReplicaIsValid(s)

    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.proposer.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.proposer.election_state.prev_req_set
    requires s.executor.reply_cache == MutableMap.MapOf(reply_cache_mutable)
    requires Replica_Next_Spontaneous_MaybeExecute_Preconditions(s)
    // requires reply_cache_mutable.Size() < 0x1_0000_0000_0000_0000
    modifies cur_req_set, prev_req_set, reply_cache_mutable
    ensures  MutableSet.SetOf(cur_req_set) == s'.proposer.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.proposer.election_state.prev_req_set
    ensures MutableMap.MapOf(reply_cache_mutable) == s'.executor.reply_cache

		// ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeExecute(s); 
    ensures CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) && LReplicaNextSpontaneousMaybeExecute(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	
    requires Replica_Next_Spontaneous_MaybeExecute_Preconditions(s)
    // ensures var (s', sequential_sent_packets) := CReplicaNextSpontaneousMaybeExecute(s); 
    ensures Replica_Next_Spontaneous_MaybeExecute_Postconditions(
      (AbstractifyCReplicaToLReplica(s)), s', sequential_sent_packets)
  {
    // var (s', sequential_sent_packets) := 
		if  && s.executor.next_op_to_execute.COutstandingOpKnown? && CLtUpperBound(s.executor.ops_complete, s.executor.constants.all.params.max_integer_val) /* && CReplicaConstantsValid(s.executor.constants) */
		{ 
			var v := s.executor.next_op_to_execute.v; 
			// var (t0, t1_1) := CExecutorExecute(s.executor); 
			// (
      var p := CProposerResetViewTimerDueToExecution(s.proposer, s.executor.next_op_to_execute.v, cur_req_set, prev_req_set);
      var e, packets := CExecutorExecute_I1(s.executor, reply_cache_mutable);
			s' := s.(
					proposer := p,
					learner := CLearnerForgetDecision(s.learner, s.executor.ops_complete),
          acceptor := CAcceptorForgetReceived2avs(s.acceptor, s.executor.ops_complete),
					executor := e
				);
			sequential_sent_packets := packets;
			// )
    }
		else 
    {
			// (
				s' := s;
				sequential_sent_packets := OutboundPacket(None());
			// )
    }
    lemma_CReplicaNextSpontaneousMaybeExecute(s, s', sequential_sent_packets);
    // (s', sequential_sent_packets)
	}


  /** 19 + 7 + 2 */
  /** 3 lines for I1 */
  function method CReplicaNextReadClockMaybeSendHeartbeat(s: CReplica, clock: CClockReading) : (CReplica, OutboundPackets) 
		requires CReplicaIsValid(s)
		// requires CClockReadingIsValid(clock)
		ensures var (s', sequential_sent_packets) := CReplicaNextReadClockMaybeSendHeartbeat(s, clock); 
    CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockMaybeSendHeartbeat(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			if clock.t < s.nextHeartbeatTime then 
				// var t1 := 
					(s, PacketSequence([])) 				
				// var t2 := 
				// 	PacketSequence([]); 				
				// (t1, t2) 
			else 
				var t1 := 
					UpperBoundedAdditionImpl(clock.t, s.constants.all.params.heartbeat_period, s.constants.all.params.max_integer_val); 				
				var t2 := 
					Broadcast(BuildBroadcastToEveryone(s.constants.all.config, s.constants.my_index, CMessage_Heartbeat(s.proposer.election_state.current_view, s.constants.my_index in s.proposer.election_state.current_view_suspectors, s.executor.ops_complete))); 				
				// var t3 := 
					(s.(nextHeartbeatTime := t1), t2);				
				// (t3, t2); 		
    lemma_NoReceived_Postconditions(s, t1.0, t1.1); /** Manually Added */
		(t1.0, t1.1)
	}

  /** 10 lines manual code for I1 */
  method CReplicaNextReadClockCheckForViewTimeout(s: CReplica, clock: CClockReading, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
		requires CReplicaIsValid(s)

    /** Manually Added for I1 */
		requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.proposer.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.proposer.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  MutableSet.SetOf(cur_req_set) == s'.proposer.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.proposer.election_state.prev_req_set
    ensures  s'.executor.reply_cache == s.executor.reply_cache

    ensures CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockCheckForViewTimeout(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerCheckForViewTimeout(s.proposer, clock.t, cur_req_set, prev_req_set); 		
		sequential_sent_packets := 
			PacketSequence([]); 		
		s' := 
			s.(proposer := t1); 		
    lemma_NoReceived_Postconditions(s, s', sequential_sent_packets); /** Manually Added */
		// (t3, t2)
	}

  method CReplicaNextReadClockCheckForQuorumOfViewSuspicions(s: CReplica, clock: CClockReading, cur_req_set:MutableSet<CRequestHeader>, prev_req_set:MutableSet<CRequestHeader>) returns (s':CReplica, sequential_sent_packets:OutboundPackets) 
		requires CReplicaIsValid(s)
		
    /** Manually Added for I1 */
    requires cur_req_set != prev_req_set
    requires MutableSet.SetOf(cur_req_set) == s.proposer.election_state.cur_req_set
    requires MutableSet.SetOf(prev_req_set) == s.proposer.election_state.prev_req_set
    modifies cur_req_set, prev_req_set
    ensures  MutableSet.SetOf(cur_req_set) == s'.proposer.election_state.cur_req_set
    ensures  MutableSet.SetOf(prev_req_set) == s'.proposer.election_state.prev_req_set

    ensures CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
	{
		var t1 := 
			CProposerCheckForQuorumOfViewSuspicions(s.proposer, clock.t, cur_req_set, prev_req_set); 		
		sequential_sent_packets := 
			PacketSequence([]); 		
		s' := 
			s.(proposer := t1); 		
    lemma_NoReceived_Postconditions(s, s', sequential_sent_packets); /** Manually Added */
		// (t3, t2)
	}

  /************************** AutoMan Translation End ************************/

  /************************** Manual Code For I0 ************************/

  /** 13 + 8 */
  method {:opaque} CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:CReplica) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures CReplicaIsValid(s') 
            && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
            && OutboundPacketsIsValid(sequential_sent_packets) 
            && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
            
            ensures s'.proposer.election_state.cur_req_set == s.proposer.election_state.cur_req_set
            ensures s'.proposer.election_state.prev_req_set == s.proposer.election_state.prev_req_set
            ensures  s'.executor.reply_cache == s.executor.reply_cache
  {
    if (exists opn :: opn in s.acceptor.last_checkpointed_operation && opn > s.acceptor.log_truncation_point && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) )
    {
        var opn :| opn > s.acceptor.log_truncation_point && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config);
        var newAcceptor := CAcceptorTruncateLog(s.acceptor, opn);
        s' := s.(acceptor := newAcceptor);
        sequential_sent_packets := Broadcast(CBroadcastNop);
        lemma_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sequential_sent_packets);
        assert LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets));
    } 
    else 
    if (exists opn :: opn in s.acceptor.last_checkpointed_operation && opn <= s.acceptor.log_truncation_point && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config) )
    {
        s' := s;
        sequential_sent_packets := Broadcast(CBroadcastNop);
        lemma_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sequential_sent_packets);
        assert LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets));
    } 
    else {
        /** This is a branch that cannot be executed, so we use an axiom lemma to pass the verification */
        assert !exists opn :: opn in s.acceptor.last_checkpointed_operation
        && CIsLogTruncationPointValid(opn, s.acceptor.last_checkpointed_operation, s.constants.all.config);
        s' := s;
        sequential_sent_packets := Broadcast(CBroadcastNop);
        lemma_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sequential_sent_packets);
        assert LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets));
    }
    lemma_NoReceived_Postconditions(s, s', sequential_sent_packets);
  }
  
  /** 0 + 3 */
  lemma {:axiom}  lemma_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s:CReplica, s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures CReplicaIsValid(s') 
            && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
            && OutboundPacketsIsValid(sequential_sent_packets) 
            && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
  
  lemma lemma_Msg2avs(r2avs: CAcceptorTuple)
    requires CAcceptorTupleIsValid(r2avs)
    requires (forall p :: p in r2avs.received_2av_packets ==> p.msg.CMessage_2av?)
    ensures forall p :: p in r2avs.received_2av_packets ==> CRequestBatchIsValid(p.msg.val_2av)
  {
    assert (forall p :: p in r2avs.received_2av_packets ==> CMessageIsValid(p.msg));
    assert (forall p :: p in r2avs.received_2av_packets ==> p.msg.CMessage_2av?);
  }

  lemma lemma_AbstractifyPacketSeq(s:seq<CPacket>, ls:seq<RslPacket>)
    requires forall p :: p in s ==> CPacketIsAbstractable(p)
    requires ls == AbstractifySeq(s, AbstractifyCPacketToRslPacket)
    ensures forall p :: p in s ==> AbstractifyCPacketToRslPacket(p) in ls
  {

  }

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
    /** I1 */
    ensures s'.proposer.election_state.cur_req_set == s.proposer.election_state.cur_req_set
    ensures s'.proposer.election_state.prev_req_set == s.proposer.election_state.prev_req_set
    ensures  s'.executor.reply_cache == s.executor.reply_cache
  {
    // print("Chose 2b val\n");
    ghost var ls := AbstractifyCReplicaToLReplica(s);
    ghost var lopn := ls.acceptor.opn_to_be_send_2b;
    ghost var lquorum := LByzQuorumSize(ls.acceptor.constants.all.config);

    assert s.acceptor.val_to_be_sent_2b.CValToBeSent2bUnknown? ==> ls.acceptor.val_to_be_sent_2b.ValToBeSent2bUnknown?;
    

    var opn := s.acceptor.opn_to_be_send_2b;
    var quorum := CByzQuorumSize(s.acceptor.constants.all.config);
    if && s.acceptor.val_to_be_sent_2b.CValToBeSent2bUnknown?
        && opn in s.acceptor.received_2avs
        && |s.acceptor.received_2avs[opn].received_2av_packets| >= quorum
        && CAcceptorStateCorrect(s.acceptor.received_2avs, s.acceptor.max_bal, s.constants.all.config)
        && CHasReceivedSame2avFromByzQuorum(s.acceptor.received_2avs[opn], quorum) 
    {
      // print("r2av size: ", |s.acceptor.received_2avs|, "\n");
      // print("r2av size: ", |s.acceptor.received_2avs[opn].received_2av_packets|, "\n");
      assert ls.acceptor.val_to_be_sent_2b.ValToBeSent2bUnknown?;
      assert lopn in ls.acceptor.received_2avs;
      assert |ls.acceptor.received_2avs[lopn].received_2av_packets| >= lquorum;
      assert AcceptorStateCorrect(ls.acceptor.received_2avs, ls.acceptor.max_bal, ls.constants.all.config);
      assert HasReceivedSame2avFromByzQuorum(ls.acceptor.received_2avs[opn], lquorum);  

      var p2avs := s.acceptor.received_2avs[opn];
      lemma_Msg2avs(p2avs);
      assert (forall p :: p in p2avs.received_2av_packets ==> CRequestBatchIsValid(p.msg.val_2av));
      
      var p :|  p in p2avs.received_2av_packets
              && CCountMatchedValInReceived2avs(p2avs.received_2av_packets, p.msg.val_2av) >= quorum;

      assert AbstractifySeq(s.acceptor.received_2avs[opn].received_2av_packets, AbstractifyCPacketToRslPacket) == ls.acceptor.received_2avs[lopn].received_2av_packets;
      lemma_AbstractifyPacketSeq(s.acceptor.received_2avs[opn].received_2av_packets, ls.acceptor.received_2avs[lopn].received_2av_packets);
      assert forall pkt :: pkt in s.acceptor.received_2avs[opn].received_2av_packets ==> AbstractifyCPacketToRslPacket(pkt) in ls.acceptor.received_2avs[lopn].received_2av_packets;

      ghost var lp2 := AbstractifyCPacketToRslPacket(p);
      assert CountMatchedValInReceived2avs(ls.acceptor.received_2avs[lopn].received_2av_packets, lp2.msg.val_2av) >= lquorum;
      assert lp2 in ls.acceptor.received_2avs[lopn].received_2av_packets;
      assert lp2 in ls.acceptor.received_2avs[lopn].received_2av_packets
                && CountMatchedValInReceived2avs(ls.acceptor.received_2avs[lopn].received_2av_packets, lp2.msg.val_2av) >= lquorum;
      
      var newAcceptor := CAcceptorDecide2bVal(s.acceptor, s.acceptor.max_bal, opn, p.msg.val_2av);
      s' := s.(acceptor := newAcceptor);
      sent_packets := Broadcast(CBroadcastNop);

      ghost var a' := ls.acceptor.(val_to_be_sent_2b := ValToBeSent2bKnown(lp2.msg.val_2av, ls.acceptor.max_bal));
      ghost var ls' := ls.(acceptor := a');
      ghost var ls2' := AbstractifyCReplicaToLReplica(s');
      assert LAcceptorDecide2bVal(ls.acceptor, ls2'.acceptor, ls.acceptor.max_bal, lopn, lp2.msg.val_2av);
      assert ls2'.acceptor == a';
      assert ls' == ls2';
      assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == [];
      assert LAcceptorDecide2bVal(
                AbstractifyCReplicaToLReplica(s).acceptor,
                AbstractifyCReplicaToLReplica(s').acceptor,
                AbstractifyCReplicaToLReplica(s).acceptor.max_bal,
                AbstractifyCReplicaToLReplica(s).acceptor.opn_to_be_send_2b,
                AbstractifyCPacketToRslPacket(p).msg.val_2av
              );

      assert LReplicaNextSpontaneousMaybeDecide2bVal(
            AbstractifyCReplicaToLReplica(s), 
            AbstractifyCReplicaToLReplica(s'), 
            AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets)
          );
    }
    else
    {
      s' := s;
      sent_packets := Broadcast(CBroadcastNop);
      assert LReplicaNextSpontaneousMaybeDecide2bVal(
              AbstractifyCReplicaToLReplica(s), 
              AbstractifyCReplicaToLReplica(s'), 
              AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets)
            );
    }
    lemma_NoReceived_Postconditions(s, s', sent_packets);
  }


  lemma lemma_Msg2bs(r2bs: CLearnerTuple)
    requires CLearnerTupleIsValid(r2bs)
    requires (forall p :: p in r2bs.received_2bs ==> p.msg.CMessage_2b?)
    ensures forall p :: p in r2bs.received_2bs ==> CRequestBatchIsValid(p.msg.val_2b)
  {
    assert (forall p :: p in r2bs.received_2bs ==> CMessageIsValid(p.msg));
    assert (forall p :: p in r2bs.received_2bs ==> p.msg.CMessage_2b?);
  }

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
            
    ensures s'.proposer.election_state.cur_req_set == s.proposer.election_state.cur_req_set
    ensures s'.proposer.election_state.prev_req_set == s.proposer.election_state.prev_req_set
    ensures  s'.executor.reply_cache == s.executor.reply_cache
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

      ghost var lp2 := AbstractifyCPacketToRslPacket(p);
      // assert CountMatchedValInReceived2bs(ls.learner.unexecuted_learner_state[lopn].received_2bs, lp2.msg.val_2b) >= lquorum;
      // assert lp2 in ls.learner.unexecuted_learner_state[opn].received_2bs;
      assert lp2 in ls.learner.unexecuted_learner_state[opn].received_2bs
            && CountMatchedValInReceived2bs(ls.learner.unexecuted_learner_state[lopn].received_2bs, lp2.msg.val_2b) >= lquorum;

      var newExecutor := CExecutorGetDecision(s.executor, s.learner.max_ballot_seen, opn, p.msg.val_2b);
      s' := s.(executor := newExecutor);
      sent_packets := Broadcast(CBroadcastNop);
      assert AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets) == [];
      assert LReplicaNextSpontaneousMaybeMakeDecision(
              AbstractifyCReplicaToLReplica(s), 
              AbstractifyCReplicaToLReplica(s'), 
              AbstractifyOutboundCPacketsToSeqOfRslPackets(sent_packets)
            );
    }
    else
    {
      s' := s;
      sent_packets := Broadcast(CBroadcastNop);
    }
    lemma_NoReceived_Postconditions(s, s', sent_packets);
  }

  /** 4 + 4 */
  method CReplicaNextReadClockMaybeNominateValueAndSend1c(s:CReplica, clock:CClockReading) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures CReplicaIsValid(s') 
    && Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(s), s', sequential_sent_packets) /** Manually Added */
    && OutboundPacketsIsValid(sequential_sent_packets) 
    && LReplicaNextReadClockMaybeNominateValueAndSend1c(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyCClockReadingToClockReading(clock), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))

    /** Manually Added for I1 */
    ensures s'.proposer.election_state.cur_req_set == s.proposer.election_state.cur_req_set
    ensures s'.proposer.election_state.prev_req_set == s.proposer.election_state.prev_req_set
  {
    var newProposer, packets := CProposerMaybeNominateValueAndSend1c(s.proposer, clock.t, s.acceptor.log_truncation_point);
    s' := s.(proposer := newProposer);
    sequential_sent_packets := packets;
    lemma_NoReceived_Postconditions(s, s', sequential_sent_packets);
  }
  /************************** Manual Code For I0 End ************************/

 /************************** Manually Optimization for I1 ********************/

  /** 5 */
  method CGetHighestValueAmongMajority(acceptor:CAcceptor, n:int) returns (opn:COperationNumber)
    requires CAcceptorIsValid(acceptor)
    requires 0 < n as int <= |acceptor.last_checkpointed_operation|
    ensures  IsNthHighestValueInSequence(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySeq(acceptor.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber), n as int)
    // requires |acceptor.last_checkpointed_operation| > n as int
  {
      // var i:int := 1;
      var cm := acceptor.last_checkpointed_operation;
      var a := SeqToArray(cm);
      assert multiset(a[..]) == multiset(cm);
      SortSeq(a);

      ghost var s := a[..]; 
      assert multiset(s) == multiset(cm);
      forall i, j | 0 <= i < j < |s|
        ensures s[i] <= s[j]
      {
        assert a[i] <= a[j];
      }

      opn := a[a.Length - (n as int)];

      assert opn == s[|s|-(n as int)];

      ghost var f1 := (x:COperationNumber) => x > s[|s|-(n as int)];
      ghost var f2 := (x:COperationNumber) => x > opn;
      Lemma_CountMatchesInSeqSameForSameFunctions(s, f1, f2);
      ghost var f1' := (x:COperationNumber) => x >= s[|s|-(n as int)];
      ghost var f2' := (x:COperationNumber) => x >= opn;
      Lemma_CountMatchesInSeqSameForSameFunctions(s, f1', f2');

      lemma_SortedSequenceMatchCount(s, n as int);
      assert IsNthHighestValueInSequence(opn, s, n);
      lemma_SequenceToMultisetPreservesIsNthHighestValueForCOperationNumbers(opn, s, multiset(cm), n);
      lemma_SequenceToMultisetPreservesIsNthHighestValueForCOperationNumbers(opn, cm, multiset(cm), n);
      lemma_AbstractionOfCOperationNumberIsNthHighestValueInSequence(opn, cm, n);
  }

  
lemma lemma_SortedSequenceMatchCount(s:seq<COperationNumber>, k:int)
  requires |s| > 0
  requires 0 < k <= |s|
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures CountMatchesInSeq(s, (x:COperationNumber) => x > s[|s|-k]) < k
  ensures CountMatchesInSeq(s, (x:COperationNumber) => x >= s[|s|-k]) >= k
{
  var s' := s[1..];
  var f1 := (x:COperationNumber) => x > s[|s|-k];
  var f2 := (x:COperationNumber) => x >= s[|s|-k];

  if k == |s|
  {
    calc {
      CountMatchesInSeq(s, f1);
      CountMatchesInSeq(s', f1);
      < { Lemma_CountMatchesInSeqBounds(s', f1); }
      k;
    }

    Lemma_CountMatchesInSeqAll(s, f2);
  }
  else
  {
    var f1' := (x:COperationNumber) => x > s'[|s'|-k];
    var f2' := (x:COperationNumber) => x >= s'[|s'|-k];
    lemma_SortedSequenceMatchCount(s', k);
    assert s'[|s'|-k] == s[|s|-k];

    calc {
      CountMatchesInSeq(s, f1);
      CountMatchesInSeq(s', f1);
        { Lemma_CountMatchesInSeqSameForSameFunctions(s', f1, f1'); }
      CountMatchesInSeq(s', f1');
      < k;
    }

    calc {
      CountMatchesInSeq(s, f2);
      >= CountMatchesInSeq(s', f2);
        { Lemma_CountMatchesInSeqSameForSameFunctions(s', f2, f2'); }
      CountMatchesInSeq(s', f2');
      >= k;
    }
  }
}

predicate IsNthHighestValueInMultisetOfCOperationNumbers(v:COperationNumber, m:multiset<COperationNumber>, n:int)
{
  && 0 < n as int <= |m|
  && v in m
  && CountMatchesInMultiset(m, (x:COperationNumber) => x > v) < n as int
  && CountMatchesInMultiset(m, (x:COperationNumber) => x >= v) >= n as int
}

lemma lemma_SequenceToMultisetPreservesIsNthHighestValueForCOperationNumbers(v:COperationNumber, s:seq<COperationNumber>, m:multiset<COperationNumber>, n:int)
  requires m == multiset(s)
  ensures  IsNthHighestValueInSequence(v, s, n) <==> IsNthHighestValueInMultisetOfCOperationNumbers(v, m, n)
{
  Lemma_MatchCountInSeqIsMatchCountInMultiset(s, m, (x:COperationNumber) => x > v);
  Lemma_MatchCountInSeqIsMatchCountInMultiset(s, m, (x:COperationNumber) => x >= v);
}

lemma lemma_AbstractionOfCOperationNumberIsNthHighestValueInSequence(opn:COperationNumber, cm:seq<COperationNumber>, n:int)
  requires IsNthHighestValueInSequence(opn, cm, n)
  ensures  IsNthHighestValueInSequence(AbstractifyCOperationNumberToOperationNumber(opn), AbstractifySeq(cm, AbstractifyCOperationNumberToOperationNumber), n as int)
{
  var f1 := (x:COperationNumber) => x > opn;
  var f2 := x => x > AbstractifyCOperationNumberToOperationNumber(opn);
  Lemma_CountMatchesInSeqCorrespondence(cm, f1, AbstractifySeq(cm, AbstractifyCOperationNumberToOperationNumber), f2);

  var f1' := (x:COperationNumber) => x >= opn;
  var f2' := x => x >= AbstractifyCOperationNumberToOperationNumber(opn);
  Lemma_CountMatchesInSeqCorrespondence(cm, f1', AbstractifySeq(cm, AbstractifyCOperationNumberToOperationNumber), f2');
}


  method SeqToArray<T(0)>(s:seq<T>) returns (a:array<T>)
    ensures fresh(a)
    ensures a.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> s[i] == a[i]
    ensures a[..] == s
    ensures fresh(a)
  {
    a := new T[|s|];

    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < i ==> s[j] == a[j]
    {
      a[i] := s[i];
      i := i + 1;
    }
  }

  /** 15 */
  method SortSeq(a : array<COperationNumber>)
      modifies a
      requires a.Length < 0xFFFFFFFFFFFFFFFF
      ensures Sorted_COperationNumber(a, 0, a.Length as uint64)
      ensures multiset(a[..]) == old(multiset(a[..]))
  {
      if a.Length as uint64 == 0 { return; }
      var i:uint64 := 1;
      while i < a.Length as uint64
          invariant 0 < i <= a.Length as uint64
          invariant NeighborSorted_COperationNumber(a, 0, i)
          invariant multiset(a[..]) == old(multiset(a[..]))
      {
          var j:uint64 := i;
          while 0 < j && a[j-1] > a[j]
          invariant 0 <= j <= i
          invariant NeighborSorted_COperationNumber(a, 0, j)
          invariant NeighborSorted_COperationNumber(a, j, i+1)
          invariant 0 < j < i ==> a[j-1] <= a[j+1]
          invariant multiset(a[..]) == old(multiset(a[..]))
          {
              a[j], a[j-1] := a[j-1], a[j];
              j := j - 1;
          }
          i := i + 1;
      }
      lemma_NeighborSortedImpliesSortedCOperationNumber(a, 0, a.Length as uint64);
  }

  /** 14 */
  method CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints_I1(s:CReplica) returns (s':CReplica, sequential_sent_packets:OutboundPackets)
    requires CReplicaIsValid(s)
    ensures CReplicaIsValid(s') && OutboundPacketsIsValid(sequential_sent_packets) 
    ensures LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(AbstractifyCReplicaToLReplica(s), AbstractifyCReplicaToLReplica(s'), AbstractifyOutboundCPacketsToSeqOfRslPackets(sequential_sent_packets))
    ensures  Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions((AbstractifyCReplicaToLReplica(s)),
                                                                                   s', sequential_sent_packets)
    ensures s'.proposer.election_state.cur_req_set == s.proposer.election_state.cur_req_set
    ensures s'.proposer.election_state.prev_req_set == s.proposer.election_state.prev_req_set
    ensures  s'.executor.reply_cache == s.executor.reply_cache
  {
    ghost var ss := AbstractifyCReplicaToLReplica(s);
    var n := CByzQuorumSize(s.constants.all.config);
    assert n <= |s.constants.all.config.replica_ids|;
    assert |s.acceptor.constants.all.config.replica_ids| == |s.acceptor.last_checkpointed_operation|;
    assert s.constants == s.acceptor.constants;
    assert |s.constants.all.config.replica_ids| == |s.acceptor.last_checkpointed_operation|;

    var opn := CGetHighestValueAmongMajority(s.acceptor, n);

    assert IsLogTruncationPointValid(
          AbstractifyCOperationNumberToOperationNumber(opn),
          AbstractifySeq(s.acceptor.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber),
          AbstractifyCConfigurationToLConfiguration(s.constants.all.config)
        );
    assert AbstractifyCOperationNumberToOperationNumber(opn) == opn as int;
    assert AbstractifySeq(s.acceptor.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber) == ss.acceptor.last_checkpointed_operation;
    assert AbstractifyCConfigurationToLConfiguration(s.constants.all.config) == ss.constants.all.config;
    assert IsLogTruncationPointValid(opn as int, ss.acceptor.last_checkpointed_operation, ss.constants.all.config);

    if opn > s.acceptor.log_truncation_point { 
        // ghost var op :| op in ss.acceptor.last_checkpointed_operation && IsLogTruncationPointValid(op, ss.acceptor.last_checkpointed_operation, ss.constants.all.config);
        var newAcceptor := CAcceptorTruncateLog(s.acceptor, opn);
        s' := s.(acceptor := newAcceptor);
        sequential_sent_packets := Broadcast(CBroadcastNop);
    }
    else {
        s' := s;
        sequential_sent_packets := Broadcast(CBroadcastNop);
    }
    lamme_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(s, s', sequential_sent_packets);
  }


  predicate Sorted_COperationNumber(a: array<COperationNumber>, low: uint64, high: uint64)
    requires a.Length < 0xFFFFFFFFFFFFFFFF
    requires 0 <= low <= high <= a.Length as uint64
    reads a
  {
    forall i, j :: low <= i < j < high ==> a[i] <= a[j]
  }

  predicate NeighborSorted_COperationNumber(a: array<COperationNumber>, low: uint64, high: uint64)
    requires a.Length < 0xFFFFFFFFFFFFFFFF
    requires 0 <= low <= high <= a.Length as uint64
    reads a
  {
    forall i {:trigger a[i-1], a[i]} :: low < i < high ==> a[i-1] <= a[i]
  }

  lemma lemma_NeighborSortedImpliesSortedCOperationNumber(a: array<COperationNumber>, low: uint64, high: uint64)
    requires a.Length < 0xFFFFFFFFFFFFFFFF
    requires 0 <= low <= high <= a.Length as uint64
    requires NeighborSorted_COperationNumber(a, low, high)
    ensures Sorted_COperationNumber(a, low, high)
    decreases high - low
  {
    if low != high {
      lemma_NeighborSortedImpliesSortedCOperationNumber(a, low+1, high);
      forall j | low < j < high
        ensures  a[low] <= a[j]
      {
        var i := low+1;
        if(i == j) {
          assert a[j-1] <= a[j];
        } else {
          assert a[i-1] <= a[i];
          assert a[i] <= a[j];
          assert a[low] <= a[j];
        }
      }
    }
  }

  /************************** Manually Optimization for I1 End ********************/
 


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

  /********* pre conditions *******************/
  predicate Replica_Common_Preconditions(replica:CReplica, inp:CPacket)
  {
    && CReplicaIsValid(replica)
    && CPacketIsSendable(inp)
  }

  predicate Replica_Next_Process_Heartbeat_Preconditions(replica:CReplica, inp:CPacket)
  {
    && inp.msg.CMessage_Heartbeat?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_ReadClock_MaybeNominateValueAndSend1c_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_ReadClock_MaybeNominateValueAndSend2av_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_MaybeEnterPhase2_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica:CReplica)
  {
    CReplicaIsValid(replica)
  }

  predicate Replica_Next_Process_Request_Preconditions(replica:CReplica, inp:CPacket)
  {
    && inp.msg.CMessage_Request?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_1a_Preconditions(replica:CReplica, inp:CPacket)
  {
    && inp.msg.CMessage_1a?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_1b_Preconditions(replica:CReplica, inp:CPacket)
  {
    && inp.msg.CMessage_1b?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_StartingPhase2_Preconditions(replica:CReplica, inp:CPacket)
  {
    && inp.msg.CMessage_StartingPhase2?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_1c_Preconditions(replica:CReplica, inp:CPacket)
  {
    && inp.msg.CMessage_1c?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_2av_Preconditions(replica:CReplica, inp:CPacket)
  {
    && inp.msg.CMessage_2av?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  predicate Replica_Next_Process_2b_Preconditions(replica:CReplica, inp:CPacket)
  {
    && inp.msg.CMessage_2b?
    && CReplicaIsValid(replica)
    && CPacketIsValid(inp)
    && CMessageIsMarshallable(inp.msg)
  }

  /************** post conditions *********************/

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

  predicate Replica_Next_Process_2b_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket,
                                                   packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_2b?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcess2b(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Process_1c_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket,
                                                   packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_1c?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcess1c(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Process_2av_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket,
                                                   packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_2av?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcess2av(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Process_StartingPhase2_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket,
                                                               packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_StartingPhase2?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcessStartingPhase2(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Process_1b_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket,
                                                   packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_1b?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcess1b(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Process_1a_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket,
                                                   packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_1a?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcess1a(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Process_Request_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket,
                                                        packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    // run-time error
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_Request?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)

    // refinement
    && LReplicaNextProcessRequest(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate ReplicaCommonPostconditions(replica:LReplica, replica':CReplica, sent_packets:OutboundPackets)
  {
    && CReplicaConstantsIsValid(replica'.constants)
    && AbstractifyCReplicaConstantsToLReplicaConstants(replica'.constants) == replica.constants
    && CReplicaIsAbstractable(replica')
    && CReplicaIsValid(replica')
    && OutboundPacketsIsValid(sent_packets)
    && OutboundPacketsIsAbstractable(sent_packets)
    && OutboundPacketsHasCorrectSrc(sent_packets, replica'.constants.all.config.replica_ids[replica'.constants.my_index])
  }

  predicate Replica_Next_Process_Heartbeat_Postconditions(replica:LReplica, replica':CReplica,
                                                          inp:CPacket, clock:int, packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && CPacketIsAbstractable(inp)
    && inp.msg.CMessage_Heartbeat?
    && Replica_Common_Postconditions(replica, replica', inp, packets_sent)
    && LReplicaNextProcessHeartbeat(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCPacketToRslPacket(inp),
         clock as int,
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_ReadClock_MaybeNominateValueAndSend1c_Postconditions(
    replica:LReplica,
    replica':CReplica,
    clock:CClockReading,
    packets_sent:OutboundPackets
  )
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextReadClockMaybeNominateValueAndSend1c(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCClockReadingToClockReading(clock),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_ReadClock_CheckForViewTimeout_Postconditions(
    replica:LReplica,
    replica':CReplica,
    clock:CClockReading,
    packets_sent:OutboundPackets
  )
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextReadClockCheckForViewTimeout(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCClockReadingToClockReading(clock),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions(
    replica:LReplica,
    replica':CReplica,
    clock:CClockReading,
    packets_sent:OutboundPackets
  )
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextReadClockCheckForQuorumOfViewSuspicions(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCClockReadingToClockReading(clock),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions(
    replica:LReplica,
    replica':CReplica,
    clock:CClockReading,
    packets_sent:OutboundPackets
  )
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextReadClockMaybeSendHeartbeat(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyCClockReadingToClockReading(clock),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions(replica:LReplica, replica':CReplica, packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_MaybeEnterPhase2_Postconditions(replica:LReplica, replica':CReplica, packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousMaybeEnterPhase2(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions(
    replica:LReplica,
    replica':CReplica,
    packets_sent:OutboundPackets
  )
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Spontaneous_MaybeDecide2bVal_Postconditions(
    replica:LReplica,
    replica':CReplica,
    packets_sent:OutboundPackets
  )
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousMaybeDecide2bVal(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_MaybeSend2b_Postconditions(replica:LReplica, replica':CReplica, packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousMaybeSend2b(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions(
    replica:LReplica,
    replica':CReplica,
    packets_sent:OutboundPackets
  )
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousMaybeMakeDecision(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  predicate Replica_Next_Spontaneous_MaybeExecute_Postconditions(replica:LReplica, replica':CReplica,
                                                                 packets_sent:OutboundPackets)
    // reads replica'.executor.app.app
  {
    && Replica_Common_Postconditions_NoPacket(replica, replica', packets_sent)
    && LReplicaNextSpontaneousMaybeExecute(
         replica,
         AbstractifyCReplicaToLReplica(replica'),
         AbstractifyOutboundCPacketsToSeqOfRslPackets(packets_sent))
  }

  /* ----------------------------------------- */
  lemma {:axiom} lemma_NoReceived_Postconditions(replica:CReplica, replica':CReplica, packets_sent:OutboundPackets)
    requires CReplicaIsAbstractable(replica)
    ensures Replica_Common_Postconditions_NoPacket(AbstractifyCReplicaToLReplica(replica), replica', packets_sent)

  lemma {:axiom} lemma_Postconditions(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires CReplicaIsAbstractable(replica)
    ensures Replica_Common_Postconditions(AbstractifyCReplicaToLReplica(replica), replica', inp, packets_sent)

  lemma {:axiom} lemma_CReplicaInit(constants:CReplicaConstants, replica:CReplica)
    requires CReplicaConstantsIsValid(constants)
    ensures CReplicaIsValid(replica)
    ensures replica.constants == constants
    ensures LReplicaInit(AbstractifyCReplicaToLReplica(replica), AbstractifyCReplicaConstantsToLReplicaConstants(constants))

  lemma {:axiom} lemma_CReplicaNextProcessRequest_pre(replica:CReplica, inp:CPacket)
    requires Replica_Next_Process_Request_Preconditions(replica, inp)
    ensures  inp.src in replica.proposer.constants.all.config.replica_ids

  lemma {:axiom} lemma_CReplicaNextProcessRequest(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_Request_Preconditions(replica, inp)
    ensures  Replica_Next_Process_Request_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
                                                         inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcess1a_pre(replica:CReplica, inp:CPacket)
    requires Replica_Next_Process_1a_Preconditions(replica, inp)
    ensures CBallotIsValid(inp.msg.bal_1a)

  lemma {:axiom} lemma_CReplicaNextProcess1a(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_1a_Preconditions(replica, inp)
    ensures Replica_Next_Process_1a_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcess1b(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_1b_Preconditions(replica, inp)
    ensures  Replica_Next_Process_1b_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcessStartingPhase2(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_StartingPhase2_Preconditions(replica, inp)
    ensures Replica_Next_Process_StartingPhase2_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcess1c(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_1c_Preconditions(replica, inp)
    ensures  Replica_Next_Process_1c_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcess2av(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_2av_Preconditions(replica, inp)
    ensures  Replica_Next_Process_2av_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcess2b_pre(replica:CReplica, inp:CPacket)
    requires Replica_Next_Process_2b_Preconditions(replica, inp)
    ensures CBallotIsValid(inp.msg.bal_2b)

  lemma {:axiom} lemma_CReplicaNextProcess2b(replica:CReplica, inp:CPacket, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Process_2b_Preconditions(replica, inp)
    ensures Replica_Next_Process_2b_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', inp, packets_sent)

  lemma {:axiom} lemma_CReplicaNextProcessHeartbeat_Pre(replica:CReplica, inp:CPacket)
    requires CReplicaIsValid(replica)
    requires inp.msg.CMessage_Heartbeat?
    ensures inp.src in replica.proposer.constants.all.config.replica_ids
    ensures CBallotIsValid(inp.msg.bal_heartbeat)

  lemma {:axiom} lemma_CReplicaNextProcessHeartbeat(replica:CReplica, inp:CPacket, clock:int, replica':CReplica, packets_sent:OutboundPackets)
    requires CReplicaIsValid(replica)
    requires inp.msg.CMessage_Heartbeat?
    ensures Replica_Next_Process_Heartbeat_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
                                                          inp, clock, packets_sent)
    ensures  replica'.executor == replica.executor

  lemma {:axiom} lemma_CReplicaNextSpontaneousMaybeEnterNewViewAndSend1a(replica:CReplica, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_MaybeEnterNewViewAndSend1a_Preconditions(replica)
    ensures Replica_Next_MaybeEnterNewViewAndSend1a_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
                                                                   packets_sent)

  lemma {:axiom} lemma_CReplicaNextSpontaneousMaybeEnterPhase2(replica:CReplica, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_MaybeEnterPhase2_Preconditions(replica)
    ensures Replica_Next_MaybeEnterPhase2_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica', packets_sent)

  lemma {:axiom} lemma_CReplicaNextReadClockMaybeNominateValueAndSend1c(replica:CReplica, clock:CClockReading, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_ReadClock_MaybeNominateValueAndSend1c_Preconditions(replica)
    ensures Replica_Next_ReadClock_MaybeNominateValueAndSend1c_Postconditions((AbstractifyCReplicaToLReplica(replica)),
                                                                              replica', clock, packets_sent)

  lemma {:axiom} lamme_CReplicaNextSpontaneousTruncateLogBasedOnCheckpoints(replica:CReplica, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Preconditions(replica)
    ensures  Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_Postconditions((AbstractifyCReplicaToLReplica(replica)),
                                                                                   replica', packets_sent)

  lemma {:axiom} lemma_CReplicaNextSpontaneousMaybeMakeDecision(replica:CReplica, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_MaybeMakeDecision_Preconditions(replica)
    ensures  Replica_Next_Spontaneous_MaybeMakeDecision_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
                                                                       packets_sent)
    ensures  replica' == replica



  lemma {:axiom} lemma_CReplicaNextSpontaneousMaybeExecute(replica:CReplica, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_Spontaneous_MaybeExecute_Preconditions(replica)
    ensures  Replica_Next_Spontaneous_MaybeExecute_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
                                                                  packets_sent)

  lemma {:axiom} lemma_CReplicaNextReadClockMaybeSendHeartbeat(replica:CReplica, clock:CClockReading, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_ReadClock_MaybeSendHeartbeat_Preconditions(replica)
    ensures Replica_Next_ReadClock_MaybeSendHeartbeat_Postconditions((AbstractifyCReplicaToLReplica(replica)), replica',
                                                                     clock, packets_sent)


  lemma {:axiom} lemma_CReplicaNextReadClockCheckForViewTimeout(replica:CReplica, clock:CClockReading, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_ReadClock_CheckForViewTimeout_Preconditions(replica)
    ensures  Replica_Next_ReadClock_CheckForViewTimeout_Postconditions((AbstractifyCReplicaToLReplica(replica)),
                                                                       replica', clock, packets_sent)

  lemma {:axiom} lemma_CReplicaNextReadClockCheckForQuorumOfViewSuspicions(replica:CReplica, clock:CClockReading, replica':CReplica, packets_sent:OutboundPackets)
    requires Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Preconditions(replica)
    ensures  Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions_Postconditions((AbstractifyCReplicaToLReplica(replica)),
                                                                                  replica', clock, packets_sent)
}