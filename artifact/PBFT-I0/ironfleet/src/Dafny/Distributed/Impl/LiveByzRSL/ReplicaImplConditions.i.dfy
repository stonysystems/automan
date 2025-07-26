include "../ByzRSL/ReplicaImpl.i.dfy"
include "../ByzRSL/CMessage.i.dfy"
include "../ByzRSL/CClockReading.i.dfy"
include "PacketParsing.i.dfy"
include "../ByzRSL/CConstants.i.dfy"

module LiveBysRSL_ReplicaImplConditions_i {
    import opened LiveByzRSL__ReplicaModel_i
    import opened LiveByzRSL__Replica_i
    import opened LiveByzRSL__CMessage_i
    import opened LiveByzRSL__CClockReading_i
    import opened LiveByzRSL__PacketParsing_i
    import opened LiveByzRSL__ConstantsState_i
  /* ----------------------------------------- */

  // predicate ConstantsStayConstant_Replica(replica:LReplica, replica':CReplica)
  //   requires CReplicaConstantsIsAbstractable(replica'.constants)
  // {
  //   && AbstractifyCReplicaConstantsToLReplicaConstants(replica'.constants) == replica.constants
  //   && replica.constants == replica.proposer.constants
  //   && replica.constants == replica.acceptor.constants
  //   && replica.constants == replica.learner.constants
  //   && replica.constants == replica.executor.constants
  //   && replica'.constants == replica'.proposer.constants
  //   && replica'.constants == replica'.acceptor.constants
  //   && replica'.constants == replica'.learner.constants
  //   && replica'.constants == replica'.executor.constants
  // }

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

  // predicate Replica_Common_Postconditions(replica:LReplica, replica':CReplica, inp:CPacket, packets_sent:OutboundPackets)
  // {
  //   && CReplicaConstantsIsValid(replica'.constants)
  //   && CPacketIsSendable(inp)
  //   && CReplicaIsAbstractable(replica')
  //   && ConstantsStayConstant_Replica(replica, replica')
  //   && CReplicaIsValid(replica')
  //   && OutboundPacketsIsValid(packets_sent)
  //   && OutboundPacketsHasCorrectSrc(packets_sent, replica'.constants.all.config.replica_ids[replica'.constants.my_index])
  //   && OutboundPacketsIsAbstractable(packets_sent)
  // }

  //   predicate Replica_Common_Postconditions_NoPacket(replica:LReplica, replica':CReplica, packets_sent:OutboundPackets)
  // {
  //   && CReplicaConstantsIsValid(replica'.constants)
  //   && CReplicaIsAbstractable(replica')
  //   && ConstantsStayConstant_Replica(replica, replica')
  //   && CReplicaIsValid(replica')
  //   && OutboundPacketsIsValid(packets_sent)
  //   && OutboundPacketsHasCorrectSrc(packets_sent, replica'.constants.all.config.replica_ids[replica'.constants.my_index])
  //   && OutboundPacketsIsAbstractable(packets_sent)
  // }

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

}