include "../../Protocol/ByzRSL/Message.i.dfy"
include "../../Protocol/ByzRSL/Environment.i.dfy"
include "../../Protocol/ByzRSL/Broadcast.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../ByzRSL/CMessage.i.dfy"
include "../ByzRSL/AppInterface.i.dfy"

module LiveByzRSL__CMessageRefinements_i {
  import opened Native__Io_s
  import opened Native__NativeTypes_i
  import opened Concrete_NodeIdentity_i
  import opened LiveByzRSL__AppInterface_i
  import opened LiveByzRSL__CMessage_i
  import opened LiveByzRSL__CTypes_i
  import opened LiveByzRSL__Message_i
  import opened LiveByzRSL__Environment_i
  import opened LiveByzRSL__Broadcast_i
  import opened Common__NodeIdentity_i
  import opened Common__UdpClient_i
  import opened Environment_s
  import opened Collections__Sets_i
  import opened GenericRefinement_i
   

  function AbstractifyCMessageToRslPacket(sentTo:EndPoint, sentFrom:EndPoint, msg:CMessage) : RslPacket
    requires CMessageIsAbstractable(msg)
    requires EndPointIsValidIPV4(sentTo)
    requires EndPointIsValidIPV4(sentFrom)
  {
    LPacket(AbstractifyEndPointToNodeIdentity(sentTo), AbstractifyEndPointToNodeIdentity(sentFrom), AbstractifyCMessageToRslMessage(msg))
  }


  predicate CPacketsIsValid(cps:set<CPacket>)
  {
    forall cp :: cp in cps ==> CPacketIsValid(cp)
  }

  predicate CPacketsIsAbstractable(cps:set<CPacket>)
  {
    forall cp :: cp in cps ==> CPacketIsAbstractable(cp)
  }

  function AbstractifySetOfCPacketsToSetOfRslPackets_transparent(cps:set<CPacket>) : set<RslPacket>
    requires CPacketsIsAbstractable(cps)
    ensures forall p :: p in cps ==> AbstractifyCPacketToRslPacket(p) in AbstractifySetOfCPacketsToSetOfRslPackets_transparent(cps)
    // ensures |cps| == |AbstractifySetOfCPacketsToSetOfRslPackets_transparent(cps)|
  {
    // lemma_AbstractifyCPacketToRslPacket_injective_forall();
    // lemma_AbstractifySetOfCPacketsToSetOfRslPackets_properties(cps);
    set cp | cp in cps :: AbstractifyCPacketToRslPacket(cp)
  }

  lemma {:axiom} AbstractifyMapHasEqualSize(cps:set<CPacket>)
    requires CPacketsIsAbstractable(cps)
    ensures |cps| == |AbstractifySetOfCPacketsToSetOfRslPackets_transparent(cps)|

  function AbstractifySetOfCPacketsToSetOfRslPackets(cps:set<CPacket>) : set<RslPacket>
    requires CPacketsIsAbstractable(cps)
    ensures forall p :: p in cps ==> AbstractifyCPacketToRslPacket(p) in AbstractifySetOfCPacketsToSetOfRslPackets(cps)   // Still too trigger happy
    ensures |cps| == |AbstractifySetOfCPacketsToSetOfRslPackets(cps)|
  {
    //  set netp | netp in netps ::
    //    var net := AbstractifyCPacketToShtPacket(netp); net
    AbstractifyMapHasEqualSize(cps);
    AbstractifySetOfCPacketsToSetOfRslPackets_transparent(cps)
  }

  // lemma {:axiom} lemma_AbstractifyCPacketToRslPacket_injective(e1:CPacket, e2:CPacket)
  //   requires AbstractifyCPacketToRslPacket(e1) == AbstractifyCPacketToRslPacket(e2)
  //   ensures e1==e2
  // // {
  // // }

  // lemma lemma_AbstractifyCPacketToRslPacket_injective_forall()
  //   ensures forall e1, e2 {:trigger AbstractifyCPacketToRslPacket(e1),AbstractifyCPacketToRslPacket(e2)} ::
  //             AbstractifyCPacketToRslPacket(e1) == AbstractifyCPacketToRslPacket(e2) ==> e1 == e2;
  // {
  //   forall e1, e2 | AbstractifyCPacketToRslPacket(e1) == AbstractifyCPacketToRslPacket(e2)
  //     ensures e1 == e2
  //   {
  //     lemma_AbstractifyCPacketToRslPacket_injective(e1, e2);
  //   }
  // }

  predicate CPacketSeqIsAbstractable(cps:seq<CPacket>)
  {
    forall i :: 0 <= i < |cps| ==> CPacketIsAbstractable(cps[i])
  }

  function {:opaque} AbstractifySeqOfCPacketsToSeqOfRslPackets(cps:seq<CPacket>) : seq<RslPacket>
    requires CPacketSeqIsAbstractable(cps)
    ensures |cps| == |AbstractifySeqOfCPacketsToSeqOfRslPackets(cps)|
    ensures forall i :: 0 <= i < |cps| ==> AbstractifySeqOfCPacketsToSeqOfRslPackets(cps)[i] == AbstractifyCPacketToRslPacket(cps[i])
  {
    if |cps| == 0 then []
    else [AbstractifyCPacketToRslPacket(cps[0])] + AbstractifySeqOfCPacketsToSeqOfRslPackets(cps[1..])
  }


  predicate CPacketSeqHasCorrectSrc(sent_packets:seq<CPacket>, me:EndPoint)
  {
    forall p :: p in sent_packets ==> p.src == me
  }


  predicate CMessageIsInjectiveType(m:CMessage)
  {
    && CMessageIsAbstractable(m)
    && (m.CMessage_1b? || m.CMessage_2b?)
  }

  lemma {:axiom} lemma_AbstractifyCMessageToRslMessage_isInjective(m1:CMessage, m2:CMessage)
    requires CMessageIsInjectiveType(m1) && CMessageIsInjectiveType(m2)
    requires AbstractifyCMessageToRslMessage(m1) == AbstractifyCMessageToRslMessage(m2)
    ensures m1 == m2
  // {
  //   lemma_AbstractifyCRequestBatchToRequestBatch_isInjective();

  //   if (m1.CMessage_1b?) {
  //     lemma_BallotInjective(m1.bal_1b, m2.bal_1b);
  //     lemma_VotesInjective(m1.votes, m2.votes);
  //     assert m1 == m2;
  //   } else if (m1.CMessage_2b?) {
  //     lemma_BallotInjective(m1.bal_2b, m2.bal_2b);
  //     assert AbstractifyCRequestBatchToRequestBatch(m1.val_2b) == AbstractifyCRequestBatchToRequestBatch(m2.val_2b);
  //     assert m1 == m2;
  //   }
  // }

  predicate CPacketIsInjectiveType(p:CPacket)
  {
    CPacketIsAbstractable(p) && CMessageIsInjectiveType(p.msg)
  }

  lemma lemma_AbstractifyCPacketToRslPacket_isInjective()
    ensures forall p1, p2 ::
              && CPacketIsInjectiveType(p1)
              && CPacketIsInjectiveType(p2)
              && AbstractifyCPacketToRslPacket(p1) == AbstractifyCPacketToRslPacket(p2)
              ==> p1 == p2
  {
    forall p1, p2 |
      && CPacketIsInjectiveType(p1)
      && CPacketIsInjectiveType(p2)
      && AbstractifyCPacketToRslPacket(p1) == AbstractifyCPacketToRslPacket(p2)
      ensures p1 == p2
    {
      lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
      lemma_AbstractifyCMessageToRslMessage_isInjective(p1.msg, p2.msg);
    }
  }

  predicate SetOfInjectiveTypeCPackets(s:set<CPacket>)
  {
    forall p :: p in s ==> CPacketIsInjectiveType(p)
  }

  predicate SetOfInjectiveTypeCPacketsIsInjective(s:set<CPacket>)
  {
    && SetOfInjectiveTypeCPackets(s)
    && (forall p1, p2 :: p1 in s && p2 in s && AbstractifyCPacketToRslPacket(p1) == AbstractifyCPacketToRslPacket(p2)
                         ==> p1 == p2)
  }

  lemma lemma_SetOfInjectiveTypeCPacketsIsInjective(s:set<CPacket>)
    requires SetOfInjectiveTypeCPackets(s)
    ensures SetOfInjectiveTypeCPacketsIsInjective(s)
  {
    lemma_AbstractifyCPacketToRslPacket_isInjective();
  }

  lemma lemma_AbstractifySetOfCPacketsToSetOfRslPackets_isInjective(cps1:set<CPacket>, cps2:set<CPacket>)
    requires CPacketsIsAbstractable(cps1)
    requires CPacketsIsAbstractable(cps2)
    requires SetOfInjectiveTypeCPackets(cps1)
    requires SetOfInjectiveTypeCPackets(cps2)
    requires AbstractifySetOfCPacketsToSetOfRslPackets(cps1) == AbstractifySetOfCPacketsToSetOfRslPackets(cps2)
    ensures  cps1 == cps2
  {
    // reveal AbstractifySetOfCPacketsToSetOfRslPackets();
    lemma_AbstractifyCPacketToRslPacket_isInjective();
    forall cp1 | cp1 in cps1
      ensures cp1 in cps2
    {
      var p := AbstractifyCPacketToRslPacket(cp1);
      assert p in AbstractifySetOfCPacketsToSetOfRslPackets(cps2);
    }
    forall cp2 | cp2 in cps2
      ensures cp2 in cps1
    {
      var p := AbstractifyCPacketToRslPacket(cp2);
      assert p in AbstractifySetOfCPacketsToSetOfRslPackets(cps1);
    }
  }

  lemma lemma_AbstractifySetOfCPacketsToSetOfRslPackets_cardinality(cps:set<CPacket>)
    requires CPacketsIsAbstractable(cps)
    requires SetOfInjectiveTypeCPackets(cps)
    ensures  |cps| == |AbstractifySetOfCPacketsToSetOfRslPackets(cps)|
  {
    lemma_SetOfInjectiveTypeCPacketsIsInjective(cps);
    var rps := AbstractifySetOfCPacketsToSetOfRslPackets(cps);
    forall y | y in rps
      ensures exists x :: x in cps && y == AbstractifyCPacketToRslPacket(x)
    {
      // reveal AbstractifySetOfCPacketsToSetOfRslPackets();
    }

    forall x | x in cps
      ensures AbstractifyCPacketToRslPacket(x) in rps
    {
      // reveal AbstractifySetOfCPacketsToSetOfRslPackets();
    }
    lemma_MapSetCardinalityOver(cps, rps, AbstractifyCPacketToRslPacket);
  }


  lemma lemma_AbstractifySetOfCPacketsToSetOfRslPackets_properties(cps:set<CPacket>)
    requires CPacketsIsAbstractable(cps)
    ensures  SetOfInjectiveTypeCPackets(cps) ==> |cps| == |AbstractifySetOfCPacketsToSetOfRslPackets(cps)|
    ensures  AbstractifySetOfCPacketsToSetOfRslPackets({}) == {}
  {
    if SetOfInjectiveTypeCPackets(cps) {
      lemma_AbstractifySetOfCPacketsToSetOfRslPackets_cardinality(cps);
    }

    // reveal AbstractifySetOfCPacketsToSetOfRslPackets();
  }

  // lemma lemma_AbstractifyCPacketToRslPacket_src(cps:set<CPacket>, src:EndPoint)
  //   requires CPacketsIsAbstractable(cps)
  //   requires EndPointIsValidPublicKey(src)
  //   requires forall p :: p in AbstractifySetOfCPacketsToSetOfRslPackets(cps) ==> p.src == AbstractifyEndPointToNodeIdentity(src)
  //   ensures  forall cp :: cp in cps ==> cp.src == src
  // {
  //   reveal AbstractifySetOfCPacketsToSetOfRslPackets();
  //   lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
  //   forall cp | cp in cps
  //     ensures cp.src == src
  //   {
  //     assert AbstractifyCPacketToRslPacket(cp).src == AbstractifyEndPointToNodeIdentity(src);
  //     assert cp.src == src;
  //   }
  // }

  // lemma lemma_AbstractifySetOfCPacketsToSetOfRslPackets_srcMembershipNeg(cps:set<CPacket>, src:EndPoint)
  //   requires CPacketsIsAbstractable(cps)
  //   requires EndPointIsValidPublicKey(src)
  //   requires !(forall p :: p in cps ==> p.src != src)
  //   ensures  !(forall p :: p in AbstractifySetOfCPacketsToSetOfRslPackets(cps) ==> p.src != AbstractifyEndPointToNodeIdentity(src))
  // {
  //   assert exists p :: p in cps && p.src == src;
  //   var cp :| cp in cps && cp.src == src;
  //   var p := AbstractifyCPacketToRslPacket(cp);
  //   reveal AbstractifySetOfCPacketsToSetOfRslPackets();
  //   assert p in AbstractifySetOfCPacketsToSetOfRslPackets(cps);
  //   lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
  // }

  // lemma lemma_AbstractifySetOfCPacketsToSetOfRslPackets_srcMembershipPos(cps:set<CPacket>, src:EndPoint)
  //   requires CPacketsIsAbstractable(cps)
  //   requires EndPointIsValidPublicKey(src)
  //   requires forall p :: p in cps ==> p.src != src
  //   ensures  forall p :: p in AbstractifySetOfCPacketsToSetOfRslPackets(cps) ==> p.src != AbstractifyEndPointToNodeIdentity(src)
  // {
  //   forall p | p in AbstractifySetOfCPacketsToSetOfRslPackets(cps)
  //     ensures p.src != AbstractifyEndPointToNodeIdentity(src)
  //   {
  //     reveal AbstractifySetOfCPacketsToSetOfRslPackets();
  //     var cp :| cp in cps && AbstractifyCPacketToRslPacket(cp) == p;
  //     assert p.src == AbstractifyEndPointToNodeIdentity(cp.src);
  //     assert cp.src != src;
  //     lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
  //   }
  // }

  // lemma lemma_AbstractifySetOfCPacketsToSetOfRslPackets_srcMembership(cps:set<CPacket>, src:EndPoint)
  //   requires CPacketsIsAbstractable(cps)
  //   requires EndPointIsValidPublicKey(src)
  //   ensures  (forall p :: p in cps ==> p.src != src) <==> (forall p :: p in AbstractifySetOfCPacketsToSetOfRslPackets(cps) ==> p.src != AbstractifyEndPointToNodeIdentity(src))
  // {
  //   var b := (forall p :: p in cps ==> p.src != src);

  //   if b {
  //     lemma_AbstractifySetOfCPacketsToSetOfRslPackets_srcMembershipPos(cps, src);
  //   } else {
  //     lemma_AbstractifySetOfCPacketsToSetOfRslPackets_srcMembershipNeg(cps, src);
  //   }
  // }


  // function {:opaque} BuildLBroadcast(src:NodeIdentity, dsts:seq<NodeIdentity>, m:RslMessage):seq<RslPacket>
  //   ensures |BuildLBroadcast(src, dsts, m)| == |dsts|
  //   ensures forall i :: 0 <= i < |dsts| ==> BuildLBroadcast(src, dsts, m)[i] == LPacket(dsts[i], src, m)
  // {
  //   if |dsts| == 0 then []
  //   else [LPacket(dsts[0], src, m)] + BuildLBroadcast(src, dsts[1..], m)
  // }

  // predicate CBroadcastIsAbstractable(broadcast:CBroadcast)
  // {
  //   || broadcast.CBroadcastNop?
  //   || (&& broadcast.CBroadcast?
  //      && EndPointIsValidIPV4(broadcast.src)
  //      && (forall i :: 0 <= i < |broadcast.dsts| ==> EndPointIsValidIPV4(broadcast.dsts[i]))
  //      && CMessageIsAbstractable(broadcast.msg))
  // }

  // function AbstractifyCBroadcastToRlsPacketSeq(broadcast:CBroadcast) : seq<RslPacket>
  //   requires CBroadcastIsAbstractable(broadcast)
  // {
  //   match broadcast
  //     case CBroadcast(_,_,_) => BuildLBroadcast(AbstractifyEndPointToNodeIdentity(broadcast.src),
  //                                               AbstractifyEndPointsToNodeIdentities(broadcast.dsts),
  //                                               AbstractifyCMessageToRslMessage(broadcast.msg))
  //     case CBroadcastNop => []
  // }

  // predicate OutboundPacketsIsAbstractable(out:OutboundPackets)
  // {
  //   match out
  //     case Broadcast(broadcast) => CBroadcastIsAbstractable(broadcast)
  //     case OutboundPacket(Some(p)) => CPacketIsAbstractable(p)
  //     case OutboundPacket(None()) => true
  //     case PacketSequence(s) => CPacketSeqIsAbstractable(s)
  // }

  // function AbstractifyOutboundCPacketsToSeqOfRslPackets(out:OutboundPackets) : seq<RslPacket>
  //   requires OutboundPacketsIsAbstractable(out)
  // {
  //   match out
  //     case Broadcast(broadcast) => AbstractifyCBroadcastToRlsPacketSeq(broadcast)
  //     case OutboundPacket(Some(p)) => [AbstractifyCPacketToRslPacket(p)]
  //     case OutboundPacket(None()) => []
  //     case PacketSequence(s) => AbstractifySeqOfCPacketsToSeqOfRslPackets(s)
  // }

  // predicate OutboundPacketsHasCorrectSrc(out:OutboundPackets, me:EndPoint)
  // {
  //   match out
  //     case Broadcast(CBroadcast(src, _, _)) => src == me
  //     case Broadcast(CBroadcastNop()) => true
  //     case OutboundPacket(p) => p.Some? ==> p.v.src == me
  //     case PacketSequence(s) => (forall p :: p in s ==> p.src == me)
  // //    case OutboundPacket(Some(p)) => p.src == me
  // //    case OutboundPacket(None()) => true
  // }

}
