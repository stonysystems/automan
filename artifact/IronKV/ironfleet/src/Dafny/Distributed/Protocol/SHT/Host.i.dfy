include "SingleDelivery.i.dfy"
include "Delegations.i.dfy"
include "Parameters.i.dfy"
include "../LiveSHT/RefinementProof/Environment.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Common/Logic/Option.i.dfy"
include "../../Services/SHT/AbstractService.s.dfy"
include "../Common/NodeIdentity.i.dfy"

module SHT__Host_i {
import opened Collections__Maps2_s
import opened SHT__SingleDelivery_i
import opened SHT__Delegations_i
import opened Protocol_Parameters_i 
import opened LiveSHT__Environment_i
import opened Collections__Sets_i
import opened Logic__Option_i
import opened AbstractServiceSHT_s`All
import opened Concrete_NodeIdentity_i
import opened SHT__HT_s
import opened SHT__Message_i
import opened SHT__SingleMessage_i
import opened SHT__Network_i
import opened AppInterface_i`Spec
import opened SHT__Keys_i


datatype Constants = Constants(
    rootIdentity:NodeIdentity,
    hostIds:seq<NodeIdentity>,
    params:Parameters)

datatype Host = Host(
    constants:Constants,
    me:NodeIdentity,
    ghost delegationMap:DelegationMap,
    h:Hashtable,
    sd:SingleDeliveryAcct,
    receivedPacket:Option<Packet>,
    numDelegations:int,
    ghost receivedRequests:seq<AppRequest>
    )

function LSHTPacketToPacket(lp:LSHTPacket) : Packet
{
    Packet(lp.dst, lp.src, lp.msg)
}

predicate ValidKeyPlus(key:KeyPlus)
{
    key.KeyZero? || key.KeyInf? || ValidKey(key.k)
}

predicate ValidOptionalValue(opt:OptionalValue)
{
    opt.ValueAbsent? || ValidValue(opt.v)
}

predicate ValidKeyRange(kr:KeyRange)
{
    ValidKeyPlus(kr.klo) && ValidKeyPlus(kr.khi)
}

function ExtractPacketsFromLSHTPackets(seqPackets:seq<LSHTPacket>) : set<Packet>
    ensures forall p :: p in seqPackets <==> Packet(p.dst, p.src, p.msg) in ExtractPacketsFromLSHTPackets(seqPackets)
{
    MapSeqToSet(seqPackets, LSHTPacketToPacket)
}

function DelegationMap_Init(rootIdentity:NodeIdentity) : DelegationMap {
    map k {:auto_trigger} :: rootIdentity
}

function method HashtableLookup(h:Hashtable, k:Key) : OptionalValue
{
    if k in h then ValuePresent(h[k]) else ValueAbsent()
}

// Initially, everybody thinks the root is in charge of every key.
predicate Host_Init(s:Host, id:NodeIdentity, rootIdentity:NodeIdentity, hostIds:seq<NodeIdentity>, params:Parameters) {
    s==Host(
        Constants(rootIdentity, hostIds, params),
        id,
        DelegationMap_Init(rootIdentity),
        // map[0 := rootIdentity],
        map [],
        SingleDelivery_Init(),
        None,
        1,
        [])
}

// marked relational spec, used as a predicate
predicate NextGetRequest_Reply(s:Host, s':Host, src:NodeIdentity, seqno:int, k:Key, sm:SingleMessage, m:Message, out:set<Packet>, shouldSend:bool)
    // requires DelegationMapComplete(s.delegationMap);
    requires k in s.delegationMap
{
    var owner := DelegateForKey(s.delegationMap, k);
    if shouldSend && ValidKey(k) then
            (if owner == s.me
                 then 
                         m == Reply(k, HashtableLookup(s.h, k)) 
                      && s'.receivedRequests == s.receivedRequests + [AppGetRequest(seqno, k)]
                 else 
                         m == Redirect(k, owner)
                      && s'.receivedRequests == s.receivedRequests
             )
        && SendSingleMessage(s.sd, s'.sd, m, sm, s.constants.params, shouldSend)
        && sm.dst == src
        && out == {Packet(src, s.me, sm)}
        && s'.receivedPacket == None
    else
        && s' == s.(receivedPacket := None)
        // && s' == s
        && out == {}
}

predicate NextGetRequest_Reply_Real(s:Host, s':Host, src:NodeIdentity, seqno:int, k:Key, sm:SingleMessage, m:Message, out:set<Packet>, shouldSend:bool)
    requires k in s.delegationMap
    ensures NextGetRequest_Reply_Real(s,s',src,seqno,k,sm,m,out,shouldSend) ==>
            NextGetRequest_Reply(s,s',src,seqno,k,sm,m,out,shouldSend)
{
    var owner := DelegateForKey(s.delegationMap, k);
    var newReceivedRequests := if owner == s.me then s.receivedRequests + [AppGetRequest(seqno, k)] else s.receivedRequests;
    var msg := if owner == s.me then Reply(k, HashtableLookup(s.h, k)) else Redirect(k, owner);

    && SendSingleMessageReal(s.sd, s'.sd, msg, src, sm, s.constants.params, shouldSend)
    && if ValidKey(k) && shouldSend then
        && m == msg
        && s' == s.(sd := s'.sd, receivedRequests := newReceivedRequests, receivedPacket := None)
        && out == {Packet(src, s.me, sm)}
       else
        && s' == s.(receivedPacket:=None)
        && m == msg
        && out == {}
}

predicate NextGetRequest(s:Host, s':Host, pkt:Packet, out:set<Packet>)
    requires pkt.msg.SingleMessage?;
    requires pkt.msg.m.GetRequest? ==> pkt.msg.m.k_getrequest in s.delegationMap
    // requires DelegationMapComplete(s.delegationMap);
{
       pkt.msg.m.GetRequest?
    && s'.delegationMap == s.delegationMap
    && s'.h == s.h
    && s'.numDelegations == s.numDelegations  // UNCHANGED
    && (exists sm,m,b :: NextGetRequest_Reply(s, s', pkt.src, pkt.msg.seqno, pkt.msg.m.k_getrequest, sm, m, out, b))
}

// predicate NextGetRequestReal(s:Host, s':Host, pkt:Packet, out:set<Packet>)
//     requires pkt.msg.SingleMessage?;
//     requires pkt.msg.m.GetRequest?
//     requires pkt.msg.m.k_getrequest in s.delegationMap
//     // requires DelegationMapComplete(s.delegationMap);
// {
//     var (new_sd, )
//     && s'.delegationMap == s.delegationMap
//     && s'.h == s.h
//     && s'.numDelegations == s.numDelegations  // UNCHANGED
//     && (exists sm,m,b :: NextGetRequest_Reply(s, s', pkt.src, pkt.msg.seqno, pkt.msg.m.k_getrequest, sm, m, out, b))
// }

predicate NextSetRequest_Complete(s:Host, s':Host, src:NodeIdentity, seqno:int, reqm:Message, sm:SingleMessage, replym:Message, out:set<Packet>, shouldSend:bool)
    requires reqm.SetRequest?
    requires reqm.k_setrequest in s.delegationMap
{
    var k := reqm.k_setrequest;
    var ov := reqm.v_setrequest;
    var owner := DelegateForKey(s.delegationMap, k);
    if shouldSend && ValidKey(k) && ValidOptionalValue(ov) then
          (if owner == s.me
           then
               s'.h == (if ov.ValueAbsent? then mapremove(s.h, k) else s.h[k:=ov.v])
            && replym == Reply(k, ov)
            && s'.receivedRequests == s.receivedRequests + [AppSetRequest(seqno, k, ov)]
           else
               s'.h == s.h
            && replym == Redirect(k, owner)
            && s'.receivedRequests == s.receivedRequests
           )
        && SendSingleMessage(s.sd, s'.sd, replym, sm, s.constants.params, shouldSend)
        && sm.dst == src
        && out == {Packet(src, s.me, sm)}
        && s'.receivedPacket == None
    else
        && s' == s.(receivedPacket := None)
        && out == {}
}

predicate NextSetRequest_Complete_Real(s:Host, s':Host, src:NodeIdentity, seqno:int, reqm:Message, sm:SingleMessage, replym:Message, out:set<Packet>, shouldSend:bool)
    // requires DelegationMapComplete(s.delegationMap);
    requires reqm.SetRequest?;
    requires reqm.k_setrequest in s.delegationMap
    ensures NextSetRequest_Complete_Real(s,s',src,seqno,reqm,sm,replym,out,shouldSend) ==>
            NextSetRequest_Complete(s,s',src,seqno,reqm,sm,replym,out,shouldSend)
{
    var k := reqm.k_setrequest;
    var ov := reqm.v_setrequest;
    var owner := DelegateForKey(s.delegationMap, k);
    var newhtable := if owner == s.me then (if ov.ValueAbsent? then mapremove(s.h, k) else s.h[k:=ov.v]) else s.h;
    var msg := if owner == s.me then Reply(k, ov) else Redirect(k, owner);
    var reqs := if owner == s.me then s.receivedRequests + [AppSetRequest(seqno, k, ov)] else s.receivedRequests;

    && SendSingleMessageReal(s.sd, s'.sd, msg, src, sm, s.constants.params, shouldSend)
    && if shouldSend && ValidKey(k) && ValidOptionalValue(ov) then
        && replym == msg
        && s' == s.(h := newhtable, sd := s'.sd, receivedRequests := reqs, receivedPacket := None)
        && out == {Packet(src, s.me, sm)}
    else
        && replym == msg
        && s' == s.(receivedPacket:=None)
        && out == {}
}


predicate NextSetRequest(s:Host, s':Host, pkt:Packet, out:set<Packet>)
    requires pkt.msg.SingleMessage?;
    requires DelegationMapComplete(s.delegationMap);
{
       pkt.msg.m.SetRequest?
    && (exists sm,m,b :: NextSetRequest_Complete(s, s', pkt.src, pkt.msg.seqno, pkt.msg.m, sm, m, out, b))
    && s'.delegationMap == s.delegationMap  // UNCHANGED
    && s'.numDelegations == s.numDelegations  // UNCHANGED
}

predicate NextDelegate(s:Host, s':Host, pkt:Packet, out:set<Packet>)
    requires pkt.msg.SingleMessage?;
    // requires DelegationMapComplete(s.delegationMap);
{
       pkt.msg.m.Delegate?
    && (if pkt.src in s.constants.hostIds then
           s'.delegationMap == UpdateDelegationMap(s.delegationMap, pkt.msg.m.range, s.me)
        && s'.h == BulkUpdateHashtable(s.h, pkt.msg.m.range, pkt.msg.m.h)
        && s'.numDelegations == s.numDelegations + 1 
       else 
           s'.delegationMap == s.delegationMap
        && s'.h == s.h
        && s'.numDelegations == s.numDelegations
       )
    && SendNoMessage(s.sd, s'.sd)
    && ReceiveNoMessage(s.sd, s'.sd)
    && out == {}
    && s'.receivedRequests == s.receivedRequests
    // && s'.receivedPacket == None
}

predicate NextDelegateReal(s:Host, s':Host, pkt:Packet, out:set<Packet>)
    requires pkt.msg.SingleMessage?;
    requires pkt.msg.m.Delegate?
    // requires DelegationMapComplete(s.delegationMap);
    ensures NextDelegateReal(s,s',pkt,out) ==>
            NextDelegate(s,s',pkt,out)
{
    && (if pkt.src in s.constants.hostIds then
           s'.delegationMap == UpdateDelegationMap(s.delegationMap, pkt.msg.m.range, s.me)
        && s'.h == BulkUpdateHashtable(s.h, pkt.msg.m.range, pkt.msg.m.h)
        && s'.numDelegations == s.numDelegations + 1 
       else 
           s'.delegationMap == s.delegationMap
        && s'.h == s.h
        && s'.numDelegations == s.numDelegations
       )
    && out == {}
    && s'.sd == s.sd
    && s'.receivedRequests == s.receivedRequests
    && s'.receivedPacket == None
}

predicate NextShard(s:Host, s':Host, out:set<Packet>, kr:KeyRange, recipient:NodeIdentity, sm:SingleMessage, shouldSend:bool)
{
       recipient != s.me  // HISTORY: proof caught this missing conjunct
    && recipient in s.constants.hostIds // HISTORY: proof caught this missing conjunct
    && DelegateForKeyRangeIsHost(s.delegationMap, kr, s.me)  // HISTORY: proof caught this missing conjunct!
    && SendSingleMessage(s.sd, s'.sd, Delegate(kr, ExtractRange(s.h, kr)), sm, s.constants.params, shouldSend)
    && recipient == sm.dst
    && s.constants == s'.constants
    && s'.numDelegations == s.numDelegations + 1
    && s'.receivedRequests == s.receivedRequests
    && s'.receivedPacket == None
    && if shouldSend then
            out == { Packet(recipient, s.me, sm) }
         && s'.delegationMap == UpdateDelegationMap(s.delegationMap, kr, recipient)
         && s'.h == BulkRemoveHashtable(s.h, kr)
       else
            out == {}
         && s'.delegationMap == s.delegationMap
         && s'.h == s.h
}

predicate NextShardReal(s:Host, s':Host, out:set<Packet>, kr:KeyRange, recipient:NodeIdentity, sm:SingleMessage, shouldSend:bool)
    requires DelegateForKeyRangeIsHost(s.delegationMap, kr, s.me)
    requires recipient != s.me
    requires recipient in s.constants.hostIds
    ensures NextShardReal(s,s',out,kr,recipient,sm,shouldSend) ==> 
            NextShard(s,s',out,kr,recipient,sm,shouldSend)
{
    && SendSingleMessageReal(s.sd, s'.sd, Delegate(kr, ExtractRange(s.h, kr)), recipient, sm, s.constants.params, shouldSend)
    && if shouldSend then
         && out == { Packet(recipient, s.me, sm) }
         && s' == s.(h := BulkRemoveHashtable(s.h, kr), delegationMap := UpdateDelegationMap(s.delegationMap, kr, recipient), sd := s'.sd, numDelegations := s.numDelegations + 1, receivedPacket := None)
       else
         && out == {}
         && s' == s.(numDelegations := s.numDelegations + 1, receivedPacket := None)
}

function max_hashtable_size():int { 62 }

predicate NextShard_Wrapper(s:Host, s':Host, pkt:Packet, out:set<Packet>)
    requires pkt.msg.SingleMessage?;
    requires DelegationMapComplete(s.delegationMap);
{
       pkt.msg.m.Shard?
    && if (   pkt.msg.m.recipient == s.me
           || !ValidKeyRange(pkt.msg.m.kr)
           || EmptyKeyRange(pkt.msg.m.kr)
           || pkt.msg.m.recipient !in s.constants.hostIds 
           || !DelegateForKeyRangeIsHost(s.delegationMap, pkt.msg.m.kr, s.me)
           || |ExtractRange(s.h, pkt.msg.m.kr)| >= max_hashtable_size()) then 
            s' == s.(receivedPacket := s'.receivedPacket) && out == {}   
       else 
            exists sm,b :: NextShard(s, s', out, pkt.msg.m.kr, pkt.msg.m.recipient, sm, b)
}

predicate NextReply(s:Host, s':Host, pkt:Packet, out:set<Packet>)
    requires pkt.msg.SingleMessage?;
    // requires DelegationMapComplete(s.delegationMap);
{
       pkt.msg.m.Reply?
    && out == {}
    && s' == s.(receivedPacket := None)
}

predicate NextReplyReal(s:Host, s':Host, pkt:Packet, out:set<Packet>)
    requires pkt.msg.SingleMessage?;
    requires pkt.msg.m.Reply?
    ensures NextReplyReal(s,s',pkt,out) ==>
            NextReply(s,s',pkt,out)
{
    && out == {}
    && s' == s.(receivedPacket := None)
}

predicate NextRedirect(s:Host, s':Host, pkt:Packet, out:set<Packet>)
    requires pkt.msg.SingleMessage?;
{
       pkt.msg.m.Redirect?
    && out == {}
    && s' == s.(receivedPacket := None)
}

predicate NextRedirectReal(s:Host, s':Host, pkt:Packet, out:set<Packet>)
    requires pkt.msg.SingleMessage?;
    requires pkt.msg.m.Redirect?
    ensures NextRedirectReal(s,s',pkt,out) ==>
            NextRedirect(s,s',pkt,out)
{
    && out == {}
    && s' == s.(receivedPacket := None)
}

predicate ShouldProcessReceivedMessage(s:Host)
{
    s.receivedPacket.Some?
 && s.receivedPacket.v.msg.SingleMessage?
 && ((s.receivedPacket.v.msg.m.Delegate? || s.receivedPacket.v.msg.m.Shard?) ==> s.numDelegations < s.constants.params.max_delegations - 2)
}

predicate Process_Message(s:Host, s':Host, out:set<Packet>)
    requires DelegationMapComplete(s.delegationMap);
{
    if ShouldProcessReceivedMessage(s) then
           (NextGetRequest(s, s', s.receivedPacket.v, out)
        || NextSetRequest(s, s', s.receivedPacket.v, out)
        || NextDelegate(s, s', s.receivedPacket.v, out)
        || NextShard_Wrapper(s, s', s.receivedPacket.v, out)
        || NextReply(s, s', s.receivedPacket.v, out)
        || NextRedirect(s, s', s.receivedPacket.v, out))
         && s'.receivedPacket.None?
    else
        s' == s && out == {}
}

predicate ReceivePacket(s:Host, s':Host, pkt:Packet, out:set<Packet>, ack:Packet)
{
    if s.receivedPacket.None? then    // No packet currently waiting to be processed
        && ReceiveSingleMessage(s.sd, s'.sd, pkt, ack, out) // Record and possibly ack it
        // && pkt.msg.SingleMessage? && ShouldAckSingleMessage(s.sd,pkt) ==> var m := Ack(pkt.msg.seqno); ack == Packet(dst:=pkt.src, src:=pkt.dst, msg:=m)
        && (if NewSingleMessage(s.sd, pkt) then
               s'.receivedPacket == Some(pkt)   // Enqueue this packet for processing
            else
               s'.receivedPacket.None?)
        && s' == s.(sd := s'.sd, receivedPacket := s'.receivedPacket)  // Nothing else changes
    else 
        s' == s && out == {}
}


predicate ProcessReceivedPacket(s:Host, s':Host, out:set<Packet>)
    requires DelegationMapComplete(s.delegationMap);
{
    if s.receivedPacket.Some? then 
        Process_Message(s, s', out)
    else
        s' == s && out == {}
}

// REVIEW: For safety, we don't need to retransmit at all.  
// We could also just retransmit some, but not all, leaving it to the impl to decide.
// For liveness, we have to retransmit some, and at the very least, retransmit in some order.
// I suspect retransmitting them all will simplify things, however.
predicate SpontaneouslyRetransmit(s:Host, s':Host, out:set<Packet>)
{
    (out == UnAckedMessages(s.sd, s.me) && s == s')
}

predicate Host_Next(s:Host, s':Host, recv:set<Packet>, out:set<Packet>)
{
       s'.constants == s.constants
    && s'.me == s.me
    && DelegationMapComplete(s.delegationMap)
    && (
           (exists pkt, ack :: pkt in recv && ReceivePacket(s, s', pkt, out, ack))
        || ProcessReceivedPacket(s, s', out)
        || SpontaneouslyRetransmit(s, s', out)
       )
}
} 
