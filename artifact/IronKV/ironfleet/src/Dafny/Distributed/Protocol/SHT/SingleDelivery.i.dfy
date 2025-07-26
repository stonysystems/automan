include "SingleMessage.i.dfy"
include "Network.i.dfy"
include "Parameters.i.dfy"

module SHT__SingleDelivery_i {
import opened Concrete_NodeIdentity_i
import opened SHT__Message_i
import opened SHT__SingleMessage_i 
import opened SHT__Network_i    
import opened Protocol_Parameters_i

// A module to ensure each message is delivered exactly once,
// built by including sequence numbers in messages and recording
// the highest received sequence number and the list of outstanding packets

// Workaround for the fact that Dafny won't let us put nat into collection types, like TombstoneTable below
// newtype nat_t = i:int | 0 <= i

// Highest sequence number we have received from each node
type TombstoneTable = map<NodeIdentity,nat>

// State about packets we've sent to each node
// datatype AckState<MT> = AckState(numPacketsAcked:nat, unAcked:seq<SingleMessage<MT>>)
// type SendState<MT> = map<NodeIdentity, AckState<MT>>
datatype AckState = AckState(numPacketsAcked:nat, unAcked:seq<SingleMessage>)
type SendState = map<NodeIdentity, AckState>

// datatype SingleDeliveryAcct<MT> = SingleDeliveryAcct(receiveState:TombstoneTable, sendState:SendState<MT>)
datatype SingleDeliveryAcct = SingleDeliveryAcct(receiveState:TombstoneTable, sendState:SendState)

function TombstoneTableLookup(src:NodeIdentity, t:TombstoneTable) : nat
{
    if src in t then t[src] as int else 0 
}

function AckStateLookup(src:NodeIdentity, sendState:SendState):AckState
{
    if src in sendState then sendState[src] else AckState(0, [])
}

// Written as a function to avoid an exists in the client
function SingleDelivery_Init() : SingleDeliveryAcct
{
    SingleDeliveryAcct(map[], map[])
}

predicate MessageNotReceived(s:SingleDeliveryAcct, src:NodeIdentity, sm:SingleMessage)
{
      sm.SingleMessage? 
   && sm.seqno > TombstoneTableLookup(src, s.receiveState)
}

predicate NewSingleMessage(s:SingleDeliveryAcct, pkt:Packet)
{
    pkt.msg.SingleMessage? &&  
    var last_seqno := TombstoneTableLookup(pkt.src, s.receiveState);
    pkt.msg.seqno == last_seqno + 1
}

// Remove all packets implicitly ack'ed by seqnoAcked from the list of unacknowledged packets
function TruncateUnAckList(unAcked:seq<SingleMessage>, seqnoAcked:nat) : seq<SingleMessage>
    ensures forall m :: m in TruncateUnAckList(unAcked, seqnoAcked) ==> m in unAcked;
{
    if |unAcked| > 0 && unAcked[0].SingleMessage? && unAcked[0].seqno <= seqnoAcked then 
        TruncateUnAckList(unAcked[1..], seqnoAcked)
    else 
        unAcked
}

predicate ReceiveAck(s:SingleDeliveryAcct, s':SingleDeliveryAcct, pkt:Packet, acks:set<Packet>)
    requires pkt.msg.Ack?;
{
    acks == {} &&   // We don't ack acks
    var oldAckState := AckStateLookup(pkt.src, s.sendState);
    if pkt.msg.ack_seqno > oldAckState.numPacketsAcked then
        var newAckState := oldAckState.(numPacketsAcked := pkt.msg.ack_seqno,
                                        unAcked := TruncateUnAckList(oldAckState.unAcked, pkt.msg.ack_seqno));
        s' == s.(sendState := s.sendState[pkt.src := newAckState])
    else 
        s' == s
}

predicate ShouldAckSingleMessage(s:SingleDeliveryAcct, pkt:Packet)
{
    pkt.msg.SingleMessage? &&  // Don't want to ack acks
    var last_seqno := TombstoneTableLookup(pkt.src, s.receiveState);
    pkt.msg.seqno <= last_seqno
}

predicate SendAck(s:SingleDeliveryAcct, pkt:Packet, ack:Packet, acks:set<Packet>) 
    requires ShouldAckSingleMessage(s, pkt);
{
    var m := Ack(pkt.msg.seqno);
    && ack == Packet(dst:=pkt.src, src:=pkt.dst, msg:=m)
    && acks == { ack }
}

// predicate SendAck(s:SingleDeliveryAcct, pkt:Packet, acks:set<Packet>) 
//     requires ShouldAckSingleMessage(s, pkt);
// {
//     var m := Ack(pkt.msg.seqno);
//     var ack := Packet(dst:=pkt.src, src:=pkt.dst, msg:=m);
//     && acks == { ack }
// }

predicate MaybeAckPacket(s:SingleDeliveryAcct, pkt:Packet, ack:Packet, acks:set<Packet>) 
{
    if ShouldAckSingleMessage(s, pkt) then
        && SendAck(s, pkt, ack, acks)
    else 
        && acks == {}
}

// predicate MaybeAckPacket(s:SingleDeliveryAcct, pkt:Packet, acks:set<Packet>) 
// {
//     if ShouldAckSingleMessage(s, pkt) then
//         && SendAck(s, pkt, acks)
//     else 
//         && acks == {}
// }

predicate ReceiveRealPacket(s:SingleDeliveryAcct, s':SingleDeliveryAcct, pkt:Packet)
    requires pkt.msg.SingleMessage?;
{
    if NewSingleMessage(s, pkt) then
        var last_seqno := TombstoneTableLookup(pkt.src, s.receiveState);
        // Mark it received 
        s' == s.(receiveState := s.receiveState[pkt.src := (last_seqno + 1) as nat])
    else
        s == s'
}

predicate UnAckedMsgForDst(s:SingleDeliveryAcct, msg:SingleMessage, dst:NodeIdentity)
{
    dst in s.sendState && msg in s.sendState[dst].unAcked
}

function UnAckedMessages(s:SingleDeliveryAcct, src:NodeIdentity):set<Packet>
{
    set dst, i | dst in s.sendState && 0 <= i < |s.sendState[dst].unAcked| && s.sendState[dst].unAcked[i].SingleMessage? :: 
        var sm := s.sendState[dst].unAcked[i];
        Packet(sm.dst, src, sm)
}

// Partial actions

// Client should ReceiveSingleMessage or ReceiveNoMessage
// marked, relational spec
predicate ReceiveSingleMessage(s:SingleDeliveryAcct, s':SingleDeliveryAcct, pkt:Packet, ack:Packet, acks:set<Packet>)
{
    // match pkt.msg {
    //     case Ack(_) => ReceiveAck(s, s', pkt, acks)
    //     case SingleMessage(seqno, _, m) => ReceiveRealPacket(s, s', pkt) && MaybeAckPacket(s', pkt, ack, acks) 
    //             && (|acks| > 0 ==> ack == var m := Ack(pkt.msg.seqno); Packet(dst:=pkt.src, src:=pkt.dst, msg:=m))
    //     case InvalidMessage => (s' == s && acks == {})
    // }
    if pkt.msg.Ack? then
        ReceiveAck(s, s', pkt, acks)
    else if pkt.msg.SingleMessage? then
        && ReceiveRealPacket(s, s', pkt) 
        && MaybeAckPacket(s', pkt, ack, acks)
    else 
        && s' == s 
        && acks == {}
}

// predicate ReceiveSingleMessage(s:SingleDeliveryAcct, s':SingleDeliveryAcct, pkt:Packet, acks:set<Packet>)
// {
//     match pkt.msg {
//         case Ack(_) => ReceiveAck(s, s', pkt, acks)
//         case SingleMessage(seqno, _, m) => ReceiveRealPacket(s, s', pkt) && MaybeAckPacket(s', pkt, acks)
//         case InvalidMessage => (s' == s && acks == {})
//     }
// }

// marked: 这个不用翻译成action
predicate ReceiveNoMessage(s1:SingleDeliveryAcct, s2:SingleDeliveryAcct)
{
    s2.receiveState == s1.receiveState
}


// Highest sequence number we've sent to dst
function HighestSeqnoSent(s:SingleDeliveryAcct, dst:NodeIdentity) : nat
{
    var ackState := AckStateLookup(dst, s.sendState); 
    ackState.numPacketsAcked + |ackState.unAcked|   
}

// Client should SendSingleMessage or SendNoMessage
// marked: 包含多个要构建的状态，且构建状态的信息不够
// marked: used as property checking predict
predicate SendSingleMessage(s:SingleDeliveryAcct, s':SingleDeliveryAcct, m:Message, sm:SingleMessage, params:Parameters, shouldSend:bool)
{
       sm.SingleMessage? 
    && sm.m == m
    && var oldAckState := AckStateLookup(sm.dst, s.sendState); 
       var new_seqno := oldAckState.numPacketsAcked + |oldAckState.unAcked| + 1;
       if new_seqno > params.max_seqno then
           s' == s && !shouldSend // Packet shouldn't be sent if we exceed the maximum sequence number
       else
           (s' == s.(sendState := s.sendState[sm.dst := oldAckState.(unAcked := oldAckState.unAcked + [sm])])
            && sm.seqno == new_seqno
            && shouldSend)
}

predicate SendSingleMessageReal(s:SingleDeliveryAcct, s':SingleDeliveryAcct, m:Message, dst:NodeIdentity, sm:SingleMessage, params:Parameters, shouldSend:bool)
    ensures SendSingleMessageReal(s,s',m,dst,sm,params,shouldSend) ==> SendSingleMessage(s,s',m,sm,params,shouldSend)
{
    var oldAckState := AckStateLookup(dst, s.sendState); 
    var new_seqno := oldAckState.numPacketsAcked + |oldAckState.unAcked| + 1;
    if new_seqno > params.max_seqno then
        && s' == s
        && shouldSend == false
        && sm == SingleMessage(0, dst, m)
    else 
        && sm == SingleMessage((oldAckState.numPacketsAcked + |oldAckState.unAcked| + 1), dst, m)
        && s' == s.(sendState := s.sendState[sm.dst := oldAckState.(unAcked := oldAckState.unAcked + [sm])])
        && shouldSend == true
}

// marked: 这个不用翻译成action
predicate SendNoMessage(s1:SingleDeliveryAcct, s2:SingleDeliveryAcct)
{
   s2.sendState == s1.sendState    // UNCHANGED
}

} 
