include "../../Protocol/SHT/SingleDelivery.i.dfy"
include "CMessage.i.dfy"
include "Parameters.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../Common/GenericRefinement.i.dfy"
include "CSingleMessage.i.dfy"
include "CNetwork.i.dfy"

module SHT__CSingleDelivery_i {
import opened Native__NativeTypes_s
import opened Native__Io_s
import opened Common__NodeIdentity_i
import opened SHT__SingleDelivery_i
import opened GenericRefinement_i
import opened SHT__CMessage_i
import opened SHT__CSingleMessage_i
import opened SHT__CNetwork_i
import opened Impl_Parameters_i
import opened SHT__SingleMessage_i 
import opened Collections__Sets_i
import opened Common__SeqIsUnique_i

/************************** AutoMan Translation ************************/
    type CTombstoneTable = map<EndPoint, nat>

	predicate CTombstoneTableIsAbstractable(s: CTombstoneTable) 
	{
		(forall i :: i in s ==> EndPointIsAbstractable(i))
	}

	predicate CTombstoneTableIsValid(s: CTombstoneTable) 
	{
		CTombstoneTableIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> EndPointIsValid(i))
	}

	function AbstractifyCTombstoneTableToTombstoneTable(s: CTombstoneTable) : TombstoneTable 
		requires CTombstoneTableIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyEndPointToNodeIdentity, NoChange, AbstractifyNodeIdentityToEndPoint)
	}

    datatype CAckState = 
	CAckState(
		numPacketsAcked: nat, 
		unAcked: seq<CSingleMessage>
	)

	predicate CAckStateIsValid(s: CAckState) 
	{
		CAckStateIsAbstractable(s) 
		&& 
		(forall i :: i in s.unAcked ==> CSingleMessageIsValid(i))
	}

	predicate CAckStateIsAbstractable(s: CAckState) 
	{
		(forall i :: i in s.unAcked ==> CSingleMessageIsAbstractable(i))
	}

	function AbstractifyCAckStateToAckState(s: CAckState) : AckState 
		requires CAckStateIsAbstractable(s)
	{
		AckState(s.numPacketsAcked, AbstractifySeq(s.unAcked, AbstractifyCSingleMessageToSingleMessage))
	}


    datatype CSingleDeliveryAcct = 
	CSingleDeliveryAcct(
		receiveState: CTombstoneTable, 
		sendState: CSendState
	)

	predicate CSingleDeliveryAcctIsValid(s: CSingleDeliveryAcct) 
	{
		CSingleDeliveryAcctIsAbstractable(s) 
		&& 
		CTombstoneTableIsValid(s.receiveState) 
		&& 
		CSendStateIsValid(s.sendState)
	}

	predicate CSingleDeliveryAcctIsAbstractable(s: CSingleDeliveryAcct) 
	{
		CTombstoneTableIsAbstractable(s.receiveState) 
		&& 
		CSendStateIsAbstractable(s.sendState)
	}

	function AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s: CSingleDeliveryAcct) : SingleDeliveryAcct 
		requires CSingleDeliveryAcctIsAbstractable(s)
	{
		SingleDeliveryAcct(AbstractifyCTombstoneTableToTombstoneTable(s.receiveState), AbstractifyCSendStateToSendState(s.sendState))
	}

    type CSendState = map<EndPoint, CAckState>

	predicate CSendStateIsAbstractable(s: CSendState) 
	{
		(forall i :: i in s ==> EndPointIsAbstractable(i) && CAckStateIsAbstractable(s[i]))
	}

	predicate CSendStateIsValid(s: CSendState) 
	{
		CSendStateIsAbstractable(s) 
		&& 
		(forall i :: i in s ==> EndPointIsValid(i) && CAckStateIsValid(s[i]))
	}

	function AbstractifyCSendStateToSendState(s: CSendState) : SendState 
		requires CSendStateIsAbstractable(s)
	{
		AbstractifyMap(s, AbstractifyEndPointToNodeIdentity, AbstractifyCAckStateToAckState, AbstractifyNodeIdentityToEndPoint)
	}

    
	function method CTombstoneTableLookup(src: EndPoint, t: CTombstoneTable) : nat 
		requires EndPointIsValid(src)
		requires CTombstoneTableIsValid(t)
		ensures CTombstoneTableLookup(src, t) == TombstoneTableLookup(AbstractifyEndPointToNodeIdentity(src), AbstractifyCTombstoneTableToTombstoneTable(t))
	{
		if src in t then 
			t[src] 
		else 
			0
	}

	function method CAckStateLookup(src: EndPoint, sendState: CSendState) : CAckState 
		requires EndPointIsValid(src)
		requires CSendStateIsValid(sendState)
		ensures var lr := AckStateLookup(AbstractifyEndPointToNodeIdentity(src), AbstractifyCSendStateToSendState(sendState)); var cr := CAckStateLookup(src, sendState); CAckStateIsValid(cr) && (AbstractifyCAckStateToAckState(cr)) == (lr)
	{
		if src in sendState then 
			sendState[src] 
		else 
			CAckState(0, [])
	}

    function method CSingleDelivery_Init() : CSingleDeliveryAcct 
        ensures var lr := SingleDelivery_Init(); var cr := CSingleDelivery_Init(); CSingleDeliveryAcctIsValid(cr) && (AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(cr)) == (lr)
	{
		CSingleDeliveryAcct(map[], map[])
	}


	function method CMessageNotReceived(s: CSingleDeliveryAcct, src: EndPoint, sm: CSingleMessage) : bool 
		requires CSingleDeliveryAcctIsValid(s)
		requires EndPointIsValid(src)
		requires CSingleMessageIsValid(sm)
		ensures CMessageNotReceived(s, src, sm) == MessageNotReceived(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyEndPointToNodeIdentity(src), AbstractifyCSingleMessageToSingleMessage(sm))
	{
		sm.CSingleMessage? 
		&& 
		sm.seqno > CTombstoneTableLookup(src, s.receiveState)
	}

    function method CNewSingleMessage(s: CSingleDeliveryAcct, pkt: CPacket) : bool 
		requires CSingleDeliveryAcctIsValid(s)
		requires CPacketIsValid(pkt)
		ensures CNewSingleMessage(s, pkt) == NewSingleMessage(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCPacketToShtPacket(pkt))
	{
		pkt.msg.CSingleMessage? 
		&& 
		var last_seqno := CTombstoneTableLookup(pkt.src, s.receiveState); 		
		pkt.msg.seqno == last_seqno + 1
	}

	function method CTruncateUnAckList(unAcked: seq<CSingleMessage>, seqnoAcked: nat) : seq<CSingleMessage> 
		requires (forall i :: i in unAcked ==> CSingleMessageIsValid(i))
		ensures (forall m :: m in CTruncateUnAckList(unAcked, seqnoAcked) ==> m in unAcked)
		ensures var lr := TruncateUnAckList(AbstractifySeq(unAcked, AbstractifyCSingleMessageToSingleMessage), seqnoAcked); var cr := CTruncateUnAckList(unAcked, seqnoAcked); (forall i :: i in cr ==> CSingleMessageIsValid(i)) && (AbstractifySeq(cr, AbstractifyCSingleMessageToSingleMessage)) == (lr)
	{
        /** Manually Added */
        assert forall sm :: sm in unAcked ==> CSingleMessageIsAbstractable(sm);

		if |unAcked| > 0 && unAcked[0].CSingleMessage? && unAcked[0].seqno <= seqnoAcked then 
			CTruncateUnAckList(unAcked[1..], seqnoAcked) 
		else 
			unAcked
	}

	/** 5 lines manual code for I1 */
	function method CReceiveAck(s: CSingleDeliveryAcct, pkt: CPacket) : (CSingleDeliveryAcct, seq<CPacket>) 
		requires CSingleDeliveryAcctIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CAck?
		ensures var (s', acks) := CReceiveAck(s, pkt); 
			CSingleDeliveryAcctIsValid(s') 
			&& (forall i :: i in acks ==> CPacketIsValid(i)) 
			&& ReceiveAck(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s'), AbstractifyCPacketToShtPacket(pkt), SeqToSet(AbstractifySeq(acks, AbstractifyCPacketToShtPacket)))
	{
		// var t1 := 
			var oldAckState := 
				CAckStateLookup(pkt.src, s.sendState); 			
			// var t1 := 
				var msgs := 
					CTruncateUnAckList(oldAckState.unAcked, pkt.msg.ack_seqno); 				
				// var t1 := 
					var newAckState := 
						oldAckState.(numPacketsAcked := pkt.msg.ack_seqno, unAcked := msgs); 					
					// var t1 := 
					// 	[]; 					
					// var t2 := 
						if pkt.msg.ack_seqno > oldAckState.numPacketsAcked then 
							// var t1 := 
								(s.(sendState := s.sendState[pkt.src := newAckState]), [])						
							// t1 
						else 
							// var t1 := 
								(s, []) 							
							// t1; 					
					// (t2, t1); 				
		// 		(t1.0, t1.1); 			
		// 	(t1.0, t1.1); 		
		// (t1.0, t1.1)
	}

    function method CShouldAckSingleMessage(s: CSingleDeliveryAcct, pkt: CPacket) : bool 
		requires CSingleDeliveryAcctIsValid(s)
		requires CPacketIsValid(pkt)
		ensures CShouldAckSingleMessage(s, pkt) == ShouldAckSingleMessage(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCPacketToShtPacket(pkt))
	{
		pkt.msg.CSingleMessage? 
		&& 
		var last_seqno := CTombstoneTableLookup(pkt.src, s.receiveState); 		
		pkt.msg.seqno <= last_seqno
	}

	/** 2 line manual code for I1 */
    function method CSendAck(s: CSingleDeliveryAcct, pkt: CPacket) : (CPacket, seq<CPacket>) 
		requires CSingleDeliveryAcctIsValid(s)
		requires CPacketIsValid(pkt)
		requires CShouldAckSingleMessage(s, pkt)
		ensures var (ack, acks) := CSendAck(s, pkt); 
            CPacketIsValid(ack) 
            && (forall i :: i in acks ==> CPacketIsValid(i)) 
            && SendAck(
                AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), 
                AbstractifyCPacketToShtPacket(pkt), 
                AbstractifyCPacketToShtPacket(ack), 
                SeqToSet(AbstractifySeq(acks, AbstractifyCPacketToShtPacket)))
	{
		// var t1 := 
            var m := CAck(pkt.msg.seqno); 
            var t1 := CPacket(dst := pkt.src, src := pkt.dst, msg := m); 
            // var t2 := [t1]; 
            (t1, [t1])
            // (t1, t2); 		
		// (t1.1, t1.0)
	}

    
	function method CMaybeAckPacket(s: CSingleDeliveryAcct, pkt: CPacket) : (CPacket, seq<CPacket>) 
		requires CSingleDeliveryAcctIsValid(s)
		requires CPacketIsValid(pkt)
		ensures var (ack, acks) := CMaybeAckPacket(s, pkt); 
            CPacketIsValid(ack) 
            && (forall i :: i in acks ==> CPacketIsValid(i)) 
            && MaybeAckPacket(
                AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), 
                AbstractifyCPacketToShtPacket(pkt), 
                AbstractifyCPacketToShtPacket(ack), 
                SeqToSet(AbstractifySeq(acks, AbstractifyCPacketToShtPacket)))
	{
		// var t1 := 
            if CShouldAckSingleMessage(s, pkt) then 
                var t1 := CSendAck(s, pkt); 
                (t1.0, t1.1) 
            else 
                // var t1 := pkt; 
                // var t2 := []; 
                (pkt, [])
                // (t1, t2); 		
		// (t1.1, t1.0)
	}

	function method CReceiveRealPacket(s: CSingleDeliveryAcct, pkt: CPacket) : CSingleDeliveryAcct 
		requires CSingleDeliveryAcctIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CSingleMessage?
		ensures var s' := CReceiveRealPacket(s, pkt); CSingleDeliveryAcctIsValid(s') && ReceiveRealPacket(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s'), AbstractifyCPacketToShtPacket(pkt))
	{
		// var t1 := 
			if CNewSingleMessage(s, pkt) then 
				// var t1 := 
					var last_seqno := 
						CTombstoneTableLookup(pkt.src, s.receiveState); 					
					// var t1 := 
						s.(receiveState := s.receiveState[pkt.src := last_seqno + 1])				
					// t1; 				
				// t1 
			else 
				// var t1 := 
					s			
				// t1; 		
		// t1
	}

    function method CUnAckedMsgForDst(s: CSingleDeliveryAcct, msg: CSingleMessage, dst: EndPoint) : bool 
		requires CSingleDeliveryAcctIsValid(s)
		requires CSingleMessageIsValid(msg)
		requires EndPointIsValid(dst)
		ensures CUnAckedMsgForDst(s, msg, dst) == UnAckedMsgForDst(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCSingleMessageToSingleMessage(msg), AbstractifyEndPointToNodeIdentity(dst))
	{
		dst in s.sendState 
		&& 
		msg in s.sendState[dst].unAcked
	}

	/** 4 lines manual code for I1 */
	function method CReceiveSingleMessage(s: CSingleDeliveryAcct, pkt: CPacket) : (CSingleDeliveryAcct, CPacket, seq<CPacket>) 
		requires CSingleDeliveryAcctIsValid(s)
		requires CPacketIsValid(pkt)
		ensures var (s', ack, acks) := CReceiveSingleMessage(s, pkt); CSingleDeliveryAcctIsValid(s') && CPacketIsValid(ack) && (forall i :: i in acks ==> CPacketIsValid(i)) && ReceiveSingleMessage(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s'), AbstractifyCPacketToShtPacket(pkt), AbstractifyCPacketToShtPacket(ack), SeqToSet(AbstractifySeq(acks, AbstractifyCPacketToShtPacket)))
	{
		// var t1 := 
			if pkt.msg.CAck? then 
				var t1 := 
					CReceiveAck(s, pkt); 				
				// var t2 := 
				// 	pkt; 				
				(t1.0, pkt, t1.1) 
			else 
				// var t1 := 
					if pkt.msg.CSingleMessage? then 
						var t1 := 
							CReceiveRealPacket(s, pkt); 						
						var t2 := 
							CMaybeAckPacket(t1, pkt); 						
						(t1, t2.0, t2.1) 
					else 
						// var t1 := 
						// 	s; 						
						// var t2 := 
						// 	pkt; 						
						// var t3 := 
						// 	[]; 						
						(s, pkt, [])			
		// 		(t1.2, t1.1, t1.0); 		
		// (t1.2, t1.1, t1.0)
	}

    function method CHighestSeqnoSent(s: CSingleDeliveryAcct, dst: EndPoint) : nat 
		requires CSingleDeliveryAcctIsValid(s)
		requires EndPointIsValid(dst)
		ensures CHighestSeqnoSent(s, dst) == HighestSeqnoSent(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyEndPointToNodeIdentity(dst))
	{
		var ackState := CAckStateLookup(dst, s.sendState); 		
		ackState.numPacketsAcked + |ackState.unAcked|
	}

	/** 5 lines manual code for I1 */
	function method CSendSingleMessageReal(s: CSingleDeliveryAcct, m: CMessage, dst: EndPoint, params: CParameters) : (CSingleDeliveryAcct, CSingleMessage, bool) 
		requires CSingleDeliveryAcctIsValid(s)
		requires CMessageIsValid(m)
		requires EndPointIsValid(dst)
		requires CParametersIsValid(params)
		// ensures CSendSingleMessageReal(s, s', m, dst, sm, params, shouldSend) ==> CSendSingleMessage(s, s', m, sm, params, shouldSend)
		ensures var (s', sm, shouldSend) := CSendSingleMessageReal(s, m, dst, params); 
			CSingleDeliveryAcctIsValid(s') 
			&& CSingleMessageIsValid(sm) 
			&& SendSingleMessageReal(
				AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), 
				AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s'), 
				AbstractifyCMessageToMessage(m), 
				AbstractifyEndPointToNodeIdentity(dst), 
				AbstractifyCSingleMessageToSingleMessage(sm), 
				AbstractifyCParametersToParameters(params), 
				shouldSend)
	{
		/** Manually Added */
		ghost var ss := AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s);
		ghost var sdst := AbstractifyEndPointToNodeIdentity(dst);
		ghost var smsg := AbstractifyCMessageToMessage(m);
		ghost var soldAckState := AckStateLookup(sdst, ss.sendState);

		// var t1 := 
			var oldAckState := 
				CAckStateLookup(dst, s.sendState); 			
			// var t1 := 
				var new_seqno := 
					oldAckState.numPacketsAcked + |oldAckState.unAcked| + 1; 				
				// var t1 := 
					if new_seqno > params.max_seqno then 
						(s, CSingleMessage(0, dst, m), false)
						// var t1 := 
						// 	s; 						
						// var t2 := 
						// 	false; 						
						// var t3 := 
						// 	CSingleMessage(0, dst, m); 						
						// (t1, t3, t2) 
					else 
						// var t1 := 
							var new_sm := 
								CSingleMessage(new_seqno, dst, m); 							
							// var t1 := 
							// 	new_sm; 							
							// var t2 := 
							// 	s.(sendState := s.sendState[new_sm.dst := oldAckState.(unAcked := oldAckState.unAcked + [new_sm])]); 							
							// var t3 := 
							// 	true; 	

							/** Manually Added */						
							ghost var unackseq := oldAckState.unAcked + [new_sm];
        					ghost var ssm := SingleMessage((soldAckState.numPacketsAcked + |soldAckState.unAcked| + 1), sdst, smsg);
        					ghost var sunackseq := soldAckState.unAcked + [ssm];
							assert AbstractifySeq(unackseq, AbstractifyCSingleMessageToSingleMessage) == sunackseq;
							(s.(sendState := s.sendState[new_sm.dst := oldAckState.(unAcked := oldAckState.unAcked + [new_sm])]), new_sm, true)
							// (t2, t1, t3)					
		// 				(t1.0, t1.1, t1.2); 				
		// 		(t1.0, t1.1, t1.2); 			
		// 	(t1.2, t1.1, t1.0); 		
		// (t1.2, t1.1, t1.0)
	}

/************************** AutoMan Translation End ************************/

/************************** Manually Written for I0 ************************/
method CUnAckedMessages(s:CSingleDeliveryAcct, src:EndPoint) returns (out:seq<CPacket>)
    requires CSingleDeliveryAcctIsValid(s)
    requires EndPointIsValid(src)
    ensures SeqIsValid(out, CPacketIsValid)
    ensures SeqIsAbstractable(out, AbstractifyCPacketToShtPacket)
    ensures SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)) == UnAckedMessages(
                    AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s),
                    AbstractifyEndPointToNodeIdentity(src)
                )
{
    // set dst, i | dst in s.sendState && 0 <= i < |s.sendState[dst].unAcked| && s.sendState[dst].unAcked[i].CSingleMessage? :: 
    //     // var sm := s.sendState[dst].unAcked[i];
    //     CPacket(s.sendState[dst].unAcked[i].dst, src, s.sendState[dst].unAcked[i])
    var pkt_set := set dst, i | dst in s.sendState && 0 <= i < |s.sendState[dst].unAcked| && s.sendState[dst].unAcked[i].CSingleMessage? :: 
        var sm := s.sendState[dst].unAcked[i];
        CPacket(sm.dst, src, sm);
    out := SetToUniqueSeqConstruct(pkt_set);

    assert forall e :: e in s.sendState ==> forall sm :: sm in s.sendState[e].unAcked ==> CSingleMessageIsAbstractable(sm);
    assert forall e :: e in s.sendState ==> forall sm :: sm in s.sendState[e].unAcked && sm.CSingleMessage? ==> EndPointIsAbstractable(sm.dst);

    ghost var r_pkt_set := AbstractifySet(pkt_set, AbstractifyCPacketToShtPacket);
    ghost var r_acct := AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s);
    ghost var r_src := AbstractifyEndPointToNodeIdentity(src);
    ghost var g_set := UnAckedMessages(r_acct, r_src);

    forall p | p in g_set
        ensures p in r_pkt_set;
    {
        var dst, i :| dst in r_acct.sendState && 0 <= i < |r_acct.sendState[dst].unAcked| && r_acct.sendState[dst].unAcked[i].SingleMessage? 
            && (var sm := r_acct.sendState[dst].unAcked[i]; p.dst == sm.dst && p.src == r_src && p.msg == sm); // Needed for the OBSERVE on the next line
        assert AckStateLookup(dst, r_acct.sendState) == r_acct.sendState[dst];  // OBSERVE

        var c_dst :| c_dst in s.sendState && AbstractifyEndPointToNodeIdentity(c_dst) == dst;
        var c_sm := s.sendState[c_dst].unAcked[i];
        var cp := CPacket(c_sm.dst, src, c_sm);
        assert c_sm.CSingleMessage?;
        assert cp in pkt_set;       // OBSERVE
    }
}
/************************** Manually Written for I0 End ************************/

predicate CSendSingleMessage(s:CSingleDeliveryAcct, s':CSingleDeliveryAcct, m:CMessage, sm:CSingleMessage, params:CParameters, shouldSend:bool)
    requires CSingleDeliveryAcctIsValid(s)
    requires CSingleMessageIsValid(sm)
{
       sm.CSingleMessage? 
    && sm.m == m
    && var oldAckState := CAckStateLookup(sm.dst, s.sendState); 
       var new_seqno := oldAckState.numPacketsAcked + |oldAckState.unAcked| + 1;
       if new_seqno > params.max_seqno then
           s' == s && !shouldSend // Packet shouldn't be sent if we exceed the maximum sequence number
       else
           (s' == s.(sendState := s.sendState[sm.dst := oldAckState.(unAcked := oldAckState.unAcked + [sm])])
            && sm.seqno == new_seqno
            && shouldSend)
}


}