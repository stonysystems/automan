/**********************************************************************
AUTOMAN LOG

[Module] SHT__SingleDelivery_i

[Action] ReceiveAck
Check passed

[Action] SendAck
Check passed

[Action] MaybeAckPacket
Check passed

[Action] ReceiveRealPacket
Check passed

[Action] ReceiveSingleMessage
Check passed

[Action] SendSingleMessageReal
Check passed
**********************************************************************/

include ""


module Impl_SHT__SingleDelivery_i 
{
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
		AbstractifyMap(s, AbstractifyEndPointToNodeIdentity, AbstractifyAckStateToCAckState, AbstractifyNodeIdentityToEndPoint)
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

	function method CTombstoneTableLookup(src: EndPoint, t: CTombstoneTable) : nat 
		requires EndPointIsValid(src)
		requires CTombstoneTableIsValid(t)
		ensures var lr := TombstoneTableLookup(AbstractifyEndPointToNodeIdentity(src), AbstractifyCTombstoneTableToTombstoneTable(t)); var cr := CTombstoneTableLookup(src, t); (cr) == (lr)
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
		ensures var lr := MessageNotReceived(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyEndPointToNodeIdentity(src), AbstractifyCSingleMessageToSingleMessage(sm)); var cr := CMessageNotReceived(s, src, sm); (cr) == (lr)
	{
		sm.CSingleMessage? 
		&& 
		sm.seqno > CTombstoneTableLookup(src, s.receiveState)
	}

	function method CNewSingleMessage(s: CSingleDeliveryAcct, pkt: CPacket) : bool 
		requires CSingleDeliveryAcctIsValid(s)
		requires CPacketIsValid(pkt)
		ensures var lr := NewSingleMessage(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCPacketToPacket(pkt)); var cr := CNewSingleMessage(s, pkt); (cr) == (lr)
	{
		pkt.msg.CSingleMessage? 
		&& 
		var last_seqno := 
			CTombstoneTableLookup(pkt.src, s.receiveState); 		
		pkt.msg.seqno == last_seqno + 1
	}

	function method CTruncateUnAckList(unAcked: seq<CSingleMessage>, seqnoAcked: nat) : seq<CSingleMessage> 
		requires (forall i :: i in unAcked ==> CSingleMessageIsValid(i))
		ensures (forall m :: m in CTruncateUnAckList(unAcked, seqnoAcked) ==> m in unAcked)
		ensures var lr := TruncateUnAckList(AbstractifySeq(unAcked, AbstractifyCSingleMessageToSingleMessage), seqnoAcked); var cr := CTruncateUnAckList(unAcked, seqnoAcked); (forall i :: i in cr ==> CSingleMessageIsValid(i)) && (AbstractifySeq(cr, AbstractifyCSingleMessageToSingleMessage)) == (lr)
	{
		if |unAcked| > 0 && unAcked[0].CSingleMessage? && unAcked[0].seqno <= seqnoAcked then 
			CTruncateUnAckList(unAcked[1 .. ], seqnoAcked) 
		else 
			unAcked
	}

	function method CReceiveAck(s: CSingleDeliveryAcct, pkt: CPacket) : (CSingleDeliveryAcct, set<CPacket>) 
		requires CSingleDeliveryAcctIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CAck?
		ensures var (s', acks) := CReceiveAck(s, pkt); CSingleDeliveryAcctIsValid(s') && (forall i :: i in acks ==> CPacketIsValid(i)) && ReceiveAck(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s'), AbstractifyCPacketToPacket(pkt), AbstractifySet(acks, AbstractifyCPacketToPacket))
	{
		var t1 := 
			var oldAckState := 
				CAckStateLookup(pkt.src, s.sendState); 			
			var t1 := 
				var msgs := 
					CTruncateUnAckList(oldAckState.unAcked, pkt.msg.ack_seqno); 				
				var t1 := 
					var newAckState := 
						oldAckState.(numPacketsAcked := pkt.msg.ack_seqno, unAcked := msgs); 					
					var t1 := 
						{}; 					
					var t2 := 
						if pkt.msg.ack_seqno > oldAckState.numPacketsAcked then 
							var t1 := 
								s.(sendState := s.sendState[pkt.src := newAckState]); 							
							t1 
						else 
							var t1 := 
								s; 							
							t1; 					
					(t2, t1); 				
				(t1.1, t1.0); 			
			(t1.1, t1.0); 		
		(t1.1, t1.0)
	}

	function method CShouldAckSingleMessage(s: CSingleDeliveryAcct, pkt: CPacket) : bool 
		requires CSingleDeliveryAcctIsValid(s)
		requires CPacketIsValid(pkt)
		ensures var lr := ShouldAckSingleMessage(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCPacketToPacket(pkt)); var cr := CShouldAckSingleMessage(s, pkt); (cr) == (lr)
	{
		pkt.msg.CSingleMessage? 
		&& 
		var last_seqno := 
			CTombstoneTableLookup(pkt.src, s.receiveState); 		
		pkt.msg.seqno <= last_seqno
	}

	function method CSendAck(s: CSingleDeliveryAcct, pkt: CPacket) : (CPacket, set<CPacket>) 
		requires CSingleDeliveryAcctIsValid(s)
		requires CPacketIsValid(pkt)
		requires CShouldAckSingleMessage(s, pkt)
		ensures var (ack, acks) := CSendAck(s, pkt); CPacketIsValid(ack) && (forall i :: i in acks ==> CPacketIsValid(i)) && SendAck(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCPacketToPacket(pkt), AbstractifyCPacketToPacket(ack), AbstractifySet(acks, AbstractifyCPacketToPacket))
	{
		var t1 := 
			var m := 
				CAck(pkt.msg.seqno); 			
			var t1 := 
				CPacket(dst := pkt.src, src := pkt.dst, msg := m); 			
			var t2 := 
				{t1}; 			
			(t1, t2); 		
		(t1.1, t1.0)
	}

	function method CMaybeAckPacket(s: CSingleDeliveryAcct, pkt: CPacket) : (CPacket, set<CPacket>) 
		requires CSingleDeliveryAcctIsValid(s)
		requires CPacketIsValid(pkt)
		ensures var (ack, acks) := CMaybeAckPacket(s, pkt); CPacketIsValid(ack) && (forall i :: i in acks ==> CPacketIsValid(i)) && MaybeAckPacket(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCPacketToPacket(pkt), AbstractifyCPacketToPacket(ack), AbstractifySet(acks, AbstractifyCPacketToPacket))
	{
		var t1 := 
			if CShouldAckSingleMessage(s, pkt) then 
				var t1 := 
					CSendAck(s, pkt); 				
				(t1.0, t1.1) 
			else 
				var t1 := 
					pkt; 				
				var t2 := 
					{}; 				
				(t1, t2); 		
		(t1.1, t1.0)
	}

	function method CReceiveRealPacket(s: CSingleDeliveryAcct, pkt: CPacket) : CSingleDeliveryAcct 
		requires CSingleDeliveryAcctIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CSingleMessage?
		ensures var s' := CReceiveRealPacket(s, pkt); CSingleDeliveryAcctIsValid(s') && ReceiveRealPacket(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s'), AbstractifyCPacketToPacket(pkt))
	{
		var t1 := 
			if CNewSingleMessage(s, pkt) then 
				var t1 := 
					var last_seqno := 
						CTombstoneTableLookup(pkt.src, s.receiveState); 					
					var t1 := 
						s.(receiveState := s.receiveState[pkt.src := last_seqno + 1]); 					
					t1; 				
				t1 
			else 
				var t1 := 
					s; 				
				t1; 		
		t1
	}

	function method CUnAckedMsgForDst(s: CSingleDeliveryAcct, msg: CSingleMessage, dst: EndPoint) : bool 
		requires CSingleDeliveryAcctIsValid(s)
		requires CSingleMessageIsValid(msg)
		requires EndPointIsValid(dst)
		ensures var lr := UnAckedMsgForDst(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCSingleMessageToSingleMessage(msg), AbstractifyEndPointToNodeIdentity(dst)); var cr := CUnAckedMsgForDst(s, msg, dst); (cr) == (lr)
	{
		dst in s.sendState 
		&& 
		msg in s.sendState[dst].unAcked
	}

	function method CUnAckedMessages(s: CSingleDeliveryAcct, src: EndPoint) : set<CPacket> 
		requires CSingleDeliveryAcctIsValid(s)
		requires EndPointIsValid(src)
		ensures var lr := UnAckedMessages(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyEndPointToNodeIdentity(src)); var cr := CUnAckedMessages(s, src); (forall i :: i in cr ==> CPacketIsValid(i)) && (AbstractifySet(cr, AbstractifyCPacketToPacket)) == (lr)
	{
		(set dst, i | dst in s.sendState && 0 <= i && i < |s.sendState[dst].unAcked| && s.sendState[dst].unAcked[i].CSingleMessage? :: var sm := s.sendState[dst].unAcked[i]; CPacket(sm.dst, src, sm))
	}

	function method CReceiveSingleMessage(s: CSingleDeliveryAcct, pkt: CPacket) : (CSingleDeliveryAcct, CPacket, set<CPacket>) 
		requires CSingleDeliveryAcctIsValid(s)
		requires CPacketIsValid(pkt)
		ensures var (s', ack, acks) := CReceiveSingleMessage(s, pkt); CSingleDeliveryAcctIsValid(s') && CPacketIsValid(ack) && (forall i :: i in acks ==> CPacketIsValid(i)) && ReceiveSingleMessage(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s'), AbstractifyCPacketToPacket(pkt), AbstractifyCPacketToPacket(ack), AbstractifySet(acks, AbstractifyCPacketToPacket))
	{
		var t1 := 
			if pkt.msg.CAck? then 
				var t1 := 
					CReceiveAck(s, pkt); 				
				var t2 := 
					pkt; 				
				(t1.0, t2, t1.1) 
			else 
				var t1 := 
					if pkt.msg.CSingleMessage? then 
						var t1 := 
							CReceiveRealPacket(s, pkt); 						
						var t2 := 
							CMaybeAckPacket(s', pkt); 						
						(t1, t2.0, t2.1) 
					else 
						var t1 := 
							s; 						
						var t2 := 
							pkt; 						
						var t3 := 
							{}; 						
						(t1, t2, t3); 				
				(t1.2, t1.1, t1.0); 		
		(t1.2, t1.1, t1.0)
	}

	function method CHighestSeqnoSent(s: CSingleDeliveryAcct, dst: EndPoint) : nat 
		requires CSingleDeliveryAcctIsValid(s)
		requires EndPointIsValid(dst)
		ensures var lr := HighestSeqnoSent(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyEndPointToNodeIdentity(dst)); var cr := CHighestSeqnoSent(s, dst); (cr) == (lr)
	{
		var ackState := 
			CAckStateLookup(dst, s.sendState); 		
		ackState.numPacketsAcked + |ackState.unAcked|
	}

	function method CSendSingleMessageReal(s: CSingleDeliveryAcct, m: CMessage, dst: EndPoint, params: CParameters) : (CSingleDeliveryAcct, CSingleMessage, bool) 
		requires CSingleDeliveryAcctIsValid(s)
		requires CMessageIsValid(m)
		requires EndPointIsValid(dst)
		requires CParametersIsValid(params)
		ensures CSendSingleMessageReal(s, s', m, dst, sm, params, shouldSend) ==> CSendSingleMessage(s, s', m, sm, params, shouldSend)
		ensures var (s', sm, shouldSend) := CSendSingleMessageReal(s, m, dst, params); CSingleDeliveryAcctIsValid(s') && CSingleMessageIsValid(sm) && SendSingleMessageReal(AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s), AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s'), AbstractifyCMessageToMessage(m), AbstractifyEndPointToNodeIdentity(dst), AbstractifyCSingleMessageToSingleMessage(sm), AbstractifyCParametersToParameters(params), shouldSend)
	{
		var t1 := 
			var oldAckState := 
				CAckStateLookup(dst, s.sendState); 			
			var t1 := 
				var new_seqno := 
					oldAckState.numPacketsAcked + |oldAckState.unAcked| + 1; 				
				var t1 := 
					if new_seqno > params.max_seqno then 
						var t1 := 
							s; 						
						var t2 := 
							false; 						
						var t3 := 
							CSingleMessage(0, dst, m); 						
						(t1, t3, t2) 
					else 
						var t1 := 
							var new_sm := 
								CSingleMessage(new_seqno, dst, m); 							
							var t1 := 
								new_sm; 							
							var t2 := 
								s.(sendState := s.sendState[new_sm.dst := oldAckState.(unAcked := oldAckState.unAcked + [new_sm])]); 							
							var t3 := 
								true; 							
							(t2, t1, t3); 						
						(t1.2, t1.1, t1.0); 				
				(t1.2, t1.1, t1.0); 			
			(t1.2, t1.1, t1.0); 		
		(t1.2, t1.1, t1.0)
	}
}
