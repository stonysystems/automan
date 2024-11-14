/**********************************************************************
AUTOMAN LOG

[Module] SHT__Host_i

[Action] Host_Init
Check passed

[Action] NextGetRequestReal
Check passed

[Action] NextSetRequestReal
Check passed

[Action] NextDelegateReal
Check passed

[Action] NextShardReal
Check passed

[Action] NextReplyReal
Check passed

[Action] NextRedirectReal
Check passed
**********************************************************************/

include ""


module Impl_SHT__Host_i 
{

	datatype CConstants = 
	CConstants(
		rootIdentity: EndPoint, 
		hostIds: seq<EndPoint>, 
		params: CParameters
	)

	predicate CConstantsIsValid(s: CConstants) 
	{
		CConstantsIsAbstractable(s) 
		&& 
		EndPointIsValid(s.rootIdentity) 
		&& 
		(forall i :: i in s.hostIds ==> EndPointIsValid(i)) 
		&& 
		CParametersIsValid(s.params)
	}

	predicate CConstantsIsAbstractable(s: CConstants) 
	{
		EndPointIsAbstractable(s.rootIdentity) 
		&& 
		(forall i :: i in s.hostIds ==> EndPointIsAbstractable(i)) 
		&& 
		CParametersIsAbstractable(s.params)
	}

	function AbstractifyCConstantsToConstants(s: CConstants) : Constants 
		requires CConstantsIsAbstractable(s)
	{
		Constants(AbstractifyEndPointToNodeIdentity(s.rootIdentity), AbstractifySeq(s.hostIds, AbstractifyEndPointToNodeIdentity), AbstractifyCParametersToParameters(s.params))
	}

	datatype CHost = 
	CHost(
		constants: CConstants, 
		me: EndPoint, 
		ghost delegationMap: CDelegationMap, 
		h: Hashtable, 
		sd: CSingleDeliveryAcct, 
		receivedPacket: COption<CPacket>, 
		numDelegations: int, 
		ghost receivedRequests: seq<AppRequest>
	)

	predicate CHostIsValid(s: CHost) 
	{
		CHostIsAbstractable(s) 
		&& 
		CConstantsIsValid(s.constants) 
		&& 
		EndPointIsValid(s.me) 
		&& 
		CDelegationMapIsValid(s.delegationMap) 
		&& 
		HashtableIsValid(s.h) 
		&& 
		CSingleDeliveryAcctIsValid(s.sd) 
		&& 
		(forall i :: i in s.receivedRequests ==> AppRequestIsValid(i))
	}

	predicate CHostIsAbstractable(s: CHost) 
	{
		CConstantsIsAbstractable(s.constants) 
		&& 
		EndPointIsAbstractable(s.me) 
		&& 
		CDelegationMapIsAbstractable(s.delegationMap) 
		&& 
		HashtableIsAbstractable(s.h) 
		&& 
		CSingleDeliveryAcctIsAbstractable(s.sd) 
		&& 
		(forall i :: i in s.receivedRequests ==> AppRequestIsAbstractable(i))
	}

	function AbstractifyCHostToHost(s: CHost) : Host 
		requires CHostIsAbstractable(s)
	{
		Host(AbstractifyCConstantsToConstants(s.constants), AbstractifyEndPointToNodeIdentity(s.me), AbstractifyCDelegationMapToDelegationMap(s.delegationMap), AbstractifyHashtableToHashtable(s.h), AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s.sd), , s.numDelegations, AbstractifySeq(s.receivedRequests, AbstractifyAppRequestToAppRequest))
	}

	function method CSHTPacketToPacket(lp: CSHTPacket) : CPacket 
		requires CSHTPacketIsValid(lp)
		ensures var lr := LSHTPacketToPacket(AbstractifyCSHTPacketToLSHTPacket(lp)); var cr := CSHTPacketToPacket(lp); CPacketIsValid(cr) && (AbstractifyCPacketToPacket(cr)) == (lr)
	{
		CPacket(lp.dst, lp.src, lp.msg)
	}

	function method CValidKeyPlus(key: KeyPlus) : bool 
		requires KeyPlusIsValid(key)
		ensures var lr := ValidKeyPlus(AbstractifyKeyPlusToKeyPlus(key)); var cr := CValidKeyPlus(key); (cr) == (lr)
	{
		(key.CKeyZero?) || ((key.CKeyInf?) || (CValidKey(key.k)))
	}

	function method CValidOptionalValue(opt: OptionalValue) : bool 
		requires OptionalValueIsValid(opt)
		ensures var lr := ValidOptionalValue(AbstractifyOptionalValueToOptionalValue(opt)); var cr := CValidOptionalValue(opt); (cr) == (lr)
	{
		(opt.CValueAbsent?) || (CValidValue(opt.v))
	}

	function method CValidKeyRange(kr: KeyRange) : bool 
		requires KeyRangeIsValid(kr)
		ensures var lr := ValidKeyRange(AbstractifyKeyRangeToKeyRange(kr)); var cr := CValidKeyRange(kr); (cr) == (lr)
	{
		CValidKeyPlus(kr.klo) 
		&& 
		CValidKeyPlus(kr.khi)
	}

	function method CExtractPacketsFromLSHTPackets(seqPackets: seq<CSHTPacket>) : set<CPacket> 
		requires (forall i :: i in seqPackets ==> CSHTPacketIsValid(i))
		ensures (forall p :: p in seqPackets <==> CPacket(p.dst, p.src, p.msg) in CExtractPacketsFromLSHTPackets(seqPackets))
		ensures var lr := ExtractPacketsFromLSHTPackets(AbstractifySeq(seqPackets, AbstractifyCSHTPacketToLSHTPacket)); var cr := CExtractPacketsFromLSHTPackets(seqPackets); (forall i :: i in cr ==> CPacketIsValid(i)) && (AbstractifySet(cr, AbstractifyCPacketToPacket)) == (lr)
	{
		CMapSeqToSet(seqPackets, LSHTPacketToPacket)
	}

	function method CDelegationMap_Init(rootIdentity: EndPoint) : CDelegationMap 
		requires EndPointIsValid(rootIdentity)
		ensures var lr := DelegationMap_Init(AbstractifyEndPointToNodeIdentity(rootIdentity)); var cr := CDelegationMap_Init(rootIdentity); CDelegationMapIsValid(cr) && (AbstractifyCDelegationMapToDelegationMap(cr)) == (lr)
	{
		(map k :: rootIdentity)
	}

	function method CHashtableLookup(h: Hashtable, k: Key) : OptionalValue 
		requires HashtableIsValid(h)
		requires KeyIsValid(k)
		ensures var lr := HashtableLookup(AbstractifyHashtableToHashtable(h), AbstractifyKeyToKey(k)); var cr := CHashtableLookup(h, k); OptionalValueIsValid(cr) && (AbstractifyOptionalValueToOptionalValue(cr)) == (lr)
	{
		if k in h then 
			CValuePresent(h[k]) 
		else 
			CValueAbsent()
	}

	function method CHost_Init(id: EndPoint, rootIdentity: EndPoint, hostIds: seq<EndPoint>, params: CParameters) : CHost 
		requires EndPointIsValid(id)
		requires EndPointIsValid(rootIdentity)
		requires (forall i :: i in hostIds ==> EndPointIsValid(i))
		requires CParametersIsValid(params)
		ensures var s := CHost_Init(id, rootIdentity, hostIds, params); CHostIsValid(s) && Host_Init(AbstractifyCHostToHost(s), AbstractifyEndPointToNodeIdentity(id), AbstractifyEndPointToNodeIdentity(rootIdentity), AbstractifySeq(hostIds, AbstractifyEndPointToNodeIdentity), AbstractifyCParametersToParameters(params))
	{
		var t1 := 
			CHost(CConstants(rootIdentity, hostIds, params), id, CDelegationMap_Init(rootIdentity), map[], CSingleDelivery_Init(), None, 1, []); 		
		t1
	}

	function method CNextGetRequest_Reply(s: CHost, s': CHost, src: EndPoint, seqno: int, k: Key, sm: CSingleMessage, m: CMessage, out: set<CPacket>, shouldSend: bool) : bool 
		requires CHostIsValid(s)
		requires CHostIsValid(s')
		requires EndPointIsValid(src)
		requires KeyIsValid(k)
		requires CSingleMessageIsValid(sm)
		requires CMessageIsValid(m)
		requires (forall i :: i in out ==> CPacketIsValid(i))
		requires k in s.delegationMap
		ensures var lr := NextGetRequest_Reply(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyEndPointToNodeIdentity(src), seqno, AbstractifyKeyToKey(k), AbstractifyCSingleMessageToSingleMessage(sm), AbstractifyCMessageToMessage(m), AbstractifySet(out, AbstractifyCPacketToPacket), shouldSend); var cr := CNextGetRequest_Reply(s, s', src, seqno, k, sm, m, out, shouldSend); (cr) == (lr)
	{
		var owner := 
			CDelegateForKey(s.delegationMap, k); 		
		if shouldSend && CValidKey(k) then 
			if owner == s.me then m == CReply(k, CHashtableLookup(s.h, k)) && s'.receivedRequests == s.receivedRequests + [CAppGetRequest(seqno, k)] else m == CRedirect(k, owner) && s'.receivedRequests == s.receivedRequests 
			&& 
			CSendSingleMessage(s.sd, s'.sd, m, sm, s.constants.params, shouldSend) 
			&& 
			sm.dst == src 
			&& 
			out == {CPacket(src, s.me, sm)} 
			&& 
			s'.receivedPacket == None 
		else 
			s' == s.(receivedPacket := None) 
			&& 
			out == {}
	}

	function method CNextGetRequest(s: CHost, s': CHost, pkt: CPacket, out: set<CPacket>) : bool 
		requires CHostIsValid(s)
		requires CHostIsValid(s')
		requires CPacketIsValid(pkt)
		requires (forall i :: i in out ==> CPacketIsValid(i))
		requires pkt.msg.CSingleMessage?
		requires pkt.msg.m.CGetRequest? ==> pkt.msg.m.k_getrequest in s.delegationMap
		ensures var lr := NextGetRequest(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifySet(out, AbstractifyCPacketToPacket)); var cr := CNextGetRequest(s, s', pkt, out); (cr) == (lr)
	{
		pkt.msg.m.CGetRequest? 
		&& 
		s'.delegationMap == s.delegationMap 
		&& 
		s'.h == s.h 
		&& 
		s'.numDelegations == s.numDelegations 
		&& 
		(exists sm, m, b :: CNextGetRequest_Reply(s, s', pkt.src, pkt.msg.seqno, pkt.msg.m.k_getrequest, sm, m, out, b))
	}

	function method CNextGetRequestReal(s: CHost, pkt: CPacket) : (CHost, CSingleMessage, CMessage, set<CPacket>, bool) 
		requires CHostIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CSingleMessage?
		requires pkt.msg.m.CGetRequest?
		requires pkt.msg.m.k_getrequest in s.delegationMap
		ensures CNextGetRequestReal(s, s', pkt, sm, m, out, shouldSend) ==> CNextGetRequest_Reply(s, s', pkt.src, pkt.msg.seqno, pkt.msg.m.k_getrequest, sm, m, out, shouldSend) ==> (exists sm1, m1, b :: CNextGetRequest_Reply(s, s', pkt.src, pkt.msg.seqno, pkt.msg.m.k_getrequest, sm1, m1, out, b))
		ensures CNextGetRequestReal(s, s', pkt, sm, m, out, shouldSend) ==> CNextGetRequest(s, s', pkt, out)
		ensures var (s', sm, m, out, shouldSend) := CNextGetRequestReal(s, pkt); CHostIsValid(s') && CSingleMessageIsValid(sm) && CMessageIsValid(m) && (forall i :: i in out ==> CPacketIsValid(i)) && NextGetRequestReal(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifyCSingleMessageToSingleMessage(sm), AbstractifyCMessageToMessage(m), AbstractifySet(out, AbstractifyCPacketToPacket), shouldSend)
	{
		var t1 := 
			var k := 
				pkt.msg.m.k_getrequest; 			
			var t1 := 
				var src := 
					pkt.src; 				
				var t1 := 
					var seqno := 
						pkt.msg.seqno; 					
					var t1 := 
						var owner := 
							CDelegateForKey(s.delegationMap, k); 						
						var t1 := 
							var newReceivedRequests := 
								if owner == s.me then 
									s.receivedRequests + [CAppGetRequest(seqno, k)] 
								else 
									s.receivedRequests; 							
							var t1 := 
								var msg := 
									if owner == s.me then 
										CReply(k, CHashtableLookup(s.h, k)) 
									else 
										CRedirect(k, owner); 								
								var t1 := 
									CSendSingleMessageReal(s.sd, msg, src, s.constants.params); 								
								var t2 := 
									if CValidKey(k) && holder then 
										var t1 := 
											msg; 										
										var t2 := 
											s.(sd := t1.0, receivedRequests := newReceivedRequests, receivedPacket := None); 										
										var t3 := 
											{CPacket(src, s.me, t1.1)}; 										
										(t2, t1, t3) 
									else 
										var t1 := 
											s.(receivedPacket := None); 										
										var t2 := 
											msg; 										
										var t3 := 
											{}; 										
										(t1, t2, t3); 								
								(t2.2, t1.1, t2.1, t2.0, t1.2); 							
							(t1.4, t1.3, t1.2, t1.1, t1.0); 						
						(t1.4, t1.3, t1.2, t1.1, t1.0); 					
					(t1.4, t1.3, t1.2, t1.1, t1.0); 				
				(t1.4, t1.3, t1.2, t1.1, t1.0); 			
			(t1.4, t1.3, t1.2, t1.1, t1.0); 		
		(t1.4, t1.3, t1.2, t1.1, t1.0)
	}

	function method CNextSetRequest_Complete(s: CHost, s': CHost, src: EndPoint, seqno: int, reqm: CMessage, sm: CSingleMessage, replym: CMessage, out: set<CPacket>, shouldSend: bool) : bool 
		requires CHostIsValid(s)
		requires CHostIsValid(s')
		requires EndPointIsValid(src)
		requires CMessageIsValid(reqm)
		requires CSingleMessageIsValid(sm)
		requires CMessageIsValid(replym)
		requires (forall i :: i in out ==> CPacketIsValid(i))
		requires reqm.CSetRequest?
		requires reqm.k_setrequest in s.delegationMap
		ensures var lr := NextSetRequest_Complete(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyEndPointToNodeIdentity(src), seqno, AbstractifyCMessageToMessage(reqm), AbstractifyCSingleMessageToSingleMessage(sm), AbstractifyCMessageToMessage(replym), AbstractifySet(out, AbstractifyCPacketToPacket), shouldSend); var cr := CNextSetRequest_Complete(s, s', src, seqno, reqm, sm, replym, out, shouldSend); (cr) == (lr)
	{
		var k := 
			reqm.k_setrequest; 		
		var ov := 
			reqm.v_setrequest; 		
		var owner := 
			CDelegateForKey(s.delegationMap, k); 		
		if shouldSend && CValidKey(k) && CValidOptionalValue(ov) then 
			if owner == s.me then s'.h == if ov.CValueAbsent? then Cmapremove(s.h, k) else s.h[k := ov.v] && replym == CReply(k, ov) && s'.receivedRequests == s.receivedRequests + [CAppSetRequest(seqno, k, ov)] else s'.h == s.h && replym == CRedirect(k, owner) && s'.receivedRequests == s.receivedRequests 
			&& 
			CSendSingleMessage(s.sd, s'.sd, replym, sm, s.constants.params, shouldSend) 
			&& 
			sm.dst == src 
			&& 
			out == {CPacket(src, s.me, sm)} 
			&& 
			s'.receivedPacket == None 
		else 
			s' == s.(receivedPacket := None) 
			&& 
			out == {}
	}

	function method CNextSetRequest(s: CHost, s': CHost, pkt: CPacket, out: set<CPacket>) : bool 
		requires CHostIsValid(s)
		requires CHostIsValid(s')
		requires CPacketIsValid(pkt)
		requires (forall i :: i in out ==> CPacketIsValid(i))
		requires pkt.msg.CSingleMessage?
		ensures var lr := NextSetRequest(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifySet(out, AbstractifyCPacketToPacket)); var cr := CNextSetRequest(s, s', pkt, out); (cr) == (lr)
	{
		pkt.msg.m.CSetRequest? 
		&& 
		pkt.msg.m.k_setrequest in s.delegationMap 
		&& 
		(exists sm, m, b :: CNextSetRequest_Complete(s, s', pkt.src, pkt.msg.seqno, pkt.msg.m, sm, m, out, b)) 
		&& 
		s'.delegationMap == s.delegationMap 
		&& 
		s'.numDelegations == s.numDelegations
	}

	function method CNextSetRequestReal(s: CHost, pkt: CPacket) : (CHost, CSingleMessage, CMessage, set<CPacket>, bool) 
		requires CHostIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CSingleMessage?
		requires pkt.msg.m.CSetRequest?
		requires pkt.msg.m.k_setrequest in s.delegationMap
		ensures CNextSetRequestReal(s, s', pkt, sm, replym, out, shouldSend) ==> CNextSetRequest_Complete(s, s', pkt.src, pkt.msg.seqno, pkt.msg.m, sm, replym, out, shouldSend) ==> (exists sm1, m1, b1 :: CNextSetRequest_Complete(s, s', pkt.src, pkt.msg.seqno, pkt.msg.m, sm1, m1, out, b1))
		ensures CNextSetRequestReal(s, s', pkt, sm, replym, out, shouldSend) ==> CNextSetRequest(s, s', pkt, out)
		ensures var (s', sm, replym, out, shouldSend) := CNextSetRequestReal(s, pkt); CHostIsValid(s') && CSingleMessageIsValid(sm) && CMessageIsValid(replym) && (forall i :: i in out ==> CPacketIsValid(i)) && NextSetRequestReal(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifyCSingleMessageToSingleMessage(sm), AbstractifyCMessageToMessage(replym), AbstractifySet(out, AbstractifyCPacketToPacket), shouldSend)
	{
		var t1 := 
			var k := 
				pkt.msg.m.k_setrequest; 			
			var t1 := 
				var ov := 
					pkt.msg.m.v_setrequest; 				
				var t1 := 
					var seqno := 
						pkt.msg.seqno; 					
					var t1 := 
						var src := 
							pkt.src; 						
						var t1 := 
							var owner := 
								CDelegateForKey(s.delegationMap, k); 							
							var t1 := 
								var newhtable := 
									if owner == s.me then 
										if ov.CValueAbsent? then 
											Cmapremove(s.h, k) 
										else 
											s.h[k := ov.v] 
									else 
										s.h; 								
								var t1 := 
									var msg := 
										if owner == s.me then 
											CReply(k, ov) 
										else 
											CRedirect(k, owner); 									
									var t1 := 
										var reqs := 
											if owner == s.me then 
												s.receivedRequests + [CAppSetRequest(seqno, k, ov)] 
											else 
												s.receivedRequests; 										
										var t1 := 
											CSendSingleMessageReal(s.sd, msg, src, s.constants.params); 										
										var t2 := 
											if holder && CValidKey(k) && CValidOptionalValue(ov) then 
												var t1 := 
													msg; 												
												var t2 := 
													s.(h := newhtable, sd := t1.0, receivedRequests := reqs, receivedPacket := None); 												
												var t3 := 
													{CPacket(src, s.me, t1.1)}; 												
												(t2, t1, t3) 
											else 
												var t1 := 
													msg; 												
												var t2 := 
													s.(receivedPacket := None); 												
												var t3 := 
													{}; 												
												(t2, t1, t3); 										
										(t2.2, t1.1, t2.1, t2.0, t1.2); 									
									(t1.4, t1.3, t1.2, t1.1, t1.0); 								
								(t1.4, t1.3, t1.2, t1.1, t1.0); 							
							(t1.4, t1.3, t1.2, t1.1, t1.0); 						
						(t1.4, t1.3, t1.2, t1.1, t1.0); 					
					(t1.4, t1.3, t1.2, t1.1, t1.0); 				
				(t1.4, t1.3, t1.2, t1.1, t1.0); 			
			(t1.4, t1.3, t1.2, t1.1, t1.0); 		
		(t1.4, t1.3, t1.2, t1.1, t1.0)
	}

	function method CNextDelegate(s: CHost, s': CHost, pkt: CPacket, out: set<CPacket>) : bool 
		requires CHostIsValid(s)
		requires CHostIsValid(s')
		requires CPacketIsValid(pkt)
		requires (forall i :: i in out ==> CPacketIsValid(i))
		requires pkt.msg.CSingleMessage?
		ensures var lr := NextDelegate(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifySet(out, AbstractifyCPacketToPacket)); var cr := CNextDelegate(s, s', pkt, out); (cr) == (lr)
	{
		pkt.msg.m.CDelegate? 
		&& 
		if pkt.src in s.constants.hostIds then s'.delegationMap == CUpdateDelegationMap(s.delegationMap, pkt.msg.m.range, s.me) && s'.h == CBulkUpdateHashtable(s.h, pkt.msg.m.range, pkt.msg.m.h) && s'.numDelegations == s.numDelegations + 1 else s'.delegationMap == s.delegationMap && s'.h == s.h && s'.numDelegations == s.numDelegations 
		&& 
		CSendNoMessage(s.sd, s'.sd) 
		&& 
		CReceiveNoMessage(s.sd, s'.sd) 
		&& 
		out == {} 
		&& 
		s'.receivedRequests == s.receivedRequests
	}

	function method CNextDelegateReal(s: CHost, pkt: CPacket) : (CHost, set<CPacket>) 
		requires CHostIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CSingleMessage?
		requires pkt.msg.m.CDelegate?
		ensures CNextDelegateReal(s, s', pkt, out) ==> CNextDelegate(s, s', pkt, out)
		ensures var (s', out) := CNextDelegateReal(s, pkt); CHostIsValid(s') && (forall i :: i in out ==> CPacketIsValid(i)) && NextDelegateReal(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifySet(out, AbstractifyCPacketToPacket))
	{
		var t1 := 
			if pkt.src in s.constants.hostIds then 
				var t1 := 
					CUpdateDelegationMap(s.delegationMap, pkt.msg.m.range, s.me); 				
				var t2 := 
					CBulkUpdateHashtable(s.h, pkt.msg.m.range, pkt.msg.m.h); 				
				var t3 := 
					s.numDelegations + 1; 				
				(t1, t2, t3) 
			else 
				var t1 := 
					s.delegationMap; 				
				var t2 := 
					s.h; 				
				var t3 := 
					s.numDelegations; 				
				(t1, t2, t3); 		
		var t2 := 
			{}; 		
		var t3 := 
			s.(delegationMap := t1.2, h := t1.1, numDelegations := t1.0, receivedPacket := None); 		
		(t3, t2)
	}

	function method CNextShard(s: CHost, s': CHost, out: set<CPacket>, kr: KeyRange, recipient: EndPoint, sm: CSingleMessage, shouldSend: bool) : bool 
		requires CHostIsValid(s)
		requires CHostIsValid(s')
		requires (forall i :: i in out ==> CPacketIsValid(i))
		requires KeyRangeIsValid(kr)
		requires EndPointIsValid(recipient)
		requires CSingleMessageIsValid(sm)
		ensures var lr := NextShard(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifySet(out, AbstractifyCPacketToPacket), AbstractifyKeyRangeToKeyRange(kr), AbstractifyEndPointToNodeIdentity(recipient), AbstractifyCSingleMessageToSingleMessage(sm), shouldSend); var cr := CNextShard(s, s', out, kr, recipient, sm, shouldSend); (cr) == (lr)
	{
		recipient != s.me 
		&& 
		recipient in s.constants.hostIds 
		&& 
		CDelegateForKeyRangeIsHost(s.delegationMap, kr, s.me) 
		&& 
		CSendSingleMessage(s.sd, s'.sd, CDelegate(kr, CExtractRange(s.h, kr)), sm, s.constants.params, shouldSend) 
		&& 
		recipient == sm.dst 
		&& 
		s.constants == s'.constants 
		&& 
		s'.numDelegations == s.numDelegations + 1 
		&& 
		s'.receivedRequests == s.receivedRequests 
		&& 
		s'.receivedPacket == None 
		&& 
		if shouldSend then 
			out == {CPacket(recipient, s.me, sm)} 
			&& 
			s'.delegationMap == CUpdateDelegationMap(s.delegationMap, kr, recipient) 
			&& 
			s'.h == CBulkRemoveHashtable(s.h, kr) 
		else 
			out == {} 
			&& 
			s'.delegationMap == s.delegationMap 
			&& 
			s'.h == s.h
	}

	function method CNextShard_Wrapper(s: CHost, s': CHost, pkt: CPacket, out: set<CPacket>) : bool 
		requires CHostIsValid(s)
		requires CHostIsValid(s')
		requires CPacketIsValid(pkt)
		requires (forall i :: i in out ==> CPacketIsValid(i))
		requires pkt.msg.CSingleMessage?
		ensures var lr := NextShard_Wrapper(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifySet(out, AbstractifyCPacketToPacket)); var cr := CNextShard_Wrapper(s, s', pkt, out); (cr) == (lr)
	{
		pkt.msg.m.CShard? 
		&& 
		if (pkt.msg.m.recipient == s.me) || ((!CValidKeyRange(pkt.msg.m.kr)) || ((CEmptyKeyRange(pkt.msg.m.kr)) || ((pkt.msg.m.recipient !in s.constants.hostIds) || ((!CDelegateForKeyRangeIsHost(s.delegationMap, pkt.msg.m.kr, s.me)) || (|CExtractRange(s.h, pkt.msg.m.kr)| >= Cmax_hashtable_size()))))) then 
			s' == s.(receivedPacket := None) 
			&& 
			out == {} 
		else 
			(exists sm, b :: CNextShard(s, s', out, pkt.msg.m.kr, pkt.msg.m.recipient, sm, b))
	}

	function method CNextShardReal(s: CHost, pkt: CPacket) : (CHost, set<CPacket>, CSingleMessage, bool) 
		requires CHostIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CSingleMessage?
		requires pkt.msg.m.CShard?
		requires CDelegateForKeyRangeIsHost(s.delegationMap, pkt.msg.m.kr, s.me)
		requires pkt.msg.m.recipient != s.me
		requires pkt.msg.m.recipient in s.constants.hostIds
		ensures CNextShardReal(s, s', pkt, out, sm, shouldSend) && !(pkt.msg.m.recipient == s.me) || ((!CValidKeyRange(pkt.msg.m.kr)) || ((CEmptyKeyRange(pkt.msg.m.kr)) || ((pkt.msg.m.recipient !in s.constants.hostIds) || ((!CDelegateForKeyRangeIsHost(s.delegationMap, pkt.msg.m.kr, s.me)) || (|CExtractRange(s.h, pkt.msg.m.kr)| >= Cmax_hashtable_size()))))) ==> CNextShard(s, s', out, pkt.msg.m.kr, pkt.msg.m.recipient, sm, shouldSend) ==> CNextShard_Wrapper(s, s', pkt, out)
		ensures CNextShardReal(s, s', pkt, out, sm, shouldSend) ==> CNextShard_Wrapper(s, s', pkt, out)
		ensures var (s', out, sm, shouldSend) := CNextShardReal(s, pkt); CHostIsValid(s') && (forall i :: i in out ==> CPacketIsValid(i)) && CSingleMessageIsValid(sm) && NextShardReal(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifySet(out, AbstractifyCPacketToPacket), AbstractifyCSingleMessageToSingleMessage(sm), shouldSend)
	{
		var t1 := 
			var kr := 
				pkt.msg.m.kr; 			
			var t1 := 
				var recipient := 
					pkt.msg.m.recipient; 				
				var t1 := 
					if (pkt.msg.m.recipient == s.me) || ((!CValidKeyRange(pkt.msg.m.kr)) || ((CEmptyKeyRange(pkt.msg.m.kr)) || ((pkt.msg.m.recipient !in s.constants.hostIds) || ((!CDelegateForKeyRangeIsHost(s.delegationMap, pkt.msg.m.kr, s.me)) || (|CExtractRange(s.h, pkt.msg.m.kr)| >= Cmax_hashtable_size()))))) then 
						var t1 := 
							CCInvalidMessage(); 						
						var t2 := 
							true; 						
						var t3 := 
							s.(receivedPacket := None); 						
						var t4 := 
							{}; 						
						(t3, t4, t1, t2) 
					else 
						var t1 := 
							CSendSingleMessageReal(s.sd, CDelegate(kr, CExtractRange(s.h, kr)), recipient, s.constants.params); 						
						var t2 := 
							if holder then 
								var t1 := 
									{CPacket(recipient, s.me, t1.1)}; 								
								var t2 := 
									s.(h := CBulkRemoveHashtable(s.h, kr), delegationMap := CUpdateDelegationMap(s.delegationMap, kr, recipient), sd := t1.0, numDelegations := s.numDelegations + 1, receivedPacket := None); 								
								(t2, t1) 
							else 
								var t1 := 
									{}; 								
								var t2 := 
									s.(numDelegations := s.numDelegations + 1, receivedPacket := None); 								
								(t2, t1); 						
						(t2.1, t2.0, t1.1, t1.2); 				
				(t1.3, t1.2, t1.1, t1.0); 			
			(t1.3, t1.2, t1.1, t1.0); 		
		(t1.3, t1.2, t1.1, t1.0)
	}

	function method Cmax_hashtable_size() : int 
		ensures var lr := max_hashtable_size(); var cr := Cmax_hashtable_size(); (cr) == (lr)
	{
		62
	}

	function method CNextReply(s: CHost, s': CHost, pkt: CPacket, out: set<CPacket>) : bool 
		requires CHostIsValid(s)
		requires CHostIsValid(s')
		requires CPacketIsValid(pkt)
		requires (forall i :: i in out ==> CPacketIsValid(i))
		requires pkt.msg.CSingleMessage?
		ensures var lr := NextReply(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifySet(out, AbstractifyCPacketToPacket)); var cr := CNextReply(s, s', pkt, out); (cr) == (lr)
	{
		pkt.msg.m.CReply? 
		&& 
		out == {} 
		&& 
		s' == s.(receivedPacket := None)
	}

	function method CNextReplyReal(s: CHost, pkt: CPacket) : (CHost, set<CPacket>) 
		requires CHostIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CSingleMessage?
		requires pkt.msg.m.CReply?
		ensures CNextReplyReal(s, s', pkt, out) ==> CNextReply(s, s', pkt, out)
		ensures var (s', out) := CNextReplyReal(s, pkt); CHostIsValid(s') && (forall i :: i in out ==> CPacketIsValid(i)) && NextReplyReal(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifySet(out, AbstractifyCPacketToPacket))
	{
		var t1 := 
			{}; 		
		var t2 := 
			s.(receivedPacket := None); 		
		(t2, t1)
	}

	function method CNextRedirectReal(s: CHost, pkt: CPacket) : (CHost, set<CPacket>) 
		requires CHostIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CSingleMessage?
		requires pkt.msg.m.CRedirect?
		ensures CNextRedirectReal(s, s', pkt, out) ==> CNextRedirect(s, s', pkt, out)
		ensures var (s', out) := CNextRedirectReal(s, pkt); CHostIsValid(s') && (forall i :: i in out ==> CPacketIsValid(i)) && NextRedirectReal(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifySet(out, AbstractifyCPacketToPacket))
	{
		var t1 := 
			{}; 		
		var t2 := 
			s.(receivedPacket := None); 		
		(t2, t1)
	}

	function method CShouldProcessReceivedMessage(s: CHost) : bool 
		requires CHostIsValid(s)
		ensures var lr := ShouldProcessReceivedMessage(AbstractifyCHostToHost(s)); var cr := CShouldProcessReceivedMessage(s); (cr) == (lr)
	{
		s.receivedPacket.CSome? 
		&& 
		s.receivedPacket.v.msg.CSingleMessage? 
		&& (
		(s.receivedPacket.v.msg.m.CDelegate?) || (s.receivedPacket.v.msg.m.CShard?) ==> s.numDelegations < s.constants.params.max_delegations - 2)
	}
}
