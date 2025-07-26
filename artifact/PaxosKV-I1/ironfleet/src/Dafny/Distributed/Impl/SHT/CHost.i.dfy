include "CSingleDelivery.i.dfy"
include "CDelegations.i.dfy"
include "Parameters.i.dfy"
include "PacketParsing.i.dfy"
include "CConfiguration.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Services/SHT/AbstractService.s.dfy"
include "../../Protocol/SHT/Host.i.dfy"
include "../../Common/Logic/Option.i.dfy"

module SHT__CHost_i {
import opened SHT__CSingleDelivery_i
import opened SHT__SingleDelivery_i
import opened SHT__CDelegations_i
import opened Impl_Parameters_i 
import opened AbstractServiceSHT_s`All
import opened Concrete_NodeIdentity_i
import opened SHT__HT_s
import opened SHT__CMessage_i
import opened SHT__SingleMessage_i
import opened SHT__CNetwork_i
import opened AppInterface_i`Spec
import opened SHT__Keys_i
import opened Native__Io_s
import opened Common__NodeIdentity_i
import opened GenericRefinement_i
import opened SHT__Host_i
import opened Logic__Option_i
import opened SHT__CSingleMessage_i
import opened Collections__Maps2_s
import opened SHT__Delegations_i
import opened Collections__Sets_i
import opened SHT__PacketParsing_i
import opened SHT__CConfiguration_i

/************************** AutoMan Translation ************************/

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
		delegationMap: CDelegationMap, 
		h: Hashtable, 
		sd: CSingleDeliveryAcct, 
		receivedPacket: Option<CPacket>, 
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
		&& /** Manually Added */
		(s.receivedPacket.Some? ==> CPacketIsValid(s.receivedPacket.v) 
                                   && s.receivedPacket.v.msg.CSingleMessage? 
                                   && !s.receivedPacket.v.msg.CInvalidMessage? 
                                   && CSingleMessageIs64Bit(s.receivedPacket.v.msg) 
                                   && s.receivedPacket.v.dst == s.me)
		// && 
		// (forall i :: i in s.receivedRequests ==> AppRequestIsValid(i))
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
        && /** Manually Added */
        OptionCPacketIsAbstractable(s.receivedPacket)
		// && 
		// (forall i :: i in s.receivedRequests ==> AppRequestIsAbstractable(i))
	}

	function AbstractifyCHostToHost(s: CHost) : Host 
		requires CHostIsAbstractable(s)
        /** Manually Added */
        ensures var s' := AbstractifyCHostToHost(s);
            DelegationMapComplete(s'.delegationMap)
	{
        var s' :=
		Host(
            AbstractifyCConstantsToConstants(s.constants), 
            AbstractifyEndPointToNodeIdentity(s.me), 
            AbstractifyCDelegationMapToDelegationMap(s.delegationMap), 
            s.h, /** Manually Modified */
            AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(s.sd), 
            AbstractifyOptional(s.receivedPacket, AbstractifyCPacketToShtPacket), /** Manually Added */
            s.numDelegations, 
            s.receivedRequests); /** Manually Modified */
        lemma_DelegationMap_Complete(s'); /** Manually Modified */
        s'
	}

    function method CValidKeyPlus(key: KeyPlus) : bool 
		requires KeyPlusIsValid(key)
		ensures var lr := ValidKeyPlus(key); var cr := CValidKeyPlus(key); (cr) == (lr)
	{
		(key.KeyZero?) || ((key.KeyInf?) || (ValidKey(key.k)))
	}

    function method CValidOptionalValue(opt: OptionalValue) : bool 
		// requires COptionalValueIsValid(opt)
		// ensures var lr := ValidOptionalValue(AbstractifyCOptionalValueToOptionalValue(opt)); var cr := CValidOptionalValue(opt); (cr) == (lr)
	{
		(opt.ValueAbsent?) || (ValidValue(opt.v))
	}

    function method CValidKeyRange(kr: KeyRange) : bool 
		requires KeyRangeIsValid(kr)
		ensures var lr := ValidKeyRange(kr); var cr := CValidKeyRange(kr); (cr) == (lr)
	{
		CValidKeyPlus(kr.klo) 
		&& 
		CValidKeyPlus(kr.khi)
	}

    function method CHost_Init(id: EndPoint, rootIdentity: EndPoint, hostIds: seq<EndPoint>, params: CParameters) : CHost 
		requires EndPointIsValid(id)
		requires EndPointIsValid(rootIdentity)
		requires (forall i :: i in hostIds ==> EndPointIsValid(i))
		requires CParametersIsValid(params)
		ensures var s := CHost_Init(id, rootIdentity, hostIds, params); 
        CHostIsValid(s) && 
        Host_Init(AbstractifyCHostToHost(s), AbstractifyEndPointToNodeIdentity(id), AbstractifyEndPointToNodeIdentity(rootIdentity), AbstractifySeq(hostIds, AbstractifyEndPointToNodeIdentity), AbstractifyCParametersToParameters(params))
	{
		var t1 := 
			CHost(
                CConstants(rootIdentity, hostIds, params), 
                id, 
                // CDelegationMap_Init(rootIdentity), 
                map i | 0 <= i < 10001 :: id, /** Manually Added */
                map[], 
                CSingleDelivery_Init(), 
                None, 
                1, 
                []); 	
        lemma_CHost_Init(rootIdentity, hostIds, params, id, t1);	/** Manually Added */
		t1
	}

    function method CNextGetRequestReal(s: CHost, pkt: CPacket) : (CHost, CSingleMessage, CMessage, seq<CPacket>, bool) 
		requires CHostIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CSingleMessage?
		requires pkt.msg.m.CGetRequest?
		requires pkt.msg.m.k_getrequest in s.delegationMap
        ensures var (s',sm,msg,out,shouldSend) := CNextGetRequestReal(s,pkt);
               CHostIsValid(s')
            && CSingleMessageIsValid(sm)
            && CMessageIsValid(msg)
            && SeqIsValid(out, CPacketIsValid)
            && NextGetRequestReal(
                AbstractifyCHostToHost(s),
                AbstractifyCHostToHost(s'),
                AbstractifyCPacketToShtPacket(pkt),
                AbstractifyCSingleMessageToSingleMessage(sm),
                AbstractifyCMessageToMessage(msg),
                SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
                shouldSend
            )
            && NextGetRequest(
                AbstractifyCHostToHost(s),
                AbstractifyCHostToHost(s'),
                AbstractifyCPacketToShtPacket(pkt),
                SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
            )
		// ensures CNextGetRequestReal(s, s', pkt, sm, m, out, shouldSend) ==> CNextGetRequest_Reply(s, s', pkt.src, pkt.msg.seqno, pkt.msg.m.k_getrequest, sm, m, out, shouldSend) ==> (exists sm1, m1, b :: CNextGetRequest_Reply(s, s', pkt.src, pkt.msg.seqno, pkt.msg.m.k_getrequest, sm1, m1, out, b))
		// ensures CNextGetRequestReal(s, s', pkt, sm, m, out, shouldSend) ==> CNextGetRequest(s, s', pkt, out)
		// ensures var (s', sm, m, out, shouldSend) := CNextGetRequestReal(s, pkt); CHostIsValid(s') && CSingleMessageIsValid(sm) && CMessageIsValid(m) && (forall i :: i in out ==> CPacketIsValid(i)) && NextGetRequestReal(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifyCSingleMessageToSingleMessage(sm), AbstractifyCMessageToMessage(m), AbstractifySet(out, AbstractifyCPacketToPacket), shouldSend)
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
									s.receivedRequests + [AppGetRequest(seqno, k)] 
								else 
									s.receivedRequests; 							
							var t1 := 
								var msg := 
									if owner == s.me then 
										CReply(k, HashtableLookup(s.h, k)) 
									else 
										CRedirect(k, owner); 								
								var t1 := 
									CSendSingleMessageReal(s.sd, msg, src, s.constants.params); 								
								var t2 := 
									if ValidKey(k) && t1.2 /** Manually Added */ then 
										var t1_1 := 
											msg; 										
										var t2 := 
											s.(sd := t1.0, receivedRequests := newReceivedRequests, receivedPacket := None); 										
										var t3 := 
											[CPacket(src, s.me, t1.1)]; 										
										(t2, t1_1, t3) 
									else 
										var t1 := 
											s.(receivedPacket := None); 										
										var t2 := 
											msg; 										
										var t3 := 
											[]; 										
										(t1, t2, t3); 								
								(t2.0, t1.1, t2.1, t2.2, t1.2); 							
							(t1.4, t1.3, t1.2, t1.1, t1.0); 						
						(t1.4, t1.3, t1.2, t1.1, t1.0); 					
					(t1.4, t1.3, t1.2, t1.1, t1.0); 				
				(t1.4, t1.3, t1.2, t1.1, t1.0); 			
			(t1.4, t1.3, t1.2, t1.1, t1.0); 		
		(t1.4, t1.3, t1.2, t1.1, t1.0)
	}

    function method CNextSetRequestReal(s: CHost, pkt: CPacket) : (CHost, CSingleMessage, CMessage, seq<CPacket>, bool) 
		requires CHostIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CSingleMessage?
		requires pkt.msg.m.CSetRequest?
		requires pkt.msg.m.k_setrequest in s.delegationMap
        ensures var (s',sm,msg,out,shouldSend) := CNextSetRequestReal(s,pkt);
               CHostIsValid(s')
            && CSingleMessageIsValid(sm)
            && CMessageIsValid(msg)
            && SeqIsValid(out, CPacketIsValid)
            && NextSetRequestReal(
                AbstractifyCHostToHost(s),
                AbstractifyCHostToHost(s'),
                AbstractifyCPacketToShtPacket(pkt),
                AbstractifyCSingleMessageToSingleMessage(sm),
                AbstractifyCMessageToMessage(msg),
                SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
                shouldSend
            )
            && NextSetRequest(
                AbstractifyCHostToHost(s),
                AbstractifyCHostToHost(s'),
                AbstractifyCPacketToShtPacket(pkt),
                SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
            )
		// ensures CNextSetRequestReal(s, s', pkt, sm, replym, out, shouldSend) ==> CNextSetRequest_Complete(s, s', pkt.src, pkt.msg.seqno, pkt.msg.m, sm, replym, out, shouldSend) ==> (exists sm1, m1, b1 :: CNextSetRequest_Complete(s, s', pkt.src, pkt.msg.seqno, pkt.msg.m, sm1, m1, out, b1))
		// ensures CNextSetRequestReal(s, s', pkt, sm, replym, out, shouldSend) ==> CNextSetRequest(s, s', pkt, out)
		// ensures var (s', sm, replym, out, shouldSend) := CNextSetRequestReal(s, pkt); CHostIsValid(s') && CSingleMessageIsValid(sm) && CMessageIsValid(replym) && (forall i :: i in out ==> CPacketIsValid(i)) && NextSetRequestReal(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifyCSingleMessageToSingleMessage(sm), AbstractifyCMessageToMessage(replym), AbstractifySet(out, AbstractifyCPacketToPacket), shouldSend)
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
										if ov.ValueAbsent? then 
											mapremove(s.h, k) 
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
												s.receivedRequests + [AppSetRequest(seqno, k, ov)] 
											else 
												s.receivedRequests; 										
										var t1 := 
											CSendSingleMessageReal(s.sd, msg, src, s.constants.params); 										
										var t2 := 
											if t1.2 /** Manually Added */ && ValidKey(k) && CValidOptionalValue(ov) then 
												var t1_1 := 
													msg; 												
												var t2 := 
													s.(h := newhtable, sd := t1.0, receivedRequests := reqs, receivedPacket := None); 												
												var t3 := 
													[CPacket(src, s.me, t1.1)]; 												
												(t2, t1_1, t3) 
											else 
												var t1 := 
													msg; 												
												var t2 := 
													s.(receivedPacket := None); 												
												var t3 := 
													[]; 												
												(t2, t1, t3); 										
										// (t2.2, t1.1, t2.1, t2.0, t1.0);
                                        (t2.0, t1.1, t2.1, t2.2, t1.2);  									
									(t1.4, t1.3, t1.2, t1.1, t1.0); 								
								(t1.4, t1.3, t1.2, t1.1, t1.0); 							
							(t1.4, t1.3, t1.2, t1.1, t1.0); 						
						(t1.4, t1.3, t1.2, t1.1, t1.0); 					
					(t1.4, t1.3, t1.2, t1.1, t1.0); 				
				(t1.4, t1.3, t1.2, t1.1, t1.0); 			
			(t1.4, t1.3, t1.2, t1.1, t1.0); 		
		(t1.4, t1.3, t1.2, t1.1, t1.0)
	}

    function method CNextDelegateReal(s: CHost, pkt: CPacket) : (CHost, seq<CPacket>) 
		requires CHostIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CSingleMessage?
		requires pkt.msg.m.CDelegate?
        ensures var (s', out) := CNextDelegateReal(s,pkt);
               CHostIsValid(s')
            && SeqIsValid(out, CPacketIsValid)
            && NextDelegateReal(
                AbstractifyCHostToHost(s),
                AbstractifyCHostToHost(s'),
                AbstractifyCPacketToShtPacket(pkt),
                SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
            )
            && NextDelegate(
                AbstractifyCHostToHost(s),
                AbstractifyCHostToHost(s'),
                AbstractifyCPacketToShtPacket(pkt),
                SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
            )
		// ensures CNextDelegateReal(s, s', pkt, out) ==> CNextDelegate(s, s', pkt, out)
		// ensures var (s', out) := CNextDelegateReal(s, pkt); CHostIsValid(s') && (forall i :: i in out ==> CPacketIsValid(i)) && NextDelegateReal(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifySet(out, AbstractifyCPacketToPacket))
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
			[]; 		
		var t3 := 
			s.(delegationMap := t1.0, h := t1.1, numDelegations := t1.2, receivedPacket := None); 		
		(t3, t2)
	}

    function method CNextShardReal(s: CHost, pkt: CPacket) : (CHost, seq<CPacket>, CSingleMessage, bool) 
		requires CHostIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CSingleMessage?
		requires pkt.msg.m.CShard?
		requires CDelegateForKeyRangeIsHost(s.delegationMap, pkt.msg.m.kr, s.me)
		requires pkt.msg.m.recipient != s.me
		requires pkt.msg.m.recipient in s.constants.hostIds
        ensures var (s', out, sm, shouldSend) := CNextShardReal(s,pkt);
               CHostIsValid(s')
            && CSingleMessageIsValid(sm)
            && SeqIsValid(out, CPacketIsValid)
            && NextShardReal(
                AbstractifyCHostToHost(s),
                AbstractifyCHostToHost(s'),
                AbstractifyCPacketToShtPacket(pkt),
                SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
                AbstractifyCSingleMessageToSingleMessage(sm),
                shouldSend
            )
            && NextShard_Wrapper(
                AbstractifyCHostToHost(s),
                AbstractifyCHostToHost(s'),
                AbstractifyCPacketToShtPacket(pkt),
                SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
            )
		// ensures CNextShardReal(s, s', pkt, out, sm, shouldSend) && !(pkt.msg.m.recipient == s.me) || ((!CValidKeyRange(pkt.msg.m.kr)) || ((CEmptyKeyRange(pkt.msg.m.kr)) || ((pkt.msg.m.recipient !in s.constants.hostIds) || ((!CDelegateForKeyRangeIsHost(s.delegationMap, pkt.msg.m.kr, s.me)) || (|CExtractRange(s.h, pkt.msg.m.kr)| >= Cmax_hashtable_size()))))) ==> CNextShard(s, s', out, pkt.msg.m.kr, pkt.msg.m.recipient, sm, shouldSend) ==> CNextShard_Wrapper(s, s', pkt, out)
		// ensures CNextShardReal(s, s', pkt, out, sm, shouldSend) ==> CNextShard_Wrapper(s, s', pkt, out)
		// ensures var (s', out, sm, shouldSend) := CNextShardReal(s, pkt); CHostIsValid(s') && (forall i :: i in out ==> CPacketIsValid(i)) && CSingleMessageIsValid(sm) && NextShardReal(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifySet(out, AbstractifyCPacketToPacket), AbstractifyCSingleMessageToSingleMessage(sm), shouldSend)
	{
		var t1 := 
			var kr := 
				pkt.msg.m.kr; 			
			var t1 := 
				var recipient := 
					pkt.msg.m.recipient; 				
				var t1 := 
					if (pkt.msg.m.recipient == s.me) || ((!CValidKeyRange(pkt.msg.m.kr)) || ((EmptyKeyRange(pkt.msg.m.kr)) || ((pkt.msg.m.recipient !in s.constants.hostIds) || ((!CDelegateForKeyRangeIsHost(s.delegationMap, pkt.msg.m.kr, s.me)) || (|CExtractRange(s.h, pkt.msg.m.kr)| >= max_hashtable_size()))))) then 
						var t1 := 
							CInvalidMessage(); 						
						var t2 := 
							true; 						
						var t3 := 
							s.(receivedPacket := None); 						
						var t4 := 
							[]; 						
						(t3, t4, t1, t2) 
					else 
						var t1 := 
							CSendSingleMessageReal(s.sd, CDelegate(kr, CExtractRange(s.h, kr)), recipient, s.constants.params); 						
						var t2 := 
							if t1.2 /** Manually Modified */ then 
								var t1_1 := 
									[CPacket(recipient, s.me, t1.1)]; 								
								var t2 := 
									s.(h := CBulkRemoveHashtable(s.h, kr), delegationMap := CUpdateDelegationMap(s.delegationMap, kr, recipient), sd := t1.0, numDelegations := s.numDelegations + 1, receivedPacket := None); 								
								(t2, t1_1) 
							else 
								var t1 := 
								    []; 								
								var t2 := 
									s.(numDelegations := s.numDelegations + 1, receivedPacket := None); 								
								(t2, t1); 						
						(t2.0, t2.1, t1.1, t1.2); 				
				(t1.0, t1.1, t1.2, t1.3); 			
			(t1.3, t1.2, t1.1, t1.0); 		
		(t1.3, t1.2, t1.1, t1.0)
	}

    function method CNextReplyReal(s: CHost, pkt: CPacket) : (CHost, seq<CPacket>) 
		requires CHostIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CSingleMessage?
		requires pkt.msg.m.CReply?
        ensures var (s',out) := CNextReplyReal(s,pkt);
            CHostIsValid(s')
            && SeqIsValid(out, CPacketIsValid)
            && NextReplyReal(
                AbstractifyCHostToHost(s),
                AbstractifyCHostToHost(s'),
                AbstractifyCPacketToShtPacket(pkt),
                SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
            )
            && NextReply(
                AbstractifyCHostToHost(s),
                AbstractifyCHostToHost(s'),
                AbstractifyCPacketToShtPacket(pkt),
                SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
            )
		// ensures CNextReplyReal(s, s', pkt, out) ==> CNextReply(s, s', pkt, out)
		// ensures var (s', out) := CNextReplyReal(s, pkt); CHostIsValid(s') && (forall i :: i in out ==> CPacketIsValid(i)) && NextReplyReal(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifySet(out, AbstractifyCPacketToPacket))
	{
		var t1 := 
			[]; 		
		var t2 := 
			s.(receivedPacket := None); 		
		(t2, t1)
	}

    function method CNextRedirectReal(s: CHost, pkt: CPacket) : (CHost, seq<CPacket>) 
		requires CHostIsValid(s)
		requires CPacketIsValid(pkt)
		requires pkt.msg.CSingleMessage?
		requires pkt.msg.m.CRedirect?
        ensures var (s',out) := CNextRedirectReal(s,pkt);
            CHostIsValid(s')
            && SeqIsValid(out, CPacketIsValid)
            && NextRedirectReal(
                AbstractifyCHostToHost(s),
                AbstractifyCHostToHost(s'),
                AbstractifyCPacketToShtPacket(pkt),
                SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
            )
            && NextRedirect(
                AbstractifyCHostToHost(s),
                AbstractifyCHostToHost(s'),
                AbstractifyCPacketToShtPacket(pkt),
                SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
            )
		// ensures CNextRedirectReal(s, s', pkt, out) ==> CNextRedirect(s, s', pkt, out)
		// ensures var (s', out) := CNextRedirectReal(s, pkt); CHostIsValid(s') && (forall i :: i in out ==> CPacketIsValid(i)) && NextRedirectReal(AbstractifyCHostToHost(s), AbstractifyCHostToHost(s'), AbstractifyCPacketToPacket(pkt), AbstractifySet(out, AbstractifyCPacketToPacket))
	{
		var t1 := 
			[]; 		
		var t2 := 
			s.(receivedPacket := None); 		
		(t2, t1)
	}

    function method CShouldProcessReceivedMessage(s: CHost) : bool 
		requires CHostIsValid(s)
		ensures var lr := ShouldProcessReceivedMessage(AbstractifyCHostToHost(s)); var cr := CShouldProcessReceivedMessage(s); (cr) == (lr)
	{
		s.receivedPacket.Some? 
		&& 
		s.receivedPacket.v.msg.CSingleMessage? 
		&& (
		(s.receivedPacket.v.msg.m.CDelegate?) || (s.receivedPacket.v.msg.m.CShard?) ==> s.numDelegations < s.constants.params.max_delegations - 2)
	}

/************************** AutoMan Translation End ************************/
// datatype CConstants = CConstants(
//     rootIdentity:EndPoint,
//     hostIds:seq<EndPoint>,
//     params:CParameters)

// predicate CConstantsIsAbstractable(constants:CConstants) {
//     EndPointIsAbstractable(constants.rootIdentity)
//     && SeqIsAbstractable(constants.hostIds, AbstractifyEndPointToNodeIdentity)
//     && CParametersIsAbstractable(constants.params)
// }

// predicate CConstantsIsValid(constants:CConstants) {
//     CConstantsIsAbstractable(constants)
//     && EndPointIsValid(constants.rootIdentity)
//     && SeqIsValid(constants.hostIds, EndPointIsValid)
//     && CParametersIsValid(constants.params)
//     // && SeqIsUnique(constants.hostIds)
// }

// function AbstractifyCConstantsToConstants(constants:CConstants) : Constants
//     requires CConstantsIsAbstractable(constants)
// {
//     Constants(
//         AbstractifyEndPointToNodeIdentity(constants.rootIdentity), 
//         AbstractifySeq(constants.hostIds, AbstractifyEndPointToNodeIdentity), 
//         AbstractifyCParametersToParameters(constants.params)
//     )
// }

// datatype CHost = CHost(
//     constants:CConstants,
//     me:EndPoint,
//     delegationMap:CDelegationMap,
//     h:Hashtable,
//     sd:CSingleDeliveryAcct,
//     receivedPacket:Option<CPacket>,
//     numDelegations:int,
//     ghost receivedRequests:seq<AppRequest>
//     )

// predicate CHostIsAbstractable(host:CHost)
// {
//     CConstantsIsAbstractable(host.constants)
//     && EndPointIsAbstractable(host.me)
//     && CDelegationMapIsAbstractable(host.delegationMap)
//     && HashtableIsAbstractable(host.h)
//     && CSingleDeliveryAcctIsAbstractable(host.sd)
//     && OptionCPacketIsAbstractable(host.receivedPacket)
// }

// predicate CHostIsValid(host:CHost)
// {
//     CHostIsAbstractable(host)
//     && CConstantsIsValid(host.constants)
//     && EndPointIsValid(host.me)
//     && CDelegationMapIsValid(host.delegationMap)
//     && HashtableIsValid(host.h)
//     && CSingleDeliveryAcctIsValid(host.sd)
//     // && OptionCPacketIsAbstractable(host.receivedPacket)

//     // && CSingleDeliveryAccountIsValid(host.sd, host.constants.params)
//     && (host.receivedPacket.Some? ==> CPacketIsValid(host.receivedPacket.v) 
//                                    && host.receivedPacket.v.msg.CSingleMessage? 
//                                    && !host.receivedPacket.v.msg.CInvalidMessage? 
//                                    && CSingleMessageIs64Bit(host.receivedPacket.v.msg) 
//                                    && host.receivedPacket.v.dst == host.me)
//     // && host.numDelegations < host.constants.params.max_delegations
//     // && |host.delegationMap.lows| <= 2 * host.numDelegations as int
// }

// function AbstractifyCHostToHost(host:CHost) : Host
//     requires CHostIsAbstractable(host)
//     ensures var s := AbstractifyCHostToHost(host);
//             DelegationMapComplete(s.delegationMap)
// {
//     // lemma_DelegationMap_Complete(host);
//     var s := Host(
//         AbstractifyCConstantsToConstants(host.constants),
//         AbstractifyEndPointToNodeIdentity(host.me), 
//         AbstractifyCDelegationMapToDelegationMap(host.delegationMap),
//         host.h,
//         AbstractifyCSingleDeliveryAcctToSingleDeliveryAcct(host.sd),
//         AbstractifyOptional(host.receivedPacket, AbstractifyCPacketToShtPacket),
//         host.numDelegations as int,
//         host.receivedRequests
//     );
//     lemma_DelegationMap_Complete(s);
//     s
// }

 lemma {:axiom} lemma_DelegationMap_Complete(s:Host)
    ensures DelegationMapComplete(s.delegationMap)

// predicate method CValidKeyPlus(key:KeyPlus)
// {
//     key.KeyZero? || key.KeyInf? || ValidKey(key.k)
// }

// predicate method CValidOptionalValue(opt:OptionalValue)
// {
//     opt.ValueAbsent? || ValidValue(opt.v)
// }

// predicate method CValidKeyRange(kr:KeyRange)
// {
//     CValidKeyPlus(kr.klo) && CValidKeyPlus(kr.khi)
// }

// function method CHost_Init(id:EndPoint, rootIdentity:EndPoint, hostIds:seq<EndPoint>, params:CParameters) : CHost 
//     requires EndPointIsValid(id)
//     requires EndPointIsValid(rootIdentity)
//     requires SeqIsValid(hostIds, EndPointIsValid)
//     requires CParametersIsValid(params)
//     ensures var s := CHost_Init(id,rootIdentity,hostIds,params);
//             CHostIsValid(s)
// {
//     CHost(
//         CConstants(rootIdentity, hostIds, params),
//         id,
//         // DelegationMap_Init(rootIdentity),
//         // map[0 := rootIdentity],
//         map i | 0 <= i < 10001 :: rootIdentity,
//         map [],
//         CSingleDelivery_Init(),
//         None,
//         1,
//         [])
// }

// function method CHost_Init(constants:CConstants, id:EndPoint) : CHost 
//     requires EndPointIsValid(id)
//     requires CConstantsIsValid(constants)
//     // requires EndPointIsValid(rootIdentity)
//     // requires SeqIsValid(hostIds, EndPointIsValid)
//     // requires CParametersIsValid(params)
//     ensures var s := CHost_Init(constants, id);
//             CHostIsValid(s)
//             && Host_Init(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyEndPointToNodeIdentity(id),
//                 AbstractifyEndPointToNodeIdentity(constants.rootIdentity),
//                 AbstractifySeq(constants.hostIds, AbstractifyEndPointToNodeIdentity),
//                 AbstractifyCParametersToParameters(constants.params)
//             )
// {
//     var host := CHost(
//         // CConstants(rootIdentity, hostIds, params),
//         constants,
//         id,
//         // DelegationMap_Init(rootIdentity),
//         // map[0 := rootIdentity],
//         map i | 0 <= i < 10001 :: id,
//         map [],
//         CSingleDelivery_Init(),
//         None,
//         1,
//         []);
//     lemma_CHost_Init(constants, id, host);
//     host
// }

// lemma {:axiom} lemma_CHost_Init(constants:CConstants, id:EndPoint, host:CHost)
//     requires EndPointIsValid(id)
//     requires CConstantsIsValid(constants)
//     ensures CHostIsValid(host)
//     ensures Host_Init(
//                 AbstractifyCHostToHost(host),
//                 AbstractifyEndPointToNodeIdentity(id),
//                 AbstractifyEndPointToNodeIdentity(constants.rootIdentity),
//                 AbstractifySeq(constants.hostIds, AbstractifyEndPointToNodeIdentity),
//                 AbstractifyCParametersToParameters(constants.params)
//             )

lemma {:axiom} lemma_CHost_Init(rootIdentity: EndPoint, hostIds: seq<EndPoint>, params: CParameters, id:EndPoint, host:CHost)
    requires EndPointIsValid(id)
    requires EndPointIsValid(rootIdentity)
	requires (forall i :: i in hostIds ==> EndPointIsValid(i))
	requires CParametersIsValid(params)
    ensures CHostIsValid(host)
    ensures Host_Init(
                AbstractifyCHostToHost(host),
                AbstractifyEndPointToNodeIdentity(id),
                AbstractifyEndPointToNodeIdentity(rootIdentity),
                AbstractifySeq(hostIds, AbstractifyEndPointToNodeIdentity),
                AbstractifyCParametersToParameters(params)
            )


// // function method CNextGetRequestReal(s:CHost, pkt:CPacket) :
// //             (CHost, CSingleMessage, CMessage, seq<CPacket>, bool)
// //     requires pkt.msg.CSingleMessage?;
// //     requires pkt.msg.m.CGetRequest?
// //     requires pkt.msg.m.k_getrequest in s.delegationMap
// //     requires CHostIsValid(s)
// //     requires CPacketIsValid(pkt)
// //     ensures var (s',sm,msg,out,shouldSend) := CNextGetRequestReal(s,pkt);
// //                CHostIsValid(s')
// //             && CSingleMessageIsValid(sm)
// //             && CMessageIsValid(msg)
// //             && SeqIsValid(out, CPacketIsValid)
// //             && NextGetRequestReal(
// //                 AbstractifyCHostToHost(s),
// //                 AbstractifyCHostToHost(s'),
// //                 AbstractifyCPacketToShtPacket(pkt),
// //                 AbstractifyCSingleMessageToSingleMessage(sm),
// //                 AbstractifyCMessageToMessage(msg),
// //                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
// //                 shouldSend
// //             )
// //             && NextGetRequest(
// //                 AbstractifyCHostToHost(s),
// //                 AbstractifyCHostToHost(s'),
// //                 AbstractifyCPacketToShtPacket(pkt),
// //                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
// //             )
// //             // && NextGetRequest_Reply(
// //             //     AbstractifyCHostToHost(s),
// //             //     AbstractifyCHostToHost(s'),
// //             //     AbstractifyEndPointToNodeIdentity(pkt.src),
// //             //     pkt.msg.seqno,
// //             //     pkt.msg.m.k_getrequest,
// //             //     AbstractifyCSingleMessageToSingleMessage(sm),
// //             //     AbstractifyCMessageToMessage(msg),
// //             //     SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
// //             //     shouldSend
// //             // ) ==> 
// //             // NextGetRequest(
// //             //     AbstractifyCHostToHost(s),
// //             //     AbstractifyCHostToHost(s'),
// //             //     AbstractifyCPacketToShtPacket(pkt),
// //             //     SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
// //             // )
// // {
// //     var k := pkt.msg.m.k_getrequest;
// //     var src := pkt.src;
// //     var seqno := pkt.msg.seqno;
// //     var owner := CDelegateForKey(s.delegationMap, k);
// //     ghost var newReceivedRequests := if owner == s.me then s.receivedRequests + [AppGetRequest(seqno, k)] else s.receivedRequests;
// //     var msg := if owner == s.me then CReply(k, HashtableLookup(s.h, k)) else CRedirect(k, owner);

// //     var (new_sd, sm, shouldSend) := CSendSingleMessageReal(s.sd, msg, src, s.constants.params);
// //     if ValidKey(k) && shouldSend then
// //         (s.(sd := new_sd, 
// //         receivedRequests := newReceivedRequests, 
// //         receivedPacket := None),
// //         sm,
// //         msg,
// //         [CPacket(src, s.me, sm)],
// //         shouldSend)
// //     else
// //         (s.(receivedPacket := None), sm, msg, [], shouldSend)
// // }

// function method CNextGetRequestReal(s:CHost, pkt:CPacket) :
//             (CHost, CSingleMessage, CMessage, seq<CPacket>, bool)
//     requires pkt.msg.CSingleMessage?;
//     requires pkt.msg.m.CGetRequest?
//     requires pkt.msg.m.k_getrequest in s.delegationMap
//     requires CHostIsValid(s)
//     requires CPacketIsValid(pkt)
//     ensures var (s',sm,msg,out,shouldSend) := CNextGetRequestReal(s,pkt);
//                CHostIsValid(s')
//             && CSingleMessageIsValid(sm)
//             && CMessageIsValid(msg)
//             && SeqIsValid(out, CPacketIsValid)
//             && NextGetRequestReal(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyCHostToHost(s'),
//                 AbstractifyCPacketToShtPacket(pkt),
//                 AbstractifyCSingleMessageToSingleMessage(sm),
//                 AbstractifyCMessageToMessage(msg),
//                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
//                 shouldSend
//             )
//             && NextGetRequest(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyCHostToHost(s'),
//                 AbstractifyCPacketToShtPacket(pkt),
//                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
//             )
//             // && NextGetRequest_Reply(
//             //     AbstractifyCHostToHost(s),
//             //     AbstractifyCHostToHost(s'),
//             //     AbstractifyEndPointToNodeIdentity(pkt.src),
//             //     pkt.msg.seqno,
//             //     pkt.msg.m.k_getrequest,
//             //     AbstractifyCSingleMessageToSingleMessage(sm),
//             //     AbstractifyCMessageToMessage(msg),
//             //     SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
//             //     shouldSend
//             // ) ==> 
//             // NextGetRequest(
//             //     AbstractifyCHostToHost(s),
//             //     AbstractifyCHostToHost(s'),
//             //     AbstractifyCPacketToShtPacket(pkt),
//             //     SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
//             // )
// {
//     var k := pkt.msg.m.k_getrequest;
//     var src := pkt.src;
//     var seqno := pkt.msg.seqno;
//     var owner := CDelegateForKey(s.delegationMap, k);
//     ghost var newReceivedRequests := if owner == s.me then s.receivedRequests + [AppGetRequest(seqno, k)] else s.receivedRequests;
//     var msg := if owner == s.me then CReply(k, HashtableLookup(s.h, k)) else CRedirect(k, owner);

//     var oldAckState := CAckStateLookup(src, s.sd.sendState); 
//     var new_seqno := oldAckState.numPacketsAcked + |oldAckState.unAcked| + 1;
//     var temp_sm := CSingleMessage(new_seqno, src, msg);

//     var (new_sd, new_sm, should_send) := if new_seqno > s.constants.params.max_seqno then
//         (s.sd, CSingleMessage(0, src, msg), false)
//     else 
//         (s.sd.(sendState := s.sd.sendState[temp_sm.dst := oldAckState.(unAcked := oldAckState.unAcked + [temp_sm])]),
//         temp_sm,
//         true);

//     ghost var (new_sd', sm', shouldSend') := CSendSingleMessageReal(s.sd, msg, src, s.constants.params);
//     assert new_sd == new_sd';
//     assert new_sm == sm';
//     assert should_send == shouldSend';

//     if ValidKey(k) && should_send then
//         (s.(sd := new_sd, 
//         receivedRequests := newReceivedRequests, 
//         receivedPacket := None),
//         new_sm,
//         msg,
//         [CPacket(src, s.me, new_sm)],
//         should_send)
//     else
//         (s.(receivedPacket := None), new_sm, msg, [], should_send)
// }

// function method CNextSetRequest_Complete_Real(s:CHost, src:EndPoint, seqno:int, reqm:CMessage) :
//             (CHost, CSingleMessage, CMessage, seq<CPacket>, bool)
//     // requires DelegationMapComplete(s.delegationMap);
//     requires reqm.CSetRequest?;
//     requires reqm.k_setrequest in s.delegationMap
//     requires CHostIsValid(s)
//     requires EndPointIsValid(src)
//     requires CMessageIsValid(reqm)
//     ensures var (s',sm,msg,out,shouldSend) := CNextSetRequest_Complete_Real(s,src,seqno,reqm);
//                CHostIsValid(s')
//             && CSingleMessageIsValid(sm)
//             && CMessageIsValid(msg)
//             && SeqIsValid(out, CPacketIsValid)
//             && NextSetRequest_Complete_Real(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyCHostToHost(s'),
//                 AbstractifyEndPointToNodeIdentity(src),
//                 seqno,
//                 AbstractifyCMessageToMessage(reqm),
//                 AbstractifyCSingleMessageToSingleMessage(sm),
//                 AbstractifyCMessageToMessage(msg),
//                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
//                 shouldSend
//             )
//             && NextSetRequest_Complete(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyCHostToHost(s'),
//                 AbstractifyEndPointToNodeIdentity(src),
//                 seqno,
//                 AbstractifyCMessageToMessage(reqm),
//                 AbstractifyCSingleMessageToSingleMessage(sm),
//                 AbstractifyCMessageToMessage(msg),
//                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
//                 shouldSend
//             )
// {
//     var k := reqm.k_setrequest;
//     var ov := reqm.v_setrequest;
//     var owner := CDelegateForKey(s.delegationMap, k);
//     var newhtable := if owner == s.me then (if ov.ValueAbsent? then mapremove(s.h, k) else s.h[k:=ov.v]) else s.h;
//     var msg := if owner == s.me then CReply(k, ov) else CRedirect(k, owner);
//     var reqs := if owner == s.me then s.receivedRequests + [AppSetRequest(seqno, k, ov)] else s.receivedRequests;

//     var (new_sd, sm, shouldSend) := CSendSingleMessageReal(s.sd, msg, src, s.constants.params);
//     if shouldSend && ValidKey(k) && CValidOptionalValue(ov) then
//         (s.(h := newhtable, sd := new_sd, receivedRequests := reqs, receivedPacket := None),
//          sm,
//          msg,
//          [CPacket(src, s.me, sm)],
//          shouldSend)
//     else
//         (s.(receivedPacket := None), sm, msg, [], shouldSend)
// }


// // function method CNextSetRequestReal(s:CHost, pkt:CPacket) :
// //             (CHost, CSingleMessage, CMessage, seq<CPacket>, bool)
// //     // requires DelegationMapComplete(s.delegationMap);
// //     requires pkt.msg.CSingleMessage?;
// //     requires pkt.msg.m.CSetRequest?;
// //     requires pkt.msg.m.k_setrequest in s.delegationMap
// //     requires CHostIsValid(s)
// //     requires CPacketIsValid(pkt)
// //     ensures var (s',sm,msg,out,shouldSend) := CNextSetRequestReal(s,pkt);
// //                CHostIsValid(s')
// //             && CSingleMessageIsValid(sm)
// //             && CMessageIsValid(msg)
// //             && SeqIsValid(out, CPacketIsValid)
// //             && NextSetRequestReal(
// //                 AbstractifyCHostToHost(s),
// //                 AbstractifyCHostToHost(s'),
// //                 AbstractifyCPacketToShtPacket(pkt),
// //                 AbstractifyCSingleMessageToSingleMessage(sm),
// //                 AbstractifyCMessageToMessage(msg),
// //                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
// //                 shouldSend
// //             )
// //             && NextSetRequest(
// //                 AbstractifyCHostToHost(s),
// //                 AbstractifyCHostToHost(s'),
// //                 AbstractifyCPacketToShtPacket(pkt),
// //                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
// //             )
// //             // && NextSetRequest_Complete(
// //             //     AbstractifyCHostToHost(s),
// //             //     AbstractifyCHostToHost(s'),
// //             //     AbstractifyEndPointToNodeIdentity(src),
// //             //     seqno,
// //             //     AbstractifyCMessageToMessage(reqm),
// //             //     AbstractifyCSingleMessageToSingleMessage(sm),
// //             //     AbstractifyCMessageToMessage(msg),
// //             //     SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
// //             //     shouldSend
// //             // )
// // {
// //     var k := pkt.msg.m.k_setrequest;
// //     var ov := pkt.msg.m.v_setrequest;
// //     var seqno := pkt.msg.seqno;
// //     var src := pkt.src;
// //     var owner := CDelegateForKey(s.delegationMap, k);
// //     var newhtable := if owner == s.me then (if ov.ValueAbsent? then mapremove(s.h, k) else s.h[k:=ov.v]) else s.h;
// //     var msg := if owner == s.me then CReply(k, ov) else CRedirect(k, owner);
// //     var reqs := if owner == s.me then s.receivedRequests + [AppSetRequest(seqno, k, ov)] else s.receivedRequests;

// //     var (new_sd, sm, shouldSend) := CSendSingleMessageReal(s.sd, msg, src, s.constants.params);
// //     if shouldSend && ValidKey(k) && CValidOptionalValue(ov) then
// //         (s.(h := newhtable, sd := new_sd, receivedRequests := reqs, receivedPacket := None),
// //          sm,
// //          msg,
// //          [CPacket(src, s.me, sm)],
// //          shouldSend)
// //     else
// //         (s.(receivedPacket := None), sm, msg, [], shouldSend)
// // }

// function method CNextSetRequestReal(s:CHost, pkt:CPacket) :
//             (CHost, CSingleMessage, CMessage, seq<CPacket>, bool)
//     // requires DelegationMapComplete(s.delegationMap);
//     requires pkt.msg.CSingleMessage?;
//     requires pkt.msg.m.CSetRequest?;
//     requires pkt.msg.m.k_setrequest in s.delegationMap
//     requires CHostIsValid(s)
//     requires CPacketIsValid(pkt)
//     ensures var (s',sm,msg,out,shouldSend) := CNextSetRequestReal(s,pkt);
//                CHostIsValid(s')
//             && CSingleMessageIsValid(sm)
//             && CMessageIsValid(msg)
//             && SeqIsValid(out, CPacketIsValid)
//             && NextSetRequestReal(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyCHostToHost(s'),
//                 AbstractifyCPacketToShtPacket(pkt),
//                 AbstractifyCSingleMessageToSingleMessage(sm),
//                 AbstractifyCMessageToMessage(msg),
//                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
//                 shouldSend
//             )
//             && NextSetRequest(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyCHostToHost(s'),
//                 AbstractifyCPacketToShtPacket(pkt),
//                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
//             )
//             // && NextSetRequest_Complete(
//             //     AbstractifyCHostToHost(s),
//             //     AbstractifyCHostToHost(s'),
//             //     AbstractifyEndPointToNodeIdentity(src),
//             //     seqno,
//             //     AbstractifyCMessageToMessage(reqm),
//             //     AbstractifyCSingleMessageToSingleMessage(sm),
//             //     AbstractifyCMessageToMessage(msg),
//             //     SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
//             //     shouldSend
//             // )
// {
//     var k := pkt.msg.m.k_setrequest;
//     var ov := pkt.msg.m.v_setrequest;
//     var seqno := pkt.msg.seqno;
//     var src := pkt.src;
//     var owner := CDelegateForKey(s.delegationMap, k);
//     var newhtable := if owner == s.me then (if ov.ValueAbsent? then mapremove(s.h, k) else s.h[k:=ov.v]) else s.h;
//     var msg := if owner == s.me then CReply(k, ov) else CRedirect(k, owner);
//     var reqs := if owner == s.me then s.receivedRequests + [AppSetRequest(seqno, k, ov)] else s.receivedRequests;

//     var oldAckState := CAckStateLookup(src, s.sd.sendState); 
//     var new_seqno := oldAckState.numPacketsAcked + |oldAckState.unAcked| + 1;
//     var temp_sm := CSingleMessage(new_seqno, src, msg);

//     var (new_sd, new_sm, should_send) := if new_seqno > s.constants.params.max_seqno then
//         (s.sd, CSingleMessage(0, src, msg), false)
//     else 
//         (s.sd.(sendState := s.sd.sendState[temp_sm.dst := oldAckState.(unAcked := oldAckState.unAcked + [temp_sm])]),
//         temp_sm,
//         true);

//     ghost var (new_sd', sm', shouldSend') := CSendSingleMessageReal(s.sd, msg, src, s.constants.params);
//     assert new_sd == new_sd';
//     assert new_sm == sm';
//     assert should_send == shouldSend';

//     // var (new_sd, sm, shouldSend) := CSendSingleMessageReal(s.sd, msg, src, s.constants.params);
//     if should_send && ValidKey(k) && CValidOptionalValue(ov) then
//         (s.(h := newhtable, sd := new_sd, receivedRequests := reqs, receivedPacket := None),
//          new_sm,
//          msg,
//          [CPacket(src, s.me, new_sm)],
//          should_send)
//     else
//         (s.(receivedPacket := None), new_sm, msg, [], should_send)
// }

// function method CNextDelegateReal(s:CHost, pkt:CPacket) : (CHost, seq<CPacket>)
//     requires CHostIsValid(s)
//     requires CPacketIsValid(pkt)
//     requires pkt.msg.CSingleMessage?;
//     requires pkt.msg.m.CDelegate?
//     ensures var (s', out) := CNextDelegateReal(s,pkt);
//                CHostIsValid(s')
//             && SeqIsValid(out, CPacketIsValid)
//             && NextDelegateReal(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyCHostToHost(s'),
//                 AbstractifyCPacketToShtPacket(pkt),
//                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
//             )
//             && NextDelegate(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyCHostToHost(s'),
//                 AbstractifyCPacketToShtPacket(pkt),
//                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
//             )
// {
//     if pkt.src in s.constants.hostIds then
//         (s.(delegationMap := CUpdateDelegationMap(s.delegationMap, pkt.msg.m.range, s.me),
//             h := BulkUpdateHashtable(s.h, pkt.msg.m.range, pkt.msg.m.h),
//             numDelegations := s.numDelegations + 1,
//             receivedPacket := None),
//          []) 
//     else 
//         (s.(receivedPacket := None), [])
// }

// // function method CNextShardReal(s:CHost, kr:KeyRange, recipient:EndPoint) :
// //                 (CHost, CSingleMessage, seq<CPacket>, bool)
// //     requires CHostIsValid(s)
// //     requires KeyRangeIsValid(kr)
// //     requires EndPointIsValid(recipient)
// //     requires CDelegateForKeyRangeIsHost(s.delegationMap, kr, s.me)
// //     requires recipient != s.me
// //     requires recipient in s.constants.hostIds
// //     ensures var (s', sm, out, shouldSend) := CNextShardReal(s,kr,recipient);
// //                CHostIsValid(s')
// //             && CSingleMessageIsValid(sm)
// //             && SeqIsValid(out, CPacketIsValid)
// //             && NextShardReal(
// //                 AbstractifyCHostToHost(s),
// //                 AbstractifyCHostToHost(s'),
// //                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
// //                 kr,
// //                 AbstractifyEndPointToNodeIdentity(recipient),
// //                 AbstractifyCSingleMessageToSingleMessage(sm),
// //                 shouldSend
// //             )
// //             && NextShard(
// //                 AbstractifyCHostToHost(s),
// //                 AbstractifyCHostToHost(s'),
// //                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
// //                 kr,
// //                 AbstractifyEndPointToNodeIdentity(recipient),
// //                 AbstractifyCSingleMessageToSingleMessage(sm),
// //                 shouldSend
// //             )
// // {
// //     var (new_sd, sm, shouldSend) := CSendSingleMessageReal(s.sd, CDelegate(kr, ExtractRange(s.h, kr)), recipient, s.constants.params);
// //     if shouldSend then
// //         (s.(h := BulkRemoveHashtable(s.h, kr), 
// //             delegationMap := CUpdateDelegationMap(s.delegationMap, kr, recipient), 
// //             sd := new_sd, 
// //             numDelegations := s.numDelegations + 1,
// //             receivedPacket := None),
// //          sm,
// //          [CPacket(recipient, s.me, sm) ],
// //          shouldSend)
// //     else
// //         (s.(numDelegations := s.numDelegations + 1, receivedPacket := None), sm, [], shouldSend)
// // }


// // function method CNextShardReal(s:CHost, pkt:CPacket) :
// //                 (CHost, CSingleMessage, seq<CPacket>, bool)
// //     requires pkt.msg.CSingleMessage?
// //     requires pkt.msg.m.CShard?
// //     requires CHostIsValid(s)
// //     requires CPacketIsValid(pkt)
// //     requires CDelegateForKeyRangeIsHost(s.delegationMap, pkt.msg.m.kr, s.me)
// //     requires pkt.msg.m.recipient != s.me
// //     requires pkt.msg.m.recipient in s.constants.hostIds
// //     ensures var (s', sm, out, shouldSend) := CNextShardReal(s,pkt);
// //                CHostIsValid(s')
// //             && CSingleMessageIsValid(sm)
// //             && SeqIsValid(out, CPacketIsValid)
// //             && NextShardReal(
// //                 AbstractifyCHostToHost(s),
// //                 AbstractifyCHostToHost(s'),
// //                 AbstractifyCPacketToShtPacket(pkt),
// //                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
// //                 AbstractifyCSingleMessageToSingleMessage(sm),
// //                 shouldSend
// //             )
// //             && NextShard_Wrapper(
// //                 AbstractifyCHostToHost(s),
// //                 AbstractifyCHostToHost(s'),
// //                 AbstractifyCPacketToShtPacket(pkt),
// //                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
// //             )
// // {
// //     var kr := pkt.msg.m.kr;
// //     var recipient := pkt.msg.m.recipient;
// //     if (   pkt.msg.m.recipient == s.me
// //            || !CValidKeyRange(pkt.msg.m.kr)
// //            || EmptyKeyRange(pkt.msg.m.kr)
// //            || pkt.msg.m.recipient !in s.constants.hostIds 
// //            || !CDelegateForKeyRangeIsHost(s.delegationMap, pkt.msg.m.kr, s.me)
// //            || |ExtractRange(s.h, pkt.msg.m.kr)| >= max_hashtable_size()) then
// //         (s.(receivedPacket := None), CInvalidMessage(), [], true)
// //     else
// //         var (new_sd, sm, shouldSend) := CSendSingleMessageReal(s.sd, CDelegate(kr, ExtractRange(s.h, kr)), recipient, s.constants.params);
// //         if shouldSend then
// //             (s.(h := BulkRemoveHashtable(s.h, kr), 
// //                 delegationMap := CUpdateDelegationMap(s.delegationMap, kr, recipient), 
// //                 sd := new_sd, 
// //                 numDelegations := s.numDelegations + 1,
// //                 receivedPacket := None),
// //             sm,
// //             [CPacket(recipient, s.me, sm) ],
// //             shouldSend)
// //         else
// //             (s.(numDelegations := s.numDelegations + 1, receivedPacket := None), sm, [], shouldSend)
// // }

// function method CNextShardReal(s:CHost, pkt:CPacket) :
//                 (CHost, CSingleMessage, seq<CPacket>, bool)
//     requires pkt.msg.CSingleMessage?
//     requires pkt.msg.m.CShard?
//     requires CHostIsValid(s)
//     requires CPacketIsValid(pkt)
//     requires CDelegateForKeyRangeIsHost(s.delegationMap, pkt.msg.m.kr, s.me)
//     requires pkt.msg.m.recipient != s.me
//     requires pkt.msg.m.recipient in s.constants.hostIds
//     ensures var (s', sm, out, shouldSend) := CNextShardReal(s,pkt);
//                CHostIsValid(s')
//             && CSingleMessageIsValid(sm)
//             && SeqIsValid(out, CPacketIsValid)
//             && NextShardReal(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyCHostToHost(s'),
//                 AbstractifyCPacketToShtPacket(pkt),
//                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket)),
//                 AbstractifyCSingleMessageToSingleMessage(sm),
//                 shouldSend
//             )
//             && NextShard_Wrapper(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyCHostToHost(s'),
//                 AbstractifyCPacketToShtPacket(pkt),
//                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
//             )
// {
//     var kr := pkt.msg.m.kr;
//     var recipient := pkt.msg.m.recipient;
//     if (   pkt.msg.m.recipient == s.me
//            || !CValidKeyRange(pkt.msg.m.kr)
//            || EmptyKeyRange(pkt.msg.m.kr)
//            || pkt.msg.m.recipient !in s.constants.hostIds 
//            || !CDelegateForKeyRangeIsHost(s.delegationMap, pkt.msg.m.kr, s.me)
//            || |ExtractRange(s.h, pkt.msg.m.kr)| >= max_hashtable_size()) then
//         (s.(receivedPacket := None), CInvalidMessage(), [], true)
//     else
//         var src := recipient;
//         var msg := CDelegate(kr, ExtractRange(s.h, kr));
//         var oldAckState := CAckStateLookup(src, s.sd.sendState); 
//         var new_seqno := oldAckState.numPacketsAcked + |oldAckState.unAcked| + 1;
//         var temp_sm := CSingleMessage(new_seqno, src, msg);

//         var (new_sd, new_sm, should_send) := if new_seqno > s.constants.params.max_seqno then
//             (s.sd, CSingleMessage(0, src, msg), false)
//         else 
//             (s.sd.(sendState := s.sd.sendState[temp_sm.dst := oldAckState.(unAcked := oldAckState.unAcked + [temp_sm])]),
//             temp_sm,
//             true);

//         ghost var (new_sd', sm', shouldSend') := CSendSingleMessageReal(s.sd, msg, src, s.constants.params);
//         assert new_sd == new_sd';
//         assert new_sm == sm';
//         assert should_send == shouldSend';
//         // var (new_sd, sm, shouldSend) := CSendSingleMessageReal(s.sd, CDelegate(kr, ExtractRange(s.h, kr)), recipient, s.constants.params);
//         if should_send then
//             (s.(h := BulkRemoveHashtable(s.h, kr), 
//                 delegationMap := CUpdateDelegationMap(s.delegationMap, kr, recipient), 
//                 sd := new_sd, 
//                 numDelegations := s.numDelegations + 1,
//                 receivedPacket := None),
//             new_sm,
//             [CPacket(recipient, s.me, new_sm) ],
//             should_send)
//         else
//             (s.(numDelegations := s.numDelegations + 1, receivedPacket := None), new_sm, [], should_send)
// }

// function method CNextReplyReal(s:CHost, pkt:CPacket) : (CHost,seq<CPacket>)
//     requires CHostIsValid(s)
//     requires CPacketIsValid(pkt)
//     requires pkt.msg.CSingleMessage?;
//     requires pkt.msg.m.CReply?
//     ensures var (s',out) := CNextReplyReal(s,pkt);
//             CHostIsValid(s')
//             && SeqIsValid(out, CPacketIsValid)
//             && NextReplyReal(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyCHostToHost(s'),
//                 AbstractifyCPacketToShtPacket(pkt),
//                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
//             )
//             && NextReply(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyCHostToHost(s'),
//                 AbstractifyCPacketToShtPacket(pkt),
//                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
//             )
// {
//     (s.(receivedPacket := None), [])
// }

// function method CNextRedirectReal(s:CHost, pkt:CPacket) : (CHost,seq<CPacket>)
//     requires CHostIsValid(s)
//     requires CPacketIsValid(pkt)
//     requires pkt.msg.CSingleMessage?;
//     requires pkt.msg.m.CRedirect?
//     ensures var (s',out) := CNextRedirectReal(s,pkt);
//             CHostIsValid(s')
//             && SeqIsValid(out, CPacketIsValid)
//             && NextRedirectReal(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyCHostToHost(s'),
//                 AbstractifyCPacketToShtPacket(pkt),
//                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
//             )
//             && NextRedirect(
//                 AbstractifyCHostToHost(s),
//                 AbstractifyCHostToHost(s'),
//                 AbstractifyCPacketToShtPacket(pkt),
//                 SeqToSet(AbstractifySeq(out, AbstractifyCPacketToShtPacket))
//             )
// {
//     (s.(receivedPacket := None), [])
// }

// predicate method CShouldProcessReceivedMessage(s:CHost)
//     requires CHostIsValid(s)
//     ensures CShouldProcessReceivedMessage(s) == ShouldProcessReceivedMessage(AbstractifyCHostToHost(s))
// {
//     s.receivedPacket.Some?
//  && s.receivedPacket.v.msg.CSingleMessage?
//  && ((s.receivedPacket.v.msg.m.CDelegate? || s.receivedPacket.v.msg.m.CShard?) ==> s.numDelegations < s.constants.params.max_delegations - 2)
// }

method {:timeLimitMultiplier 2} HostModelNextReceiveMessage(host:CHost, cpacket:CPacket)  returns (host':CHost, sent_packets:seq<CPacket>)
    requires cpacket.msg.CSingleMessage?;
    requires CHostIsValid(host)
    // requires CSingleDeliveryAcctIsValid(host.sd, host.constants.params)
    requires CPacketIsValid(cpacket);
    // requires CSingleMessageIs64Bit(cpacket.msg);
    requires host.receivedPacket.Some? && host.receivedPacket.v == cpacket;
    requires cpacket.msg.m.CGetRequest? ==> cpacket.msg.m.k_getrequest in host.delegationMap
    requires cpacket.msg.m.CSetRequest? ==> cpacket.msg.m.k_setrequest in host.delegationMap
    requires cpacket.msg.m.CShard? ==> CDelegateForKeyRangeIsHost(host.delegationMap, cpacket.msg.m.kr, host.me) && cpacket.msg.m.recipient != host.me && cpacket.msg.m.recipient in host.constants.hostIds 
    // requires HostState_common_preconditions(host, cpacket);
    // requires cpacket.msg.m.CGetRequest? ==> NextGetRequestPreconditions(host, cpacket);
    // requires cpacket.msg.m.CSetRequest? ==> NextSetRequestPreconditions(host, cpacket) 
    // requires cpacket.msg.m.CDelegate? ==> NextDelegatePreconditions(host, cpacket) && (host.numDelegations < host.constants.params.max_delegations - 2);
    // requires cpacket.msg.m.CShard? ==> NextShardPreconditions(host, cpacket) && (host.numDelegations < host.constants.params.max_delegations - 2);

    ensures CHostIsValid(host');
    ensures SeqIsValid(sent_packets, CPacketIsValid)
    ensures host'.constants == host.constants
    ensures host'.me == host.me
    ensures SeqIsAbstractable(sent_packets, AbstractifyCPacketToShtPacket)
    ensures OutboundPacketsSeqIsValid(sent_packets)
    ensures OutboundPacketsSeqHasCorrectSrc(sent_packets, host.me)
    
    // ensures CPacketSeqIsAbstractable(sent_packets);
    // ensures HostState_common_postconditions(host, cpacket, host', sent_packets)
    ensures Process_Message(AbstractifyCHostToHost(host), AbstractifyCHostToHost(host'), SeqToSet(AbstractifySeq(sent_packets, AbstractifyCPacketToShtPacket)))
        //   || HostIgnoringUnParseable(AbstractifyHostStateToHost(host), AbstractifyHostStateToHost(host'), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets));
    // ensures AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets) == ExtractPacketsFromLSHTPackets(AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets));
    ensures CShouldProcessReceivedMessage(host) ==> host'.receivedPacket.None?
{
    if CShouldProcessReceivedMessage(host) {
    if (cpacket.msg.CInvalidMessage?) {
        host' := host;
        sent_packets := [];
        assert Process_Message(AbstractifyCHostToHost(host), AbstractifyCHostToHost(host'), SeqToSet(AbstractifySeq(sent_packets, AbstractifyCPacketToShtPacket)));
    } else if (cpacket.msg.m.CGetRequest?) {
        // var s',sm,msg,out,shouldSend := CNextGetRequestReal(host, cpacket);
         var (s',sm,msg,out,shouldSend) := CNextGetRequestReal(host, cpacket);
        // host', sent_packets := HostModelNextGetRequest(host, cpacket);
        host' := s';
        sent_packets := out;
        // assert NextGetRequest(AbstractifyHostStateToHost(host), AbstractifyHostStateToHost(host'), AbstractifyCPacketToShtPacket(cpacket), AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets));
    } else if (cpacket.msg.m.CSetRequest?) {
        var (s',sm,msg,out,shouldSend) := CNextSetRequestReal(host, cpacket);
        // host', sent_packets := HostModelNextSetRequest(host, cpacket);
        host' := s';
        sent_packets := out;
    } else if (cpacket.msg.m.CDelegate?) {
        var (s',out) := CNextDelegateReal(host,cpacket);
        // host', sent_packets := HostModelNextDelegate(host, cpacket);
        host' := s';
        sent_packets := out;
    } else if (cpacket.msg.m.CShard?) {
        var (s',out,sm,shouldSend) := CNextShardReal(host, cpacket);
		// var (s',sm,out,shouldSend) := CNextShardReal(host, cpacket);
        // host', sent_packets := HostModelNextShard(host, cpacket);
        host' := s';
        sent_packets := out;
    } else if (cpacket.msg.m.CReply?) {
        var (s',out) := CNextReplyReal(host,cpacket);
        host' := s';
        sent_packets := out;
        // host' := host.(receivedPacket := None);
        // sent_packets := [];
        // assert |sent_packets| == 0;
        // reveal_AbstractifySeqOfCPacketsToSetOfShtPackets();
        // assert |AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets)| == |sent_packets|;
        // assert AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets) == {};
    } else if (cpacket.msg.m.CRedirect?){
        var (s',out) := CNextRedirectReal(host,cpacket);
        host' := s';
        sent_packets := out;
    }
    else {
        assert false;
        assert Process_Message(AbstractifyCHostToHost(host), AbstractifyCHostToHost(host'), SeqToSet(AbstractifySeq(sent_packets, AbstractifyCPacketToShtPacket)));
    }
    } else {
        host' := host;
        sent_packets := [];
        assert Process_Message(AbstractifyCHostToHost(host), AbstractifyCHostToHost(host'), SeqToSet(AbstractifySeq(sent_packets, AbstractifyCPacketToShtPacket)));
    }
    assert Process_Message(AbstractifyCHostToHost(host), AbstractifyCHostToHost(host'), SeqToSet(AbstractifySeq(sent_packets, AbstractifyCPacketToShtPacket)));
    lemma_HostModelNextReceiveMessage(host,cpacket,host',sent_packets);
 }

lemma {:axiom} lemma_HostModelNextReceiveMessage(host:CHost, cpacket:CPacket, host':CHost, sent_packets:seq<CPacket>)
    requires cpacket.msg.CSingleMessage?;
    requires CHostIsValid(host)
    requires CPacketIsValid(cpacket);
    requires host.receivedPacket.Some? && host.receivedPacket.v == cpacket;
    requires cpacket.msg.m.CGetRequest? ==> cpacket.msg.m.k_getrequest in host.delegationMap
    requires cpacket.msg.m.CSetRequest? ==> cpacket.msg.m.k_setrequest in host.delegationMap
    requires cpacket.msg.m.CShard? ==> CDelegateForKeyRangeIsHost(host.delegationMap, cpacket.msg.m.kr, host.me) && cpacket.msg.m.recipient != host.me && cpacket.msg.m.recipient in host.constants.hostIds
    ensures SeqIsAbstractable(sent_packets, AbstractifyCPacketToShtPacket)
    ensures host'.constants == host.constants
    ensures host'.me == host.me
    ensures OutboundPacketsSeqIsValid(sent_packets)
    ensures OutboundPacketsSeqHasCorrectSrc(sent_packets, host.me)

method HostModelReceivePacket(host:CHost, cpacket:CPacket) returns (host':CHost, sent_packets:seq<CPacket>, ack:CPacket)
    requires CHostIsValid(host)
    // requires CSingleDeliveryAccountIsValid(host.sd, host.constants.params)
    requires CPacketIsValid(cpacket) && 
    // CSingleMessageIs64Bit(cpacket.msg) && 
    !cpacket.msg.CInvalidMessage?; // CSingleMessageMarshallable(pkt.msg); 
    requires !cpacket.msg.CInvalidMessage?;
    // requires HostState_common_preconditions(host, cpacket);
    requires cpacket.dst == host.me;
    ensures CHostIsValid(host');
    // ensures HostStateIsValid(host') && OutboundPacketsSeqIsValid(sent_packets)
    ensures CPacketIsValid(ack);
    ensures SeqIsValid(sent_packets, CPacketIsValid)
    ensures SeqIsAbstractable(sent_packets, AbstractifyCPacketToShtPacket)
    ensures ReceivePacket(AbstractifyCHostToHost(host), AbstractifyCHostToHost(host'), 
            AbstractifyCPacketToShtPacket(cpacket), SeqToSet(AbstractifySeq(sent_packets, AbstractifyCPacketToShtPacket)), AbstractifyCPacketToShtPacket(ack))
    ensures OutboundPacketsSeqIsValid(sent_packets)
    ensures OutboundPacketsSeqHasCorrectSrc(sent_packets, host.me)
    // ensures HostState_common_postconditions(host, cpacket, host', sent_packets);
    ensures |sent_packets| >= 1 ==> sent_packets == [ack];
    ensures |sent_packets| == 0 ==> ack == cpacket;
{
    // print("receive packet\n");
    sent_packets := [];
    
    // reveal_AbstractifySeqOfCPacketsToSetOfShtPackets();
    
    if (host.receivedPacket.None?) {
        var (sd', a, acks) := CReceiveSingleMessage(host.sd, cpacket);
        ack := a;
        assert CPacketIsValid(ack);
        
        if (|acks| > 0) {
            var b' := CNewSingleMessage(host.sd, cpacket);
            sent_packets := [ack];        
            
            if (b') {
                host' := host.(receivedPacket := Some(cpacket), sd := sd');
            } else {
                host' := host.(receivedPacket := None, sd := sd');
            }
            assert CPacketIsValid(ack);
        } else {
            host' := host.(sd := sd');
            ack := cpacket;
            sent_packets := [];
            assert CPacketIsValid(ack);
        }
        assert CPacketIsValid(ack);
    } else {
        host' := host;
        ack := cpacket;
        assert CPacketIsValid(ack);
    }
    assert CPacketIsValid(ack);
    lemma_HostModelReceivePacket(host,cpacket,host',sent_packets,ack);
}

lemma {:axiom} lemma_HostModelReceivePacket(host:CHost, cpacket:CPacket, host':CHost, sent_packets:seq<CPacket>, ack:CPacket)
    requires CHostIsValid(host)
    requires CPacketIsValid(cpacket) && 
    // CSingleMessageIs64Bit(cpacket.msg) && 
    !cpacket.msg.CInvalidMessage?; // CSingleMessageMarshallable(pkt.msg); 
    requires !cpacket.msg.CInvalidMessage?;
    requires cpacket.dst == host.me;
    ensures CHostIsValid(host');
    ensures OutboundPacketsSeqIsValid(sent_packets)
    ensures OutboundPacketsSeqHasCorrectSrc(sent_packets, host.me)


method {:timeLimitMultiplier 2} HostModelSpontaneouslyRetransmit(host:CHost) returns (host':CHost, sent_packets:seq<CPacket>)
    requires CHostIsValid(host)
    ensures CHostIsValid(host')
    ensures SeqIsValid(sent_packets, CPacketIsValid)
    ensures SeqIsAbstractable(sent_packets, AbstractifyCPacketToShtPacket)
    ensures host' == host
    // requires SpontaneouslyRetransmitPreconditions(host);
    // ensures SpontaneouslyRetransmitPostconditions(host, host', sent_packets);
    ensures OutboundPacketsSeqIsValid(sent_packets);
    ensures OutboundPacketsSeqHasCorrectSrc(sent_packets, host.me); 
    ensures UnAckedMessages(AbstractifyCHostToHost(host).sd, AbstractifyCHostToHost(host).me) == SeqToSet(AbstractifySeq(sent_packets, AbstractifyCPacketToShtPacket))
{ 
    host' := host;
    sent_packets := CUnAckedMessages(host.sd, host.me);

    lemma_HostModelSpontaneouslyRetransmit(host, host', sent_packets);

    // assert AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets) == UnAckedMessages(AbstractifyHostStateToHost(host).sd, AbstractifyHostStateToHost(host).me);
    
    // reveal_AbstractifySeqOfCPacketsToSetOfShtPackets();
    
    // assert forall p :: p in sent_packets ==> AbstractifyCPacketToShtPacket(p) in AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets);
    // assert forall p :: p in sent_packets ==> AbstractifyCPacketToShtPacket(p) in ExtractPacketsFromLSHTPackets(AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets));
    
    // ghost var sent_packets' := AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets);
    
    // lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
    // assert forall p :: p in sent_packets ==> CPacketIsAbstractable(p) && EndPointIsValidIPV4(p.dst) && EndPointIsValidIPV4(p.src);
    // assert forall p :: p in sent_packets ==> LPacket(AbstractifyEndPointToNodeIdentity(p.dst), AbstractifyEndPointToNodeIdentity(p.src), AbstractifyCSingleMessageToSingleMessage(p.msg)) in sent_packets';
    
    // assert forall p':: p' in sent_packets' ==> exists p :: p in sent_packets && LPacket(AbstractifyEndPointToNodeIdentity(p.dst), AbstractifyEndPointToNodeIdentity(p.src), AbstractifyCSingleMessageToSingleMessage(p.msg)) == p';
    // assert AbstractifySeqOfCPacketsToSetOfShtPackets(sent_packets) == ExtractPacketsFromLSHTPackets(sent_packets');
    // assert UnAckedMessages(AbstractifyHostStateToHost(host).sd, AbstractifyHostStateToHost(host).me) == ExtractPacketsFromLSHTPackets(AbstractifyOutboundPacketsToSeqOfLSHTPackets(sent_packets));
}

lemma {:axiom} lemma_HostModelSpontaneouslyRetransmit(host:CHost, host':CHost, sent_packets:seq<CPacket>)
    requires CHostIsValid(host)
    ensures CHostIsValid(host')
    ensures SeqIsValid(sent_packets, CPacketIsValid)
    ensures SeqIsAbstractable(sent_packets, AbstractifyCPacketToShtPacket)
    ensures host' == host
    // requires SpontaneouslyRetransmitPreconditions(host);
    // ensures SpontaneouslyRetransmitPostconditions(host, host', sent_packets);
    ensures OutboundPacketsSeqIsValid(sent_packets);
    ensures OutboundPacketsSeqHasCorrectSrc(sent_packets, host.me); 

}