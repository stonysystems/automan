/**********************************************************************
AUTOMAN LOG

[Module] LiveRSL__Acceptor_i

[Action] LAcceptorInit
Check passed

[Action] LAcceptorProcessHeartbeat
Check passed

[Action] LAcceptorTruncateLogHelper
Check passed

[Action] LAcceptorTruncateLog
Check passed
**********************************************************************/

include ""


module Impl_LiveRSL__Acceptor_i 
{

	datatype CAcceptor = 
	CAcceptor(
		constants: CReplicaConstants, 
		max_bal: CBallot, 
		votes: CVotes, 
		last_checkpointed_operation: seq<COperationNumber>, 
		log_truncation_point: COperationNumber
	)

	predicate CAcceptorIsValid(s: CAcceptor) 
	{
		CAcceptorIsAbstractable(s) 
		&& 
		CReplicaConstantsIsValid(s.constants) 
		&& 
		CBallotIsValid(s.max_bal) 
		&& 
		CVotesIsValid(s.votes) 
		&& 
		(forall i :: i in s.last_checkpointed_operation ==> COperationNumberIsValid(i)) 
		&& 
		COperationNumberIsValid(s.log_truncation_point)
	}

	predicate CAcceptorIsAbstractable(s: CAcceptor) 
	{
		CReplicaConstantsIsAbstractable(s.constants) 
		&& 
		CBallotIsAbstractable(s.max_bal) 
		&& 
		CVotesIsAbstractable(s.votes) 
		&& 
		(forall i :: i in s.last_checkpointed_operation ==> COperationNumberIsAbstractable(i)) 
		&& 
		COperationNumberIsAbstractable(s.log_truncation_point)
	}

	function AbstractifyCAcceptorToLAcceptor(s: CAcceptor) : LAcceptor 
		requires CAcceptorIsAbstractable(s)
	{
		LAcceptor(AbstractifyCReplicaConstantsToLReplicaConstants(s.constants), AbstractifyCBallotToBallot(s.max_bal), AbstractifyCVotesToVotes(s.votes), AbstractifySeq(s.last_checkpointed_operation, AbstractifyCOperationNumberToOperationNumber), AbstractifyCOperationNumberToOperationNumber(s.log_truncation_point))
	}

	function method CAcceptorInit(c: CReplicaConstants) : CAcceptor 
		requires CReplicaConstantsIsValid(c)
		requires var x := 1; |c.all.config.replica_ids| >= 0 && |c.all.config.replica_ids| == x
		ensures var a := CAcceptorInit(c); CAcceptorIsValid(a) && LAcceptorInit(AbstractifyCAcceptorToLAcceptor(a), AbstractifyCReplicaConstantsToLReplicaConstants(c))
	{
		var t1 := 
			var x := 
				1; 			
			var t1 := 
				c; 			
			var t2 := 
				CBallot(0, 0); 			
			var t3 := 
				map[]; 			
			var t4 := 
				seq(|c.all.config.replica_ids|, (idx) => 0); 			
			var t5 := 
				0; 			
			CAcceptor(t1, t2, t3, t4, t5); 		
		t1
	}

	function method CAcceptorProcessHeartbeat(s: CAcceptor, inp: CPacket) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires CPacketIsValid(inp)
		requires inp.msg.CMessage_Heartbeat?
		requires if inp.src in s.constants.all.config.replica_ids then var sender_index := CGetReplicaIndex(inp.src, s.constants.all.config); if 0 <= sender_index && sender_index < |s.last_checkpointed_operation| && inp.msg.opn_ckpt > s.last_checkpointed_operation[sender_index] then s.max_bal == 1 else s.max_bal == 2 else true
		ensures var s' := CAcceptorProcessHeartbeat(s, inp); CAcceptorIsValid(s') && LAcceptorProcessHeartbeat(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCPacketToRslPacket(inp))
	{
		var t1 := 
			if inp.src in s.constants.all.config.replica_ids then 
				var t1 := 
					var sender_index := 
						CGetReplicaIndex(inp.src, s.constants.all.config); 					
					var t1 := 
						if 0 <= sender_index && sender_index < |s.last_checkpointed_operation| && inp.msg.opn_ckpt > s.last_checkpointed_operation[sender_index] then 
							var t1 := 
								s.last_checkpointed_operation[sender_index := inp.msg.opn_ckpt]; 							
							var t2 := 
								s.constants; 							
							var t3 := 
								s.max_bal; 							
							var t4 := 
								s.votes; 							
							var t5 := 
								s.log_truncation_point; 							
							CAcceptor(t2, t3, t4, t1, t5) 
						else 
							var t1 := 
								s; 							
							t1; 					
					t1; 				
				t1 
			else 
				var t1 := 
					s; 				
				t1; 		
		t1
	}

	function method CAcceptorTruncateLogHelper(s: CAcceptor, opn: COperationNumber, new_votes: CVotes) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires COperationNumberIsValid(opn)
		requires CVotesIsValid(new_votes)
		ensures var s' := CAcceptorTruncateLogHelper(s, opn, new_votes); CAcceptorIsValid(s') && LAcceptorTruncateLogHelper(AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCAcceptorToLAcceptor(s), AbstractifyCOperationNumberToOperationNumber(opn), AbstractifyCVotesToVotes(new_votes))
	{
		var t1 := 
			s.(log_truncation_point := opn, votes := new_votes); 		
		t1
	}

	function method CAcceptorTruncateLog(s: CAcceptor, opn: COperationNumber) : CAcceptor 
		requires CAcceptorIsValid(s)
		requires COperationNumberIsValid(opn)
		ensures var s' := CAcceptorTruncateLog(s, opn); CAcceptorIsValid(s') && LAcceptorTruncateLog(AbstractifyCAcceptorToLAcceptor(s), AbstractifyCAcceptorToLAcceptor(s'), AbstractifyCOperationNumberToOperationNumber(opn))
	{
		var t1 := 
			if opn <= s.log_truncation_point then 
				var t1 := 
					s; 				
				t1 
			else 
				var t1 := 
					CRemoveVotesBeforeLogTruncationPoint(s.votes, opn); 				
				var t2 := 
					CAcceptorTruncateLogHelper(s, opn, t1); 				
				t2; 		
		t1
	}

	function method CGetReplicaIndex(id: EndPoint, c: CConfiguration) : int 
		requires EndPointIsValid(id)
		requires CConfigurationIsValid(c)
		requires id in c.replica_ids
		ensures var idx := CGetReplicaIndex(id, c); 0 <= idx && idx < |c.replica_ids| && c.replica_ids[idx] == id
		ensures var lr := GetReplicaIndex(AbstractifyEndPointToNodeIdentity(id), AbstractifyCConfigurationToLConfiguration(c)); var cr := CGetReplicaIndex(id, c); (cr) == (lr)
	{
		CFindIndexInSeq(c.replica_ids, id)
	}
}
