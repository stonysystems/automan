include "Environment.i.dfy"
include "Configuration.i.dfy"
include "Constants.i.dfy"
include "Broadcast.i.dfy"
include "../../Common/Collections/CountMatches.i.dfy"

/*
Implemented requirements clause generation for:
  1. bop (with none metadata)
  2. if-else
  3. let-bind
See the examples below for details.

TODO:
  Determine how to detect forall and exists clauses that need to be moved.
*/

module LiveRSL__Acceptor_i {
  import opened LiveRSL__Environment_i
  import opened LiveRSL__Configuration_i
  import opened LiveRSL__Constants_i
  import opened LiveRSL__Broadcast_i
  import opened LiveRSL__Types_i
  import opened LiveRSL__Message_i
  import opened Collections__CountMatches_i
  import opened Environment_s
  import opened Common__UpperBound_s

  datatype LAcceptor = LAcceptor(
    constants:LReplicaConstants,
    max_bal:Ballot,
    votes:Votes,
    last_checkpointed_operation:seq<OperationNumber>,
    log_truncation_point:OperationNumber
  )

  predicate LAcceptorInit(a:LAcceptor, c:LReplicaConstants)
  {
    var x := 1; /* NEW */
    && |c.all.config.replica_ids| >= 0 /* NEW */
    && a.constants == c
    && a.max_bal == Ballot(0,0)
    && a.votes == map []
    && |c.all.config.replica_ids| == x /* NEW */
    // Try the following two
    // && |c.all.config.replica_ids| == a 
    // && |c.all.config.replica_ids| == a.votes 
    && |a.last_checkpointed_operation| == |c.all.config.replica_ids|
    && (forall idx :: 0 <= idx < |a.last_checkpointed_operation| ==> a.last_checkpointed_operation[idx] == 0)
    && a.log_truncation_point == 0
    && |c.all.config.replica_ids| == a.max_bal.seqno + x /* NEW */
  }
  
  predicate LAcceptorProcessHeartbeat(s:LAcceptor, s':LAcceptor, inp:RslPacket)
    requires inp.msg.RslMessage_Heartbeat?
  {
    if inp.src in s.constants.all.config.replica_ids then
      var sender_index := GetReplicaIndex(inp.src, s.constants.all.config);
      if 0 <= sender_index < |s.last_checkpointed_operation| && inp.msg.opn_ckpt > s.last_checkpointed_operation[sender_index] then
        s'.last_checkpointed_operation == s.last_checkpointed_operation[sender_index := inp.msg.opn_ckpt]
        && s'.constants == s.constants
        && s'.max_bal == s.max_bal
        && s'.votes == s.votes
        && s'.log_truncation_point == s.log_truncation_point
        && s.max_bal == 1 /* NEW */
        && s'.log_truncation_point + 10 == 12 /* NEW */
      else
        s' == s
        && s.max_bal == 2 /* NEW */
    else
      s' == s
  }

  // NEW
  // LAcceptorTruncateLogHelper(-, +, +, +);
  predicate LAcceptorTruncateLogHelper(s': LAcceptor, s: LAcceptor, opn: OperationNumber, new_votes: Votes)
  {
    s' == s.(log_truncation_point := opn, votes := new_votes)
  }

  // LAcceptorTruncateLog(+, -, +);
  predicate LAcceptorTruncateLog(s:LAcceptor, s':LAcceptor, opn:OperationNumber)
  {
    if opn <= s.log_truncation_point then
      s' == s
    else
      && RemoveVotesBeforeLogTruncationPoint(s.votes, s'.votes, opn)
      && LAcceptorTruncateLogHelper(s', s, opn, s'.votes) // NEW
  }
}
