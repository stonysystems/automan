/**********************************************************************
AUTOMAN LOG

[Module] LiveByzRSL__DistributedSystem_i
**********************************************************************/

include ""


module Impl_LiveByzRSL__DistributedSystem_i 
{

	datatype CState = 
	CState(
		constants: CConstants, 
		environment: CEnvironment<EndPoint, CMessage>, 
		replicas: seq<CScheduler>, 
		clients: set<EndPoint>
	)

	predicate CStateIsValid(s: CState) 
	{
		CStateIsAbstractable(s) 
		&& 
		CConstantsIsValid(s.constants) 
		&& 
		(forall i :: i in s.replicas ==> CSchedulerIsValid(i)) 
		&& 
		(forall i :: i in s.clients ==> EndPointIsValid(i))
	}

	predicate CStateIsAbstractable(s: CState) 
	{
		CConstantsIsAbstractable(s.constants) 
		&& 
		(forall i :: i in s.replicas ==> CSchedulerIsAbstractable(i)) 
		&& 
		(forall i :: i in s.clients ==> EndPointIsAbstractable(i))
	}

	function AbstractifyCStateToRslState(s: CState) : RslState 
		requires CStateIsAbstractable(s)
	{
		RslState(AbstractifyCConstantsToLConstants(s.constants), , AbstractifySeq(s.replicas, AbstractifyCSchedulerToLScheduler), AbstractifySet(s.clients, AbstractifyEndPointToNodeIdentity))
	}

	function method CMapsComplete(ps: CState) : bool 
		requires CStateIsValid(ps)
		ensures var lr := RslMapsComplete(AbstractifyCStateToRslState(ps)); var cr := CMapsComplete(ps); (cr) == (lr)
	{
		|ps.replicas| == |ps.constants.config.replica_ids|
	}

	function method CConstantsUnchanged(ps: CState, ps': CState) : bool 
		requires CStateIsValid(ps)
		requires CStateIsValid(ps')
		ensures var lr := RslConstantsUnchanged(AbstractifyCStateToRslState(ps), AbstractifyCStateToRslState(ps')); var cr := CConstantsUnchanged(ps, ps'); (cr) == (lr)
	{
		|ps'.replicas| == |ps.replicas| 
		&& 
		ps'.clients == ps.clients 
		&& 
		ps'.constants == ps.constants
	}

	function method CInit(con: CConstants, ps: CState) : bool 
		requires CConstantsIsValid(con)
		requires CStateIsValid(ps)
		ensures var lr := RslInit(AbstractifyCConstantsToLConstants(con), AbstractifyCStateToRslState(ps)); var cr := CInit(con, ps); (cr) == (lr)
	{
		CWellFormedLConfiguration(con.config) 
		&& 
		CWFLParameters(con.params) 
		&& 
		ps.constants == con 
		&& 
		CEnvironment_Init(ps.environment) 
		&& 
		CMapsComplete(ps) 
		&& 
		(forall i :: 0 <= i && i < |con.config.replica_ids| ==> CSchedulerInit(ps.replicas[i], CReplicaConstants(i, con)))
	}

	function method CNextCommon(ps: CState, ps': CState) : bool 
		requires CStateIsValid(ps)
		requires CStateIsValid(ps')
		ensures var lr := RslNextCommon(AbstractifyCStateToRslState(ps), AbstractifyCStateToRslState(ps')); var cr := CNextCommon(ps, ps'); (cr) == (lr)
	{
		CMapsComplete(ps) 
		&& 
		CConstantsUnchanged(ps, ps') 
		&& 
		CEnvironment_Next(ps.environment, ps'.environment)
	}

	function method CNextOneReplica(ps: CState, ps': CState, idx: int, ios: seq<CIo>) : bool 
		requires CStateIsValid(ps)
		requires CStateIsValid(ps')
		requires (forall i :: i in ios ==> CIoIsValid(i))
		ensures var lr := RslNextOneReplica(AbstractifyCStateToRslState(ps), AbstractifyCStateToRslState(ps'), idx, AbstractifySeq(ios, AbstractifyCIoToRslIo)); var cr := CNextOneReplica(ps, ps', idx, ios); (cr) == (lr)
	{
		CNextCommon(ps, ps') 
		&& 
		0 <= idx && idx < |ps.constants.config.replica_ids| 
		&& 
		CSchedulerNext(ps.replicas[idx], ps'.replicas[idx], ios) 
		&& 
		ps.environment.nextStep == CEnvStepHostIos(ps.constants.config.replica_ids[idx], ios) 
		&& 
		ps'.replicas == ps.replicas[idx := ps'.replicas[idx]]
	}

	function method CNextEnvironment(ps: CState, ps': CState) : bool 
		requires CStateIsValid(ps)
		requires CStateIsValid(ps')
		ensures var lr := RslNextEnvironment(AbstractifyCStateToRslState(ps), AbstractifyCStateToRslState(ps')); var cr := CNextEnvironment(ps, ps'); (cr) == (lr)
	{
		CNextCommon(ps, ps') 
		&& 
		!(ps.environment.nextStep.CEnvStepHostIos?) 
		&& 
		ps'.replicas == ps.replicas
	}

	function method CNextOneExternal(ps: CState, ps': CState, eid: EndPoint, ios: seq<CIo>) : bool 
		requires CStateIsValid(ps)
		requires CStateIsValid(ps')
		requires EndPointIsValid(eid)
		requires (forall i :: i in ios ==> CIoIsValid(i))
		ensures var lr := RslNextOneExternal(AbstractifyCStateToRslState(ps), AbstractifyCStateToRslState(ps'), AbstractifyEndPointToNodeIdentity(eid), AbstractifySeq(ios, AbstractifyCIoToRslIo)); var cr := CNextOneExternal(ps, ps', eid, ios); (cr) == (lr)
	{
		CNextCommon(ps, ps') 
		&& 
		eid !in ps.constants.config.replica_ids 
		&& 
		ps.environment.nextStep == CEnvStepHostIos(eid, ios) 
		&& 
		ps'.replicas == ps.replicas
	}

	function method CNext(ps: CState, ps': CState) : bool 
		requires CStateIsValid(ps)
		requires CStateIsValid(ps')
		ensures var lr := RslNext(AbstractifyCStateToRslState(ps), AbstractifyCStateToRslState(ps')); var cr := CNext(ps, ps'); (cr) == (lr)
	{
		((exists idx, ios :: CNextOneReplica(ps, ps', idx, ios))) || (((exists eid, ios :: CNextOneExternal(ps, ps', eid, ios))) || (CNextEnvironment(ps, ps')))
	}
}
