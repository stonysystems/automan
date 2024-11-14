/**********************************************************************
AUTOMAN LOG

[Module] SHT__Configuration_i
**********************************************************************/

include ""


module Impl_SHT__Configuration_i 
{

	datatype CSHTConfiguration = 
	CSHTConfiguration(
		clientIds: seq<EndPoint>, 
		hostIds: seq<EndPoint>, 
		rootIdentity: EndPoint, 
		params: CParameters
	)

	predicate CSHTConfigurationIsValid(s: CSHTConfiguration) 
	{
		CSHTConfigurationIsAbstractable(s) 
		&& 
		(forall i :: i in s.clientIds ==> EndPointIsValid(i)) 
		&& 
		(forall i :: i in s.hostIds ==> EndPointIsValid(i)) 
		&& 
		EndPointIsValid(s.rootIdentity) 
		&& 
		CParametersIsValid(s.params)
	}

	predicate CSHTConfigurationIsAbstractable(s: CSHTConfiguration) 
	{
		(forall i :: i in s.clientIds ==> EndPointIsAbstractable(i)) 
		&& 
		(forall i :: i in s.hostIds ==> EndPointIsAbstractable(i)) 
		&& 
		EndPointIsAbstractable(s.rootIdentity) 
		&& 
		CParametersIsAbstractable(s.params)
	}

	function AbstractifyCSHTConfigurationToSHTConfiguration(s: CSHTConfiguration) : SHTConfiguration 
		requires CSHTConfigurationIsAbstractable(s)
	{
		SHTConfiguration(AbstractifySeq(s.clientIds, AbstractifyEndPointToNodeIdentity), AbstractifySeq(s.hostIds, AbstractifyEndPointToNodeIdentity), AbstractifyEndPointToNodeIdentity(s.rootIdentity), AbstractifyCParametersToParameters(s.params))
	}

	function method CHostsDistinct(hostIds: seq<EndPoint>, i: int, j: int) : bool 
		requires (forall i :: i in hostIds ==> EndPointIsValid(i))
		ensures var lr := HostsDistinct(AbstractifySeq(hostIds, AbstractifyEndPointToNodeIdentity), i, j); var cr := CHostsDistinct(hostIds, i, j); (cr) == (lr)
	{
		0 <= i && i < |hostIds| && 0 <= j && j < |hostIds| && hostIds[i] == hostIds[j] ==> i == j
	}

	function method CWFSHTConfiguration(c: CSHTConfiguration) : bool 
		requires CSHTConfigurationIsValid(c)
		ensures var lr := WFSHTConfiguration(AbstractifyCSHTConfigurationToSHTConfiguration(c)); var cr := CWFSHTConfiguration(c); (cr) == (lr)
	{
		0 < |c.hostIds| 
		&& 
		c.rootIdentity in c.hostIds 
		&& 
		(forall i, j :: CHostsDistinct(c.hostIds, i, j))
	}
}
