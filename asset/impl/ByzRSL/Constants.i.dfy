/**********************************************************************
AUTOMAN LOG

[Module] LiveByzRSL__Constants_i
**********************************************************************/

include ""


module Impl_LiveByzRSL__Constants_i 
{

	datatype CConstants = 
	CConstants(
		config: CConfiguration, 
		params: CParameters
	)

	predicate CConstantsIsValid(s: CConstants) 
	{
		CConstantsIsAbstractable(s) 
		&& 
		CConfigurationIsValid(s.config) 
		&& 
		CParametersIsValid(s.params)
	}

	predicate CConstantsIsAbstractable(s: CConstants) 
	{
		CConfigurationIsAbstractable(s.config) 
		&& 
		CParametersIsAbstractable(s.params)
	}

	function AbstractifyCConstantsToLConstants(s: CConstants) : LConstants 
		requires CConstantsIsAbstractable(s)
	{
		LConstants(AbstractifyCConfigurationToLConfiguration(s.config), AbstractifyCParametersToLParameters(s.params))
	}

	datatype CReplicaConstants = 
	CReplicaConstants(
		my_index: int, 
		all: CConstants
	)

	predicate CReplicaConstantsIsValid(s: CReplicaConstants) 
	{
		CReplicaConstantsIsAbstractable(s) 
		&& 
		CConstantsIsValid(s.all)
	}

	predicate CReplicaConstantsIsAbstractable(s: CReplicaConstants) 
	{
		CConstantsIsAbstractable(s.all)
	}

	function AbstractifyCReplicaConstantsToLReplicaConstants(s: CReplicaConstants) : LReplicaConstants 
		requires CReplicaConstantsIsAbstractable(s)
	{
		LReplicaConstants(s.my_index, AbstractifyCConstantsToLConstants(s.all))
	}

	function method CReplicaConstantsValid(c: CReplicaConstants) : bool 
		requires CReplicaConstantsIsValid(c)
		ensures var lr := LReplicaConstantsValid(AbstractifyCReplicaConstantsToLReplicaConstants(c)); var cr := CReplicaConstantsValid(c); (cr) == (lr)
	{
		0 <= c.my_index 
		&& 
		c.my_index < |c.all.config.replica_ids|
	}
}
