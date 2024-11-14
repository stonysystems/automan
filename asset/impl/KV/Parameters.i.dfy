/**********************************************************************
AUTOMAN LOG

[Module] Protocol_Parameters_i
**********************************************************************/

include ""


module Impl_Protocol_Parameters_i 
{

	datatype CParameters = 
	CParameters(
		max_seqno: nat, 
		max_delegations: nat
	)

	predicate CParametersIsValid(s: CParameters) 
	{
		CParametersIsAbstractable(s)
	}

	predicate CParametersIsAbstractable(s: CParameters) 
	{
		true
	}

	function AbstractifyCParametersToParameters(s: CParameters) : Parameters 
		requires CParametersIsAbstractable(s)
	{
		Parameters(s.max_seqno, s.max_delegations)
	}
}
