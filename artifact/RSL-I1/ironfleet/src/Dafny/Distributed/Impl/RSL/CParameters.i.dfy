include "../../Common/Native/NativeTypes.s.dfy"
include "../../Protocol/RSL/Parameters.i.dfy"
include "../Common/UpperBound.i.dfy"

module LiveRSL__ParametersState_i {
  import opened Native__NativeTypes_s
  import opened LiveRSL__Parameters_i
  import opened Common__UpperBound_i
  import opened Common__UpperBound_s

/************************** AutoMan Translation ************************/
  datatype CParameters = 
	CParameters(
		max_log_length: int, 
		baseline_view_timeout_period: int, 
		heartbeat_period: int, 
		max_integer_val: CUpperBound, 
		max_batch_size: int, 
		max_batch_delay: int
	)

	predicate CParametersIsValid(s: CParameters) 
	{
		CParametersIsAbstractable(s) 
		&& 
		CUpperBoundIsValid(s.max_integer_val)
    /* Manually added */
    && s.max_log_length > 0
    && s.baseline_view_timeout_period > 0
    && s.heartbeat_period > 0
    && (s.max_integer_val.CUpperBoundFinite? ==> s.max_integer_val.n > s.max_log_length)
    && s.max_batch_size > 0
    && s.max_batch_delay >= 0
	}

	predicate CParametersIsAbstractable(s: CParameters) 
	{
		CUpperBoundIsAbstractable(s.max_integer_val)
	}

	function AbstractifyCParametersToLParameters(s: CParameters) : LParameters 
		requires CParametersIsAbstractable(s)
	{
		LParameters(s.max_log_length, s.baseline_view_timeout_period, s.heartbeat_period, AbstractifyCUpperBoundToUpperBound(s.max_integer_val), s.max_batch_size, s.max_batch_delay)
	}
/************************** AutoMan Translation End ************************/

  // datatype CParameters =
  //   CParameters
  //   (
  //     max_log_length : int ,
  //     baseline_view_timeout_period : int ,
  //     heartbeat_period : int ,
  //     max_integer_val : CUpperBound ,
  //     max_batch_size : int ,
  //     max_batch_delay : int
  //   )

  // predicate CParametersIsAbstractable(
  //   s : CParameters)

  // {

  //   &&
  //   CUpperBoundIsAbstractable(s.max_integer_val)
  // }

  // predicate CParametersIsValid(
  //   s : CParameters)

  // {
  //   &&
  //     CParametersIsAbstractable(s)
  //   &&
  //     CUpperBoundIsValid(s.max_integer_val)

  //   /* Manually added */
  //   && s.max_log_length > 0
  //   && s.baseline_view_timeout_period > 0
  //   && s.heartbeat_period > 0
  //   && (s.max_integer_val.CUpperBoundFinite? ==> s.max_integer_val.n > s.max_log_length)
  //   && s.max_batch_size > 0
  //   && s.max_batch_delay >= 0
  // }

  // function AbstractifyCParametersToLParameters(
  //   s : CParameters) : LParameters
  //   requires CParametersIsAbstractable(s)
  // {
  //   LParameters(s.max_log_length, s.baseline_view_timeout_period, s.heartbeat_period, AbstractifyCUpperBoundToUpperBound(s.max_integer_val), s.max_batch_size, s.max_batch_delay)
  // }

  /* Generated, not used
  function method CWFLParameters(
    p : CParameters) : bool
    requires CParametersIsValid(p)
    ensures var bc := CWFLParameters(p); var bl := WFLParameters(AbstractifyCParametersToLParameters(p));  && bl == bc
  {

    &&
      p.max_log_length > 0
    &&
      p.baseline_view_timeout_period > 0
    &&
      p.heartbeat_period > 0
    &&
      (p.max_integer_val.UpperBoundFinite? ==> p.max_integer_val.n > p.max_log_length)
    &&
      p.max_batch_size > 0
    &&
      p.max_batch_delay >= 0
  }
  */

  /* Manually added */
  function method StaticParams() : CParameters
  {
    CParameters(1000,   // max log length
                60,   // baseline view timeout period (1000 ms = 1 sec)
                10,     // heartbeat period (100 ms)
                        // 0x8000_0000_0000_0000 - 1,  // Max integer value:  2^63 - 1
                CUpperBoundInfinite,
                16, // max_batch_size
                10)     // max_batch_delay (10 ms)
  }
}
