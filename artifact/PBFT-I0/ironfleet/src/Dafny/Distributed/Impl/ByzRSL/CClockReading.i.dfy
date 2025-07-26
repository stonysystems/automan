include "../../Common/Native/NativeTypes.s.dfy"
include "../../Protocol/ByzRSL/ClockReading.i.dfy"

module LiveByzRSL__CClockReading_i {
  import opened Native__NativeTypes_s
  import opened LiveByzRSL__ClockReading_i

  datatype CClockReading = CClockReading(t:int)

  function AbstractifyCClockReadingToClockReading(cclock:CClockReading) : ClockReading
  {
    ClockReading(cclock.t as int)
  }

}
