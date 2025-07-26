include "../../Common/Native/NativeTypes.s.dfy"
include "../../Protocol/Common/UpperBound.s.dfy"

module Common__UpperBound_i {

import opened Native__NativeTypes_s
import opened Common__UpperBound_s

datatype CUpperBound = CUpperBoundFinite(n:int) | CUpperBoundInfinite()

  function method CLeqUpperBound(x:int, u:CUpperBound) : bool
  {
    match u
    case CUpperBoundFinite(n) => x <= n
    case CUpperBoundInfinite => true
  }

  function method CLtUpperBound(x:int, u:CUpperBound) : bool
  {
    match u
    case CUpperBoundFinite(n) => x < n
    case CUpperBoundInfinite => true
  }

  predicate CUpperBoundIsAbstractable(c : CUpperBound)
  {
    true
  }

  predicate CUpperBoundIsValid(c : CUpperBound)
  {
    true
  }

  function method UpperBoundedAdditionImpl(x:int, y:int, u:CUpperBound) : int
    // ensures u.CUpperBoundFinite? ==> UpperBoundedAdditionImpl(x, y, u) as int == UpperBoundedAddition(x as int, y as int, UpperBoundFinite(u.n as int))
    // ensures u.CUpperBoundInfinite? ==> UpperBoundedAdditionImpl(x, y, u) as int == UpperBoundedAddition(x as int, y as int, UpperBoundInfinite())
    ensures UpperBoundedAdditionImpl(x, y, u) as int == UpperBoundedAddition(x as int, y as int, AbstractifyCUpperBoundToUpperBound(u))
  {
    if CLtUpperBound(x + y, u) then x + y else u.n
  }

  function AbstractifyCUpperBoundToUpperBound(u:CUpperBound) : UpperBound
  {
    match u
    case CUpperBoundFinite(n) => UpperBoundFinite(n)
    case CUpperBoundInfinite => UpperBoundInfinite
  }

// datatype CUpperBound = CUpperBoundFinite(n:uint64) | CUpperBoundInfinite()

// // function method CLeqUpperBound(x:uint64, u:CUpperBound) : bool
// // {
// //   match u
// //     case CUpperBoundFinite(n) => x <= n
// //     case CUpperBoundInfinite => true
// // }

// // function method CLtUpperBound(x:uint64, u:CUpperBound) : bool
// // {
// //   match u
// //     case CUpperBoundFinite(n) => x < n
// //     case CUpperBoundInfinite => true
// // }

// function method CLeqUpperBound(x:uint64, u:uint64) : bool
// {
//   x <= u
// }

// function method CLtUpperBound(x:uint64, u:uint64) : bool
// {
//   x < u
// }

// function method UpperBoundedAdditionImpl(x:uint64, y:uint64, u:uint64) : uint64
// {
//   if y >= u then
//     u
//   else if x >= u - y then
//     u
//   else
//     x + y
// }

}
