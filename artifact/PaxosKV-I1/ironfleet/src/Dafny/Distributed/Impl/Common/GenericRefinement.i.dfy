include "../../Common/Native/NativeTypes.s.dfy"
include "../../Common/Collections/Maps.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Common/Logic/Option.i.dfy"

module GenericRefinement_i {
import opened Native__NativeTypes_s
import opened Collections__Maps_i
import opened Collections__Sets_i
import opened Logic__Option_i

// Useful to give this cast a name, so it can be used as a higher-order function
function uint64_to_int(u:uint64) : int { u as int }
function int_to_int(u:int) : int { u as int }
  function nat_to_nat(n:nat) : nat { n }

  predicate intIsAbstractable(i:int) {true}
//////////////////////////////////////////////////////////////////////////////

 predicate OptionalIsAbstractable<CT(!new),T>(ov:Option<CT>, refine_func:CT~>T)
  reads refine_func.reads
{
  match ov 
    case Some(v) => refine_func.requires(v)
    case None => true
}

// predicate OptionalIsValid<CT(!new),T>(ov:Option<CT>, valid_func:CT~>T)
//   reads valid_func.reads
// {
//   match ov 
//     case Some(v) => valid_func(v)
//     case None => true
// }

function AbstractifyOptional<CT(!new),T>(ov:Option<CT>, refine_func:CT~>T) : Option<T> 
  reads refine_func.reads
  requires OptionalIsAbstractable(ov,refine_func)
{
    match ov {
        case Some(v) => Some(refine_func(v))
        case None => None()
    }
}

//  Generic seq-to-seq refinement
function {:opaque} MapSeqToSeq<T(!new),U>(s:seq<T>, refine_func:T~>U) : seq<U>
  reads refine_func.reads
  requires forall i :: refine_func.reads(i) == {}
  requires forall i :: 0 <= i < |s| ==> refine_func.requires(s[i])
  ensures |MapSeqToSeq(s, refine_func)| == |s|
  ensures forall i :: 0 <= i < |s| ==> refine_func(s[i]) == MapSeqToSeq(s,refine_func)[i]
{
  if |s| == 0 then []
  else [refine_func(s[0])] + MapSeqToSeq(s[1..], refine_func)
}

predicate IsInjective<CT(!new), T(!new)>(f:CT~>T)
    reads f.reads
  {
    forall i, j :: f.requires(i) && f.requires(j) && f(i) == f(j) ==> i == j
  }

  predicate SeqIsAbstractable<T(!new), CT(!new)>(s:seq<CT>, RefineValue:CT~>T)
    reads RefineValue.reads
  {
    (forall i :: i in s ==> RefineValue.requires(i))
  }

  function NoChange<T(!new)>(v : T) : T
  {
    v
  }

  predicate MapIsValid<CKT(!new),CVT(!new)>(m:map<CKT,CVT>, ValidateKey:CKT~>bool, ValidateValue:CVT~>bool)
    reads ValidateKey.reads, ValidateValue.reads
  {
    (forall k :: k in m ==>
                   ValidateKey.requires(k) && ValidateKey(k) &&
                   ValidateValue.requires(m[k]) && ValidateValue(m[k])
                 )
  }


  predicate SeqIsValid<CT(!new)>(s:seq<CT>, ValidateValue:CT~>bool)
    reads ValidateValue.reads
  {
    (forall i :: i in s ==> ValidateValue.requires(i) && ValidateValue(i) )
  }

  function AbstractifySeq<T(!new), CT(!new)>(s:seq<CT>, RefineValue:CT~>T) : seq<T>
    reads RefineValue.reads
    requires SeqIsAbstractable(s, RefineValue)
    // requires IsInjective(RefineValue)
    // requires forall x, y :: RefineValue.requires(x) && RefineValue.requires(y) && RefineValue(x) == RefineValue(y) ==> x == y
    // requires forall x, y :: x in s && y in s && RefineValue(x) == RefineValue(y) ==> x == y
    ensures var cs := AbstractifySeq(s, RefineValue);
            &&  |cs| == |s|
            &&  (forall i :: 0 <= i < |s| ==> cs[i] == RefineValue(s[i]))
                             // &&  (forall c :: RefineValue.requires(c) ==>
                             //           (c in s <==> RefineValue(c) in cs))
                             // && (forall i :: RefineValue.requires(i) ==> (i in s <==> RefineValue(i) in cs))
            && (forall i :: i in cs ==> exists x :: x in s && i == RefineValue(x))
  {
    // lemma_AbstractifySeq(RefineValue);
    var cs := if |s| == 0 then
                []
              else
                [RefineValue(s[0])] + AbstractifySeq(s[1..], RefineValue);
    assert forall i :: i in cs ==> exists x :: x in s && i == RefineValue(x);
    cs
  }


  // lemma lemma_AbstractifySeq<T(!new), CT(!new)>(f:CT~>T)
  //   ensures forall v1, v2 :: f.requires(v1) && f.requires(v2) && f(v1) == f(v2) ==> v1 == v2
  // {
  // //  assert forall u1:uint64, u2:uint64 :: u1 as int == u2 as int ==> u1 == u2;
  //   // lemma_AbstractifyEndPointToNodeIdentity_injective_forall();
  //   // lemma_CRequestEqual();
  // }

  lemma lemma_seq_concat<T(!new), CT(!new)>(s1:seq<CT>, s2:seq<CT>, RefineValue:CT~>T)
    requires SeqIsAbstractable(s1, RefineValue)
    requires SeqIsAbstractable(s2, RefineValue)
    // requires IsInjective(RefineValue)
    ensures AbstractifySeq(s1, RefineValue) + AbstractifySeq(s2, RefineValue) == AbstractifySeq(s1 + s2, RefineValue)
    ensures SeqIsAbstractable(s1 + s2, RefineValue)
  {
  }

  lemma lemma_seq_sub<T(!new), CT(!new)>(s:seq<CT>, RefineValue:CT~>T, l:int, r:int)
    requires SeqIsAbstractable(s, RefineValue)
    requires 0 <= l <= r <= |s|
    ensures AbstractifySeq(s[l..r], RefineValue) == AbstractifySeq(s, RefineValue)[l..r]
  {
    var s_sub := s[l..r];
    var s_abs := AbstractifySeq(s, RefineValue);
    var s_sub_abs := AbstractifySeq(s_sub, RefineValue);
    assert s_sub_abs == s_abs[l..r];
  }



  predicate SetIsInjective<T(!new), CT(!new)>(s:set<CT>, f:CT~>T)
    reads f.reads
    requires SetIsAbstractable(s, f)
  {
    forall i, j :: i in s && j in s && f.requires(i) && f.requires(j) && f(i) == f(j) ==> i == j
  }

  predicate SetIsAbstractable<T(!new), CT(!new)>(s:set<CT>, RefineValue:CT~>T)
    reads RefineValue.reads
  {
    forall k :: k in s ==> RefineValue.requires(k)
  }

  function AbstractifySet<T(!new), CT(!new)>(s:set<CT>, RefineValue:CT~>T) : set<T>
    reads RefineValue.reads
    requires SetIsAbstractable(s, RefineValue)
    // requires IsInjective(RefineValue)
    requires forall x, y :: x in s && y in s && RefineValue(x) == RefineValue(y) ==> x == y
    ensures var ss := AbstractifySet(s, RefineValue);
            && (forall k :: k in s ==> RefineValue(k) in ss)
                            // && (forall y :: y in ss <==> exists x :: x in s && y == RefineValue(x))
            && |ss| == |s|
  {
    var ss := set i | i in s :: RefineValue(i);
    lemma_AbstractifySet_SizeUnchange(s,ss,RefineValue);
    ss
  }

  lemma lemma_AbstractifySet_SizeUnchange<T(!new), CT(!new)>(s:set<CT>, ss:set<T>, f:CT~>T)
    requires forall x :: x in s ==> f.requires(x)
    requires forall x, y :: x in s && y in s && f(x) == f(y) ==> x == y
    requires forall x :: x in s ==> f(x) in ss
    requires forall y :: y in ss <==> exists x :: x in s && y == f(x)
    ensures  |s| == |ss|
  {
    if (s != {})
    {
      var x :| x in s;
      var s' := s - {x};
      var ss' := ss - {f(x)};
      lemma_AbstractifySet_SizeUnchange(s', ss', f);
    }
  }

/////////////////////////////////////////////////////////
//  Generic map refinement from concrete to abstract 
/////////////////////////////////////////////////////////
predicate MapIsAbstractable<KT(!new),VT,CKT(!new),CVT(!new)>(m:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT)
    reads RefineKey.reads, RefineValue.reads, ReverseKey.reads
  {
    && (forall ck :: ck in m ==> RefineKey.requires(ck) && RefineValue.requires(m[ck]))
    && (forall ck :: ck in m ==> ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck)
  }

  function {:opaque} AbstractifyMap<CKT(!new),CVT(!new),KT(!new),VT>(m:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT) : map<KT,VT>
    reads RefineKey.reads, RefineValue.reads, ReverseKey.reads
    requires forall ck :: ck in m ==> RefineKey.requires(ck) && RefineValue.requires(m[ck])
    requires forall ck :: ck in m ==> ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck
    ensures  var rm  := AbstractifyMap(m,RefineKey,RefineValue,ReverseKey);
             && (forall ck :: ck in m ==> RefineKey.requires(ck) && RefineKey(ck) in rm)
             && (forall ck :: ck in m ==> rm[RefineKey(ck)] == RefineValue(m[ck]))
    // && (forall ck :: ck !in m ==> RefineKey.requires(ck) ==> RefineKey(ck) !in rm)
             && (forall k :: k in rm ==> (exists ck :: ck in m && RefineKey(ck) == k))
    // ensures forall ck, cval {:trigger m[ck := cval]} {:trigger RefineKey(ck), RefineValue(cval)} ::
    //           (RefineKey.requires(ck) && RefineValue.requires(cval)
    //           && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck) ==>
    //           var rm  := AbstractifyMap(m, RefineKey, RefineValue, ReverseKey);
    //           var rm' := AbstractifyMap(m[ck := cval], RefineKey, RefineValue, ReverseKey);
    //           rm' == AbstractifyMap(m, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)]
    // ensures forall ck {:trigger RemoveElt(AbstractifyMap(m, RefineKey, RefineValue, ReverseKey), RefineKey(ck)) } ::
    //           (RefineKey.requires(ck) && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck && ck in m) ==>
    //           var rm  := AbstractifyMap(m, RefineKey, RefineValue, ReverseKey);
    //           var rm' := AbstractifyMap(RemoveElt(m, ck), RefineKey, RefineValue, ReverseKey);
    //           rm' == RemoveElt(rm, RefineKey(ck))
    // ensures var rm  := AbstractifyMap(m,RefineKey,RefineValue,ReverseKey);
    //           forall k :: k in m ==> (exists rk :: rk in rm && RefineKey(k) == rk)
  {
    // var new_domain := set ck | ck in m :: RefineKey(ck);
    // map k | k in new_domain :: RefineValue(m[ReverseKey(k)])
    // Lemma_AbstractifyMap_basic_properties(m, RefineKey, RefineValue, ReverseKey);
    // lemma_AbstractifyMap_properties(m, RefineKey, RefineValue, ReverseKey);
    map k {:trigger m[ReverseKey(k)]} | k in (set ck | ck in m :: RefineKey(ck)) :: RefineValue(m[ReverseKey(k)])
  }

  lemma Lemma_AbstractifyMap_basic_properties<CKT,CVT,KT,VT>(m:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT)
    requires MapIsAbstractable(m, RefineKey, RefineValue, ReverseKey)
    // Injectivity
    requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
    // requires IsInjective(RefineKey)
    ensures  m == map [] ==> AbstractifyMap(m, RefineKey, RefineValue, ReverseKey) == map []
    ensures forall ck :: ck in m ==> AbstractifyMap(m, RefineKey, RefineValue, ReverseKey)[RefineKey(ck)] == RefineValue(m[ck])
    ensures  forall ck :: ck in m <==> RefineKey.requires(ck) && RefineKey(ck) in AbstractifyMap(m, RefineKey, RefineValue, ReverseKey)
    ensures  forall ck :: ck in m ==> AbstractifyMap(m, RefineKey, RefineValue, ReverseKey)[RefineKey(ck)] == RefineValue(m[ck])
    // ensures forall ck, cv {:trigger AbstractifyMap(m[ck := cv], RefineKey, RefineValue, ReverseKey)} ::
    //           var rm := AbstractifyMap(m, RefineKey, RefineValue, ReverseKey);
    //           var rm' := AbstractifyMap(m[ck := cv], RefineKey, RefineValue, ReverseKey);
    //           rm' == rm[RefineKey(ck) := RefineValue(cv)]
  {
    assert forall i, j :: RefineKey.requires(i) && RefineKey.requires(j) && RefineKey(i) == RefineKey(j) ==> i == j;
    reveal AbstractifyMap();
  }

  lemma Lemma_AbstractifyMap_preimage<KT(!new),VT(!new),CKT(!new),CVT(!new)>(cm:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT)
    requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
    // Injectivity
    requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
    ensures  var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
             forall k :: k in rm ==> (exists ck :: ck in cm && RefineKey(ck) == k)
  {
    var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
    Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);
    forall k | k in rm
      ensures (exists ck :: ck in cm && RefineKey(ck) == k)
    {
      reveal AbstractifyMap();
    }
  }

  lemma Lemma_AbstractifyMap_append<KT(!new),VT(!new),CKT(!new),CVT(!new)>(cm:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT,
                                                                           ck:CKT, cval:CVT)
    requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
    // Injectivity
    requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
    requires RefineKey.requires(ck)
    requires RefineValue.requires(cval)
    requires ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck
    ensures  var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
             var rm' := AbstractifyMap(cm[ck := cval], RefineKey, RefineValue, ReverseKey);
             rm' == AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)]
  {
    var rm := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
    var cm' := cm[ck := cval];
    var rm' := AbstractifyMap(cm', RefineKey, RefineValue, ReverseKey);
    var r_cm' := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)];

    forall rk | rk in rm'
      ensures rk in r_cm'
      ensures r_cm'[rk] == rm'[rk]
    {
      Lemma_AbstractifyMap_basic_properties(cm', RefineKey, RefineValue, ReverseKey);
      Lemma_AbstractifyMap_preimage(cm', RefineKey, RefineValue, ReverseKey);
      if (exists p :: p in cm' && RefineKey(p) == rk){
        var preimage :| preimage in cm' && RefineKey(preimage) == rk;
        if preimage in cm {
          Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);
          calc ==> {
            true;
            { Lemma_AbstractifyMap_preimage(cm, RefineKey, RefineValue, ReverseKey); }
            RefineKey(preimage) in rm;
            RefineKey(preimage) in rm';
            rk in r_cm';
          }
        } else {
          assert preimage == ck;
          assert RefineKey(preimage) in r_cm';
        }
      }
      reveal AbstractifyMap();
    }

    forall rk | rk in r_cm'
      ensures rk in rm'
    {
      Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);
      Lemma_AbstractifyMap_preimage(cm, RefineKey, RefineValue, ReverseKey);
      Lemma_AbstractifyMap_basic_properties(cm', RefineKey, RefineValue, ReverseKey);
      if rk in rm {
        if(exists p :: p in cm && RefineKey(p) == rk){
          var preimage :| preimage in cm && RefineKey(preimage) == rk;
          assert rk in rm';
        }
      } else {
        assert rk == RefineKey(ck);
      }
      reveal AbstractifyMap();
    }

    assert r_cm' == rm';
  }

  lemma Lemma_AbstractifyMap_remove<KT(!new),VT(!new),CKT(!new),CVT(!new)>(
    cm:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT, ck:CKT)
    requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
    // Injectivity
    requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
    requires RefineKey.requires(ck)
    requires ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck
    requires ck in cm
    ensures  var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
             var rm' := AbstractifyMap(RemoveElt(cm, ck), RefineKey, RefineValue, ReverseKey);
             RefineKey(ck) in rm &&
             rm' == RemoveElt(rm, RefineKey(ck))
  {
    Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);

    var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
    var smaller_cm := RemoveElt(cm, ck);
    var rm' := AbstractifyMap(smaller_cm, RefineKey, RefineValue, ReverseKey);
    var smaller_rm := RemoveElt(rm, RefineKey(ck));

    Lemma_AbstractifyMap_basic_properties(smaller_cm, RefineKey, RefineValue, ReverseKey);

    forall o | o in rm'
      ensures o in smaller_rm && rm'[o] == smaller_rm[o];
    {
      if (exists c :: c in smaller_cm && RefineKey(c) == o){
        var co :| co in smaller_cm && RefineKey(co) == o;
        assert co != ck;
        assert RefineKey(co) != RefineKey(ck);
      }
      reveal AbstractifyMap();
    }

    forall o | o in smaller_rm
      ensures o in rm' && rm'[o] == smaller_rm[o]
    {
      Lemma_AbstractifyMap_preimage(cm, RefineKey, RefineValue, ReverseKey);
      // var co :| co in cm && co != ck && RefineKey(co) == o;
      reveal AbstractifyMap();
    }

    assert forall o :: (o in rm' <==> o in smaller_rm) && (o in rm' ==> rm'[o] == smaller_rm[o]);
    assert rm' == smaller_rm;
  }

  lemma lemma_AbstractifyMap_properties<CKT(!new),CVT(!new),KT(!new),VT(!new)>(
    cm:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT)
    requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
    // Injectivity
    requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
    ensures  cm == map [] ==> AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey) == map []
    ensures  forall ck :: ck in cm <==> RefineKey.requires(ck) && RefineKey(ck) in AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)
    ensures  forall ck :: ck in cm ==> AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck)] == RefineValue(cm[ck])
    ensures  forall ck :: ck !in cm && RefineKey.requires(ck) ==> RefineKey(ck) !in AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)
    ensures  var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
             forall k :: k in rm ==> (exists ck :: ck in cm && RefineKey(ck) == k)
    ensures forall ck, cval {:trigger cm[ck := cval]} {:trigger RefineKey(ck), RefineValue(cval)} ::
              (RefineKey.requires(ck) && RefineValue.requires(cval)
               && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck) ==>
                var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
                var rm' := AbstractifyMap(cm[ck := cval], RefineKey, RefineValue, ReverseKey);
                rm' == AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)]
    ensures forall ck {:trigger RemoveElt(AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey), RefineKey(ck)) } ::
              (RefineKey.requires(ck) && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck && ck in cm) ==>
                var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
                var rm' := AbstractifyMap(RemoveElt(cm, ck), RefineKey, RefineValue, ReverseKey);
                rm' == RemoveElt(rm, RefineKey(ck))
  {
    Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);
    Lemma_AbstractifyMap_preimage(cm, RefineKey, RefineValue, ReverseKey);

    forall ck, cval | RefineKey.requires(ck) && RefineValue.requires(cval)
      && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck
      ensures var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
              var rm' := AbstractifyMap(cm[ck := cval], RefineKey, RefineValue, ReverseKey);
              rm' == AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)]
    {
      Lemma_AbstractifyMap_append(cm, RefineKey, RefineValue, ReverseKey, ck, cval);
    }

    forall ck | RefineKey.requires(ck) && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck && ck in cm
      ensures var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
              var rm' := AbstractifyMap(RemoveElt(cm, ck), RefineKey, RefineValue, ReverseKey);
              rm' == RemoveElt(rm, RefineKey(ck))
    {
      Lemma_AbstractifyMap_remove(cm, RefineKey, RefineValue, ReverseKey, ck);
    }
  }
  
// predicate MapIsAbstractable<KT(!new),VT,CKT(!new),CVT(!new)>(m:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT) 
//   reads RefineKey.reads, RefineValue.reads, ReverseKey.reads
// {
//   && (forall ck :: ck in m ==> RefineKey.requires(ck) && RefineValue.requires(m[ck]))
//   && (forall ck :: ck in m ==> ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck)
// }

// function {:opaque} AbstractifyMap<CKT(!new),CVT(!new),KT(!new),VT>(m:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT) : map<KT,VT>
//   reads RefineKey.reads, RefineValue.reads, ReverseKey.reads
//   requires forall ck :: ck in m ==> RefineKey.requires(ck) && RefineValue.requires(m[ck])
//   requires forall ck :: ck in m ==> ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck
//   ensures  var rm  := AbstractifyMap(m,RefineKey,RefineValue,ReverseKey);
//            forall k :: k in rm ==> (exists ck :: ck in m && RefineKey(ck) == k)
// {
//   // var new_domain := set ck | ck in m :: RefineKey(ck);
//   // map k | k in new_domain :: RefineValue(m[ReverseKey(k)])
//   map k | k in (set ck | ck in m :: RefineKey(ck)) :: RefineValue(m[ReverseKey(k)])
// }

// lemma Lemma_AbstractifyMap_basic_properties<CKT,CVT,KT,VT>(m:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT)
//   requires MapIsAbstractable(m, RefineKey, RefineValue, ReverseKey)
//   // Injectivity
//   requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
//   ensures  m == map [] ==> AbstractifyMap(m, RefineKey, RefineValue, ReverseKey) == map []
//   ensures  forall ck :: ck in m <==> RefineKey.requires(ck) && RefineKey(ck) in AbstractifyMap(m, RefineKey, RefineValue, ReverseKey)
//   ensures  forall ck :: ck in m ==> AbstractifyMap(m, RefineKey, RefineValue, ReverseKey)[RefineKey(ck)] == RefineValue(m[ck])
// {
//   reveal AbstractifyMap();
// }

// lemma Lemma_AbstractifyMap_preimage<KT(!new),VT,CKT(!new),CVT(!new)>(cm:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT)
//   requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
//   // Injectivity
//   requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
//   ensures  var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
//            forall k :: k in rm ==> (exists ck :: ck in cm && RefineKey(ck) == k)
// {
//   var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
//   Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);
//   forall k | k in rm 
//     ensures (exists ck :: ck in cm && RefineKey(ck) == k)
//   {
//     reveal AbstractifyMap();
//   }
// }

// lemma Lemma_AbstractifyMap_append<KT(!new),VT,CKT(!new),CVT(!new)>(cm:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT,
//                                                  ck:CKT, cval:CVT)
//   requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
//   // Injectivity
//   requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
//   requires RefineKey.requires(ck)
//   requires RefineValue.requires(cval)
//   requires ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck
//   ensures  var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
//            var rm' := AbstractifyMap(cm[ck := cval], RefineKey, RefineValue, ReverseKey);
//            rm' == AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)]
// {
//   var rm := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
//   var cm' := cm[ck := cval];
//   var rm' := AbstractifyMap(cm', RefineKey, RefineValue, ReverseKey);
//   var r_cm' := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)];

//   forall rk | rk in rm'
//     ensures rk in r_cm'
//     ensures r_cm'[rk] == rm'[rk]
//   {
//     Lemma_AbstractifyMap_basic_properties(cm', RefineKey, RefineValue, ReverseKey);
//     Lemma_AbstractifyMap_preimage(cm', RefineKey, RefineValue, ReverseKey);
//     if (exists p :: p in cm' && RefineKey(p) == rk){
//       var preimage :| preimage in cm' && RefineKey(preimage) == rk;
//       if preimage in cm {
//         Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);
//         calc ==> {
//           true;
//             { Lemma_AbstractifyMap_preimage(cm, RefineKey, RefineValue, ReverseKey); }
//           RefineKey(preimage) in rm;
//           RefineKey(preimage) in rm';
//           rk in r_cm';
//         }
//       } else {
//         assert preimage == ck;
//         assert RefineKey(preimage) in r_cm';
//       }
//     }
//     reveal AbstractifyMap();
//   }

//   forall rk | rk in r_cm'
//     ensures rk in rm'
//   {
//     Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);
//     Lemma_AbstractifyMap_preimage(cm, RefineKey, RefineValue, ReverseKey);
//     Lemma_AbstractifyMap_basic_properties(cm', RefineKey, RefineValue, ReverseKey);
//     if rk in rm {
//       if(exists p :: p in cm && RefineKey(p) == rk){
//         var preimage :| preimage in cm && RefineKey(preimage) == rk;
//         assert rk in rm';
//       }
//     } else {
//       assert rk == RefineKey(ck);
//     }
//     reveal AbstractifyMap();
//   }

//   assert r_cm' == rm';
// }

// lemma Lemma_AbstractifyMap_remove<KT(!new),VT(!new),CKT(!new),CVT(!new)>(
//   cm:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT, ck:CKT)
//   requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
//   // Injectivity
//   requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
//   requires RefineKey.requires(ck)
//   requires ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck
//   requires ck in cm
//   ensures  var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
//            var rm' := AbstractifyMap(RemoveElt(cm, ck), RefineKey, RefineValue, ReverseKey);
//            RefineKey(ck) in rm &&
//            rm' == RemoveElt(rm, RefineKey(ck))
// {
//   Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);

//   var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
//   var smaller_cm := RemoveElt(cm, ck);
//   var rm' := AbstractifyMap(smaller_cm, RefineKey, RefineValue, ReverseKey);
//   var smaller_rm := RemoveElt(rm, RefineKey(ck));

//   Lemma_AbstractifyMap_basic_properties(smaller_cm, RefineKey, RefineValue, ReverseKey);

//   forall o | o in rm'
//     ensures o in smaller_rm && rm'[o] == smaller_rm[o];
//   {
//     if (exists c :: c in smaller_cm && RefineKey(c) == o){
//       var co :| co in smaller_cm && RefineKey(co) == o;
//       assert co != ck;
//       assert RefineKey(co) != RefineKey(ck);
//     }
//     reveal AbstractifyMap();
//   }

//   forall o | o in smaller_rm
//     ensures o in rm' && rm'[o] == smaller_rm[o]
//   {
//     Lemma_AbstractifyMap_preimage(cm, RefineKey, RefineValue, ReverseKey);
//     // var co :| co in cm && co != ck && RefineKey(co) == o;
//     reveal AbstractifyMap();
//   }

//   assert forall o :: (o in rm' <==> o in smaller_rm) && (o in rm' ==> rm'[o] == smaller_rm[o]);
//   assert rm' == smaller_rm;
// }

// lemma lemma_AbstractifyMap_properties<CKT(!new),CVT(!new),KT(!new),VT(!new)>(
//   cm:map<CKT,CVT>, RefineKey:CKT~>KT, RefineValue:CVT~>VT, ReverseKey:KT~>CKT)
//   requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
//   // Injectivity
//   requires forall ck1, ck2 :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
//   ensures  cm == map [] ==> AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey) == map []
//   ensures  forall ck :: ck in cm <==> RefineKey.requires(ck) && RefineKey(ck) in AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)
//   ensures  forall ck :: ck in cm ==> AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck)] == RefineValue(cm[ck])
//   ensures  forall ck :: ck !in cm && RefineKey.requires(ck) ==> RefineKey(ck) !in AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)
//   ensures  var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
//            forall k :: k in rm ==> (exists ck :: ck in cm && RefineKey(ck) == k)
//   ensures forall ck, cval {:trigger cm[ck := cval]} {:trigger RefineKey(ck), RefineValue(cval)} ::
//             (RefineKey.requires(ck) && RefineValue.requires(cval) 
//             && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck) ==>
//             var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
//             var rm' := AbstractifyMap(cm[ck := cval], RefineKey, RefineValue, ReverseKey);
//             rm' == AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)]
//   ensures forall ck {:trigger RemoveElt(AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey), RefineKey(ck)) } :: 
//             (RefineKey.requires(ck) && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck && ck in cm) ==>
//             var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
//             var rm' := AbstractifyMap(RemoveElt(cm, ck), RefineKey, RefineValue, ReverseKey);
//             rm' == RemoveElt(rm, RefineKey(ck))
// {
//   Lemma_AbstractifyMap_basic_properties(cm, RefineKey, RefineValue, ReverseKey);
//   Lemma_AbstractifyMap_preimage(cm, RefineKey, RefineValue, ReverseKey);

//   forall ck, cval | RefineKey.requires(ck) && RefineValue.requires(cval)
//                     && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck
//     ensures var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
//             var rm' := AbstractifyMap(cm[ck := cval], RefineKey, RefineValue, ReverseKey);
//             rm' == AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)]
//   {
//     Lemma_AbstractifyMap_append(cm, RefineKey, RefineValue, ReverseKey, ck, cval);
//   }

//   forall ck | RefineKey.requires(ck) && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck && ck in cm
//     ensures var rm  := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey);
//             var rm' := AbstractifyMap(RemoveElt(cm, ck), RefineKey, RefineValue, ReverseKey);
//             rm' == RemoveElt(rm, RefineKey(ck))
//   {
//     Lemma_AbstractifyMap_remove(cm, RefineKey, RefineValue, ReverseKey, ck);
//   }
// }

} 
