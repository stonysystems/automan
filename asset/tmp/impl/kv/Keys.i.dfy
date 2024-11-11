include ""


module Impl_SHT__Keys_i 
{

	function method CKeyLe(ka: CKey, kb: CKey) : bool 
		requires CKeyIsValid(ka)
		requires CKeyIsValid(kb)
		ensures CKeyLe(ka, kb) == KeyLe(AbstractifyCKeyToKey(ka), AbstractifyCKeyToKey(kb))
	{
		ka == kb || CKeyLt(ka, kb)
	}

	function method CKeyPlusLt(kp: CKeyPlus, kp': CKeyPlus) : bool 
		requires CKeyPlusIsValid(kp)
		requires CKeyPlusIsValid(kp')
		ensures CKeyPlusLt(kp, kp') == KeyPlusLt(AbstractifyCKeyPlusToKeyPlus(kp), AbstractifyCKeyPlusToKeyPlus(kp'))
	{
		kp != kp' 
		&& 
		[Printer for ... hasn't been implemented.]
	}

	function method CKeyPlusLe(kp: CKeyPlus, kp': CKeyPlus) : bool 
		requires CKeyPlusIsValid(kp)
		requires CKeyPlusIsValid(kp')
		ensures CKeyPlusLe(kp, kp') == KeyPlusLe(AbstractifyCKeyPlusToKeyPlus(kp), AbstractifyCKeyPlusToKeyPlus(kp'))
	{
		kp == kp' || CKeyPlusLt(kp, kp')
	}

	datatype CKeyRange = 
	CKeyRange(
		klo: CKeyPlus, 
		khi: CKeyPlus
	)

	predicate CKeyRangeIsValid(s: CKeyRange) 
	{
		CKeyRangeIsAbstractable(s) 
		&& 
		CKeyPlusIsValid(s.klo) 
		&& 
		CKeyPlusIsValid(s.khi)
	}

	predicate CKeyRangeIsAbstractable(s: CKeyRange) 
	{
		CKeyPlusIsAbstractable(s.klo) 
		&& 
		CKeyPlusIsAbstractable(s.khi)
	}

	function AbstractifyCKeyRangeToKeyRange(s: CKeyRange) : KeyRange 
		requires CKeyRangeIsAbstractable(s)
	{
		KeyRange(AbstractifyCKeyPlusToKeyPlus(s.klo), AbstractifyCKeyPlusToKeyPlus(s.khi))
	}

	function method CKeyRangeContains(range: CKeyRange, kp: CKeyPlus) : bool 
		requires CKeyRangeIsValid(range)
		requires CKeyPlusIsValid(kp)
		ensures CKeyRangeContains(range, kp) == KeyRangeContains(AbstractifyCKeyRangeToKeyRange(range), AbstractifyCKeyPlusToKeyPlus(kp))
	{
		CKeyPlusLe(range.klo, kp) 
		&& 
		CKeyPlusLt(kp, range.khi)
	}

	function method CRangesOverlap(kra: CKeyRange, krb: CKeyRange) : bool 
		requires CKeyRangeIsValid(kra)
		requires CKeyRangeIsValid(krb)
		ensures CRangesOverlap(kra, krb) == RangesOverlap(AbstractifyCKeyRangeToKeyRange(kra), AbstractifyCKeyRangeToKeyRange(krb))
	{
		CKeyRangeContains(kra, krb.klo) || CKeyRangeContains(kra, krb.khi) || CKeyRangeContains(krb, kra.klo) || CKeyRangeContains(krb, kra.khi)
	}

	function method CCompleteRange() : CKeyRange 
		ensures CCompleteRange() == CompleteRange()
	{
		CKeyRange(CKeyZero(), CKeyInf())
	}

	function method CEmptyKeyRange(kr: CKeyRange) : bool 
		requires CKeyRangeIsValid(kr)
		ensures CEmptyKeyRange(kr) == EmptyKeyRange(AbstractifyCKeyRangeToKeyRange(kr))
	{
		CKeyPlusLe(kr.khi, kr.klo)
	}
}
