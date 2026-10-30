import CriticalDirectMap

namespace FourCorner.CriticalMapNaturality
open CriticalConicParameter CriticalQuarticCubic CriticalDirectMap
variable {K L : Type*} [Field K] [Field L]

/-- All explicit inverse formulas commute with actual field maps. -/
theorem inverseA (f : K →+* L) (i x y : K) :
    f (CriticalDirectMap.inverseA i x y)=CriticalDirectMap.inverseA (f i) (f x) (f y) := by
  simp only [CriticalDirectMap.inverseA,inverseU,inverseV,inverseX,inverseL,first,denominator,scale,
    map_add,map_sub,map_mul,map_div₀,map_pow,map_one,map_ofNat]
theorem inverseB (f : K →+* L) (i x y : K) :
    f (CriticalDirectMap.inverseB i x y)=CriticalDirectMap.inverseB (f i) (f x) (f y) := by
  simp only [CriticalDirectMap.inverseB,inverseU,inverseV,inverseX,inverseL,second,denominator,scale,
    map_add,map_sub,map_mul,map_div₀,map_pow,map_one,map_ofNat,map_neg]
theorem inverseC (f : K →+* L) (i x y : K) :
    f (CriticalDirectMap.inverseC i x y)=CriticalDirectMap.inverseC (f i) (f x) (f y) := by
  simp only [CriticalDirectMap.inverseC,inverseU,inverseV,inverseX,inverseL,quarticY,denominator,scale,
    map_add,map_sub,map_mul,map_div₀,map_pow,map_one,map_ofNat,map_neg]
end FourCorner.CriticalMapNaturality
#print axioms FourCorner.CriticalMapNaturality.inverseA
#print axioms FourCorner.CriticalMapNaturality.inverseB
#print axioms FourCorner.CriticalMapNaturality.inverseC
