import LocalKummerSelection

noncomputable section
namespace FourCorner.CommonSource
open OrderedSplit

/-- The complete ordered rational source gives the full W+2H fibre in the
n=1 mod 8 case. The torsion-sum condition is proved, not an extra hypothesis. -/
theorem actual_source_coset_one {n : ℤ} (hn : n ≠ 0) (hn8 : n%8=1)
    {a b c e u v : ℚ}
    (hQ : CongruentEquation (n : ℚ) a b) (hR : CongruentEquation (n : ℚ) c e)
    (ha : a ≠ 0) (hc : c ≠ 0) (ham : a-n ≠ 0) (hcm : c-n ≠ 0)
    (hap : a+n ≠ 0) (hcp : c+n ≠ 0)
    (hu : u^2= -(a*c)/n) (hv : v^2= -((a-n)*(c-n))/n)
    (hcompl : IsCompl (H n hn) (twoTorsion (n : ℚ)))
    (U V W τQ τR : Point (n : ℚ))
    (hU : U ∈ H n hn) (hV : V ∈ H n hn)
    (hQU : finitePoint (by exact_mod_cast hn) hQ=U+τQ)
    (hRV : finitePoint (by exact_mod_cast hn) hR=V+τR)
    (htQ : 2 • τQ=0) (htR : 2 • τR=0)
    (hW0 : kummerDelta (n : ℚ) (by exact_mod_cast hn) (Multiplicative.ofAdd W) 0 =
      scalarClass (n : ℚ) (by exact_mod_cast hn))
    (hW1 : kummerDelta (n : ℚ) (by exact_mod_cast hn) (Multiplicative.ofAdd W) 1=1) :
    ∃ Z ∈ H n hn, U+V=W+2 • Z := by
  have hs := source_kummer_sum (by exact_mod_cast hn) hQ hR ha hc ham hcm hap hcp hu hv
  have ht := source_torsion_sum_one n hn hn8 _ _ U V τQ τR hU hV hQU hRV htQ htR hs
  exact source_coset_of_torsion_sum_T0 (by exact_mod_cast hn) hQ hR
    ha hc ham hcm hap hcp hu hv hcompl U V W τQ τR hQU hRV ht hW0 hW1

/-- The complete ordered rational source gives the full W+2H fibre in the
n=7 mod 8 case, with its literal signed distinguished row. -/
theorem actual_source_coset_seven {n : ℤ} (hn : n ≠ 0) (hn8 : n%8=7)
    {a b c e u v : ℚ}
    (hQ : CongruentEquation (n : ℚ) a b) (hR : CongruentEquation (n : ℚ) c e)
    (ha : a ≠ 0) (hc : c ≠ 0) (ham : a-n ≠ 0) (hcm : c-n ≠ 0)
    (hap : a+n ≠ 0) (hcp : c+n ≠ 0)
    (hu : u^2= -(a*c)/n) (hv : v^2= -((a-n)*(c-n))/n)
    (hcompl : IsCompl (H n hn) (twoTorsion (n : ℚ)))
    (U V W τQ τR : Point (n : ℚ))
    (hU : U ∈ H n hn) (hV : V ∈ H n hn)
    (hQU : finitePoint (by exact_mod_cast hn) hQ=U+τQ)
    (hRV : finitePoint (by exact_mod_cast hn) hR=V+τR)
    (htQ : 2 • τQ=0) (htR : 2 • τR=0)
    (hW0 : kummerDelta (n : ℚ) (by exact_mod_cast hn) (Multiplicative.ofAdd W) 0 =
      scalarClass (-(n : ℚ)) (by exact_mod_cast (neg_ne_zero.mpr hn)))
    (hW1 : kummerDelta (n : ℚ) (by exact_mod_cast hn) (Multiplicative.ofAdd W) 1 =
      scalarClass (-(n : ℚ)) (by exact_mod_cast (neg_ne_zero.mpr hn))) :
    ∃ Z ∈ H n hn, U+V=W+2 • Z := by
  have hs := source_kummer_sum (by exact_mod_cast hn) hQ hR ha hc ham hcm hap hcp hu hv
  have ht := source_torsion_sum_seven n hn hn8 _ _ U V τQ τR hU hV hQU hRV htQ htR hs
  exact source_coset_of_torsion_sum_zero (by exact_mod_cast hn) hQ hR
    ha hc ham hcm hap hcp hu hv hcompl U V W τQ τR hQU hRV ht hW0 hW1

#print axioms actual_source_coset_one
#print axioms actual_source_coset_seven
end FourCorner.CommonSource
