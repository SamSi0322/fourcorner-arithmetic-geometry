import ActualPairData

noncomputable section
namespace FourCorner.CommonSource
open OrderedSplit

/-- The literal two ordered paper slots determine the complete actual Kummer
sum, including the third slot derived from the cubic norm-one relation. -/
theorem two_paper_slots_full_sum {n : ℚ} (hn : n ≠ 0) (Q R : Point n)
    (h0 : kummerDelta n hn (Multiplicative.ofAdd Q) 0 * kummerDelta n hn (Multiplicative.ofAdd R) 0=
      scalarClass (-n) (neg_ne_zero.mpr hn))
    (h1 : kummerDelta n hn (Multiplicative.ofAdd Q) 1 * kummerDelta n hn (Multiplicative.ofAdd R) 1=
      scalarClass (-n) (neg_ne_zero.mpr hn)) :
    kummerDelta n hn (Multiplicative.ofAdd (Q+R))=commonKummerClass n hn := by
  have hs0 : kummerDelta n hn (Multiplicative.ofAdd (Q+R)) 0=scalarClass (-n) (neg_ne_zero.mpr hn) := by
    simpa only [kummerDelta_add,Pi.mul_apply] using h0
  have hs1 : kummerDelta n hn (Multiplicative.ofAdd (Q+R)) 1=scalarClass (-n) (neg_ne_zero.mpr hn) := by
    simpa only [kummerDelta_add,Pi.mul_apply] using h1
  have hprod := kummerDelta_product n hn (Q+R)
  simp only [Fin.prod_univ_three] at hprod
  rw [hs0,hs1] at hprod
  have hsquare : scalarClass (-n) (neg_ne_zero.mpr hn)*scalarClass (-n) (neg_ne_zero.mpr hn)=1 := by
    simpa only [pow_two] using Units.modPow.pow_eq_one (scalarClass (-n) (neg_ne_zero.mpr hn))
  rw [hsquare,one_mul] at hprod
  ext i
  fin_cases i
  · exact hs0
  · exact hs1
  · exact hprod

/-- Every paper source satisfying the stated whole-group splitting gives an
ActualPair. The square witnesses, finite remainders and torsion labels are not
extra existence assumptions: they are constructed from its actual Kummer slots. -/
theorem exists_actual_pair_from_paper {n : ℤ} (hn : n ≠ 0) (hnpos : 0 < (n:ℚ))
    (hcompl : IsCompl (H n hn) (twoTorsion (n:ℚ)))
    {a b c e : ℚ} (han : -(n:ℚ)<a) (ha : a<0) (hc : (n:ℚ)<c)
    (hQ : CongruentEquation (n:ℚ) a b) (hR : CongruentEquation (n:ℚ) c e)
    (h0 : kummerDelta (n:ℚ) (by exact_mod_cast hn)
        (Multiplicative.ofAdd (finitePoint (by exact_mod_cast hn) hQ)) 0 *
      kummerDelta (n:ℚ) (by exact_mod_cast hn)
        (Multiplicative.ofAdd (finitePoint (by exact_mod_cast hn) hR)) 0=
      scalarClass (-(n:ℚ)) (by exact_mod_cast (neg_ne_zero.mpr hn)))
    (h1 : kummerDelta (n:ℚ) (by exact_mod_cast hn)
        (Multiplicative.ofAdd (finitePoint (by exact_mod_cast hn) hQ)) 1 *
      kummerDelta (n:ℚ) (by exact_mod_cast hn)
        (Multiplicative.ofAdd (finitePoint (by exact_mod_cast hn) hR)) 1=
      scalarClass (-(n:ℚ)) (by exact_mod_cast (neg_ne_zero.mpr hn)))
    (hf : Even (commonSourceReturn (n:ℚ_[2]) a c).valuation) :
    ∃ S : ActualPair n hn, S.a=a ∧ S.b=b ∧ S.c=c ∧ S.e=e := by
  have ha0 : a ≠ 0 := ne_of_lt ha
  have hc0 : c ≠ 0 := ne_of_gt (lt_trans hnpos hc)
  have ham : a-(n:ℚ) ≠ 0 := ne_of_lt (by linarith)
  have hap : a+(n:ℚ) ≠ 0 := ne_of_gt (by linarith)
  have hcm : c-(n:ℚ) ≠ 0 := ne_of_gt (by linarith)
  have hcp : c+(n:ℚ) ≠ 0 := ne_of_gt (by linarith)
  have hs := two_paper_slots_full_sum (by exact_mod_cast hn) _ _ h0 h1
  obtain ⟨u,v,hu,hv⟩ := (source_squares_iff_kummer_sum (by exact_mod_cast hn)
    hQ hR ha0 hc0 ham hcm hap hcp).mpr hs
  have hsplit := splitsOverTwoTorsion_of_isCompl hcompl
  obtain ⟨U,hU,tauQ,htQ,hQU⟩ := hsplit (finitePoint (by exact_mod_cast hn) hQ)
  obtain ⟨V,hV,tauR,htR,hRV⟩ := hsplit (finitePoint (by exact_mod_cast hn) hR)
  refine ⟨{
    a := a
    b := b
    c := c
    e := e
    u := u
    v := v
    hnpos := hnpos
    han := han
    ha := ha
    hc := hc
    hQ := hQ
    hR := hR
    hu := hu
    hv := hv
    U := ⟨U,hU⟩
    V := ⟨V,hV⟩
    tauQ := tauQ
    tauR := tauR
    htQ := htQ
    htR := htR
    hQU := hQU
    hRV := hRV
    hf := hf
  },rfl,rfl,rfl,rfl⟩

#print axioms two_paper_slots_full_sum
#print axioms exists_actual_pair_from_paper
end FourCorner.CommonSource
