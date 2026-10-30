import ActualSourceDepth
import CSLogSupport.CommonSourceDyadicResidue

noncomputable section
namespace FourCorner.CommonSource

/-- Equality of abscissa depth determines equality of formal-parameter depth
for genuine finite points in the rational dyadic neighborhood. -/
theorem rational_formal_depth (n : ℤ) {x y w z : ℚ}
    (heP : CongruentEquation (n:ℚ) x y) (heQ : CongruentEquation (n:ℚ) w z)
    (hxv : padicValRat 2 x ≤ -4) (hwv : padicValRat 2 w ≤ -4)
    (hv : padicValRat 2 x=padicValRat 2 w) :
    (-(x:ℚ_[2])/y) ≠ 0 ∧ (-(w:ℚ_[2])/z) ≠ 0 ∧
    (-(x:ℚ_[2])/y).valuation=(-(w:ℚ_[2])/z).valuation := by
  let p := commonSourceDyadicOfRat n x y heP hxv
  let q := commonSourceDyadicOfRat n w z heQ hwv
  have hnrm := Padic.norm_int_le_one (p:=2) n
  obtain ⟨hp2,hpx,hpy⟩ := p.depth_spec hnrm
  obtain ⟨hq2,hqx,hqy⟩ := q.depth_spec hnrm
  have hxx : p.x.valuation=q.x.valuation := by
    change (x:ℚ_[2]).valuation=(w:ℚ_[2]).valuation
    simpa only [Padic.valuation_ratCast] using hv
  have hdp : p.depth=q.depth := by omega
  refine ⟨p.z_ne_zero hnrm,q.z_ne_zero hnrm,?_⟩
  change p.z.valuation=q.z.valuation
  rw [p.valuation_z hnrm,q.valuation_z hnrm,hdp]

/-- The residue conclusion uses the same integral representatives and any
common power-of-two scaling. -/
theorem scaled_residue_sign (A B : ℤ_[2]) (u v : ℚ_[2]) (k : ℕ)
    (hu : u ≠ 0) (hv : v ≠ 0) (heq : u.valuation=v.valuation)
    (hA : (A:ℚ_[2])=u/2^(k+1)) (hB : (B:ℚ_[2])=v/2^(k+1)) :
    commonSourceResidueFour A=commonSourceResidueFour B ∨
    commonSourceResidueFour A= -commonSourceResidueFour B := by
  have hAz : (A:ℚ_[2]) ≠ 0 := by rw [hA];exact div_ne_zero hu (pow_ne_zero _ (by norm_num))
  have hBz : (B:ℚ_[2]) ≠ 0 := by rw [hB];exact div_ne_zero hv (pow_ne_zero _ (by norm_num))
  have hval : (A:ℚ_[2]).valuation=(B:ℚ_[2]).valuation := by
    rw [hA,hB,commonRoot_val_div hu (pow_ne_zero _ (by norm_num)),
      commonRoot_val_div hv (pow_ne_zero _ (by norm_num)),heq]
  have hs := commonSource_residue_four_eq_or_neg_of_field_depth_eq
    (A:ℚ_[2]) (B:ℚ_[2]) hAz hBz A.property B.property hval
  simpa only [PadicInt.mk_coe] using hs

#print axioms rational_formal_depth
#print axioms scaled_residue_sign
end FourCorner.CommonSource
