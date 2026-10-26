import HpHenselOrdinary

namespace FourCorner.HpHenselBranch
open HpResidueCharts HpHenselOrdinary PadicUnitNeighbourhood
noncomputable section
variable {q : ℕ} [Fact q.Prime]

/-- The vanishing source root is the free parameter; all three remaining
roots are lifted by actual simultaneous Hensel, with no branch point discarded. -/
theorem branch (hp : q ≠ 2) (p a b : ℚ) (hb : b ≠ 0) (P A : ℤ_[q])
    (hP : (P : ℚ_[q]) = p)
    (hA : (A : ℚ_[q]) = a) (pivot : Fin 4)
    (hpivot : ∀ u : ℚ_[q], u^2 = values (p : ℚ_[q])
      ((a : ℚ_[q])+(b : ℚ_[q])*u^2) pivot)
    (r₀ : Fin 4 → ZMod q)
    (hr₀ : ∀ i, r₀ i ^ 2 = values (PadicInt.toZMod P) (PadicInt.toZMod A) i)
    (hn : ∀ i, i ≠ pivot → r₀ i ≠ 0) :
    ∃ (e : ℚ_[q]) (r : Fin 4 → ℚ_[q]), Transcendental ℚ e ∧
      (∀i,r i ≠ 0) ∧ ∀ i, r i^2 = values (p : ℚ_[q]) e i := by
  let I := {i : Fin 4 // i ≠ pivot}
  let f (i : I) (u : ℚ_[q]) := values (p : ℚ_[q])
    ((a : ℚ_[q])+(b : ℚ_[q])*u^2) i.val
  let v (i : I) := values P A i.val
  have ha (i : I) : PadicInt.toZMod (v i) = r₀ i.val^2 :=
    (map_values PadicInt.toZMod P A i.val).trans (hr₀ i.val).symm
  obtain ⟨u,hu,hr⟩ := transcendental_simultaneous_roots hp f 0 v
    (fun i => (continuous_values _ i.val).continuousAt.comp
      (by fun_prop : ContinuousAt (fun u : ℚ_[q] => (a : ℚ_[q])+(b : ℚ_[q])*u^2) 0))
    (fun i => by
      have hTwo : ((2 : ℤ_[q]) : ℚ_[q])=(2 : ℚ_[q]) := rfl
      change values (p : ℚ_[q]) ((a : ℚ_[q])+(b : ℚ_[q])*0^2) i.val=(v i : ℚ_[q])
      simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero]
      have hm (j : Fin 4) : values (p : ℚ_[q]) (a : ℚ_[q]) j=((values P A j : ℤ_[q]) : ℚ_[q]) := by
        fin_cases j <;> simp only [values,PadicInt.coe_mul,PadicInt.coe_add,
          PadicInt.coe_sub,PadicInt.coe_one,hTwo,hP,hA]
      exact hm i.val)
    (fun i => by rw [ha]; exact pow_ne_zero _ (hn i.val i.property))
    (fun i => by rw [ha]; exact IsSquare.sq _)
  choose z hz hs using hr
  let r (i : Fin 4) : ℚ_[q] := if h : i=pivot then u else z ⟨i,h⟩
  refine ⟨(a : ℚ_[q])+(b : ℚ_[q])*u^2,r,
    TranscendentalParameters.affine_square hu a b hb,?_,?_⟩
  · intro i
    by_cases h : i=pivot
    · subst i
      simp only [r,dif_pos rfl]
      intro hz
      apply hu
      rw [hz]
      exact isAlgebraic_zero
    · simpa only [r,dif_neg h] using hz ⟨i,h⟩
  · intro i
    by_cases h : i=pivot
    · subst i
      simpa only [r,dif_pos rfl] using hpivot u
    · simpa only [r,dif_neg h] using hs ⟨i,h⟩


#print axioms branch
end
end FourCorner.HpHenselBranch
