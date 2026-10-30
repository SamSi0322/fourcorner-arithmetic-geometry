import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_AdelicIndex
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
namespace FourCorner.SingleOriginPole
open AlgebraicCurve

/-- A genuine rational-base Riemann genus bound constructs arbitrarily deep
single-place poles. No algebraically closed constants or assumed pole map. -/
theorem exists_single_pole_above {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] (hgen : StichtenothGenusExists K F)
    (Q : Place K F) (hQ : Q.deg=1) (m0 : ℕ) :
    ∃ (f : F) (r : ℕ), f≠0 ∧ m0<r ∧ Q.ord f=-(r:ℤ) ∧
      ∀ v : Place K F, v≠Q → 0≤v.ord f := by
  classical
  obtain ⟨hNE,hL0,γ,D0,hreach⟩ := hgen
  letI : Nonempty (Place K F) := hNE
  letI : FiniteDimensional K (LSpace (0 : Divisor K F)) := hL0
  let D (n : ℕ) : Divisor K F := (n:ℤ) • Finsupp.single Q 1
  have coeff (n : ℕ) (v : Place K F) : D n v=if Q=v then (n:ℤ) else 0 := by
    simp [D,Finsupp.smul_apply,Finsupp.single_apply]
  have degree (n : ℕ) : Divisor.degree (D n)=(n:ℤ) := by
    simp [D,map_zsmul,Divisor.degree_single,hQ]
  let n := m0 + ell (D m0) + γ.natAbs + 2
  have hγ : γ≤(γ.natAbs:ℤ) := Int.le_natAbs
  have hdim : ell (D m0)<ell (D n) := by
    have h := hreach.isMax (D n)
    rw [degree] at h
    have hn : (n:ℤ)=(m0:ℤ)+(ell (D m0):ℤ)+(γ.natAbs:ℤ)+2 := by
      simp [n,Nat.cast_add]
    rw [hn] at h
    omega
  have hmn : m0≤n := by dsimp [n];omega
  have hcoeff : ∀ v, D m0 v≤D n v := by
    intro v
    rw [coeff,coeff]
    split_ifs <;> omega
  have hle : LSpace (D m0)≤LSpace (D n) := by
    intro f hf
    rcases mem_lSpace_iff_ord.mp hf with h0 | hf
    · rw [h0];exact Submodule.zero_mem _
    · apply mem_lSpace_iff_ord.mpr
      exact Or.inr (fun v => (neg_le_neg (hcoeff v)).trans (hf v))
  letI := finiteDimensional_lSpace (D n)
  have hlt : LSpace (D m0)<LSpace (D n) :=
    Submodule.lt_of_le_of_finrank_lt_finrank hle hdim
  obtain ⟨f,hf,hnot⟩ := SetLike.exists_of_lt hlt
  have hf0 : f≠0 := by intro h;rw [h] at hnot;exact hnot (Submodule.zero_mem _)
  have hords := (mem_lSpace_iff_ord.mp hf).resolve_left hf0
  have haway : ∀ v : Place K F, v≠Q → 0≤v.ord f := by
    intro v hv
    have h := hords v
    simpa only [coeff,if_neg (Ne.symm hv),neg_zero] using h
  have hpole : Q.ord f < -(m0:ℤ) := by
    by_contra h
    apply hnot
    apply mem_lSpace_iff_ord.mpr
    right
    intro v
    by_cases hv : v=Q
    · subst v
      simpa [coeff] using (le_of_not_gt h)
    · simpa only [coeff,if_neg (Ne.symm hv),neg_zero] using haway v hv
  refine ⟨f,(-Q.ord f).toNat,hf0,?_,?_,haway⟩ <;> omega

#print axioms exists_single_pole_above
end FourCorner.SingleOriginPole
