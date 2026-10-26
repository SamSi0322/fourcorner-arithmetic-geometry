import CriticalBasicFull
import RefinedSupport.CriticalRefinedWave27

noncomputable section
namespace FourCorner.CriticalRefinedCompletion
variable {p : ℕ} [Fact p.Prime]

/-- Reduction of any actual integral completed-field square, without
substituting an integer or rational numerator. -/
theorem residue_square_of_padic_square (Q : ℤ_[p])
    (hs : IsSquare (Q : ℚ_[p])) : IsSquare (PadicInt.toZMod Q) := by
  obtain ⟨x,hx⟩ := hs
  have hn : ‖x‖ ≤ 1 := by
    have hsq : ‖x‖*‖x‖ ≤ 1 := by
      rw [←norm_mul,←hx]
      exact Q.2
    nlinarith [norm_nonneg x]
  let y : ℤ_[p] := ⟨x,hn⟩
  have he : Q=y*y := by apply Subtype.ext;exact hx
  exact ⟨PadicInt.toZMod y,by simpa only [map_mul] using congrArg PadicInt.toZMod he⟩

/-- Hensel with the prescribed SIGN of the residue root. Both possible
residue signs are respected by choosing the sign of an actual integral root. -/
theorem prescribed_integral_root (hodd : p≠2) (Q : ℤ_[p]) (v : ZMod p)
    (hv : v≠0) (hQ : PadicInt.toZMod Q=v^2) :
    ∃ u : ℤ_[p],u^2=Q ∧ PadicInt.toZMod u=v ∧ IsUnit u := by
  have h0 : PadicInt.toZMod Q≠0 := by rw [hQ];exact pow_ne_zero 2 hv
  obtain ⟨u,hu⟩ := padicInt_isSquare_of_isSquare_residue_unit hodd Q h0
    (by rw [hQ];exact IsSquare.sq v)
  have he : u^2=Q := by simpa only [pow_two] using hu.symm
  have hr : (PadicInt.toZMod u)^2=v^2 := by
    rw [←hQ,←he,map_pow]
  have hun : IsUnit u := by
    rw [PadicInt.isUnit_iff]
    apply le_antisymm (PadicInt.norm_le_one u)
    apply le_of_not_gt
    intro hn
    have hz : PadicInt.toZMod u=0 := by
      rw [←RingHom.mem_ker,PadicInt.ker_toZMod,IsLocalRing.mem_maximalIdeal]
      exact PadicInt.not_isUnit_iff.mpr hn
    exact h0 (by rw [←he,map_pow,hz];simp)
  rcases eq_or_eq_neg_of_sq_eq_sq (PadicInt.toZMod u) v hr with h | h
  · exact ⟨u,he,h,hun⟩
  · refine ⟨-u,by simpa only [neg_sq] using he,?_,hun.neg⟩
    rw [map_neg,h,neg_neg]

lemma unit_coe_valuation {u : ℤ_[p]} (hu : IsUnit u) : (u:ℚ_[p]).valuation=0 := by
  have hun : (u:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hu.ne_zero
  have hn : ‖(u:ℚ_[p])‖=1 := PadicInt.isUnit_iff.mp hu
  rw [Padic.norm_eq_zpow_neg_valuation hun] at hn
  have hpR : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hz := (zpow_eq_one_iff_right₀ (by positivity : (0:ℝ)≤p) (ne_of_gt hpR)).mp hn
  omega

/-- Given the exact normalized integer radicands, all four signed roots
are lifted into one actual Qp tuple with the prescribed normalized residues. -/
theorem signed_four_scaled_roots (hodd : p≠2) (s : ℕ) (Q q : Fin 4 → ℤ)
    (V : Fin 4 → ZMod p) (hV : ∀ j,V j≠0)
    (hfac : ∀ j,Q j=(p:ℤ)^(2*s)*q j)
    (hres : ∀ j,(q j:ZMod p)=(V j)^2) :
    ∃ u : Fin 4 → ℤ_[p], ∃ A : Fin 4 → ℚ_[p],
      (∀ j,u j^2=(q j:ℤ_[p]) ∧ PadicInt.toZMod (u j)=V j ∧ IsUnit (u j)) ∧
      (∀ j,A j=(p:ℚ_[p])^s*(u j:ℚ_[p])) ∧
      ∀ j,A j^2=(Q j:ℚ_[p]) ∧ (A j).valuation=(s:ℤ) := by
  have hh (j : Fin 4) := prescribed_integral_root hodd (q j:ℤ_[p]) (V j) (hV j)
    (by simpa only [map_intCast] using hres j)
  choose u hu using hh
  let A : Fin 4 → ℚ_[p] := fun j=>(p:ℚ_[p])^s*(u j:ℚ_[p])
  have hp : (p:ℚ_[p])≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨u,A,hu,fun _=>rfl,?_⟩
  intro j
  have hun : (u j:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr (hu j).2.2.ne_zero
  constructor
  · dsimp [A]
    rw [mul_pow]
    have he := congrArg (fun z : ℤ_[p]=>(z:ℚ_[p])) (hu j).1
    simp only [PadicInt.coe_pow,PadicInt.coe_intCast] at he
    rw [he,hfac j]
    push_cast
    congr 1
    rw [←pow_mul]
    congr 1
    omega
  · dsimp [A]
    rw [Padic.valuation_mul (pow_ne_zero _ hp) hun,Padic.valuation_pow,
      Padic.valuation_p,unit_coe_valuation (hu j).2.2]
    simp
end FourCorner.CriticalRefinedCompletion
#print axioms FourCorner.CriticalRefinedCompletion.residue_square_of_padic_square
#print axioms FourCorner.CriticalRefinedCompletion.prescribed_integral_root
#print axioms FourCorner.CriticalRefinedCompletion.unit_coe_valuation
#print axioms FourCorner.CriticalRefinedCompletion.signed_four_scaled_roots
