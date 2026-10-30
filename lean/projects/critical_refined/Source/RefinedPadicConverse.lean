import RefinedProductSquares

noncomputable section
namespace FourCorner.CriticalRefinedCompletion
open CriticalNormalizedRadii CriticalResiduePatternData CriticalRefinedWave27
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Converse for one SAME actual Qp tuple at ANY positive depth. The literal
2t square condition alone already forces the original signed refined pattern. -/
theorem refined_pattern_of_padic_roots (hodd : p≠2) (X Y L : ℤ) (s : ℕ) (hs : 1≤s)
    (A : Fin 4 → ℚ_[p])
    (hprim : Nat.gcd (Nat.gcd X.natAbs Y.natAbs) L.natAbs=1)
    (hL : padicValInt p L=2*s)
    (hroot : ∀ j,A j^2=(criticalRadicands X Y L j:ℚ_[p]) ∧ (A j).valuation=(s:ℤ))
    (ht : IsSquare (2*oppositeParameter A L)) : RefinedPattern p := by
  have hLQ : (L:ℚ_[p]).valuation=((2*s:ℕ):ℤ) := by rw [Padic.valuation_intCast,hL]
  have heq := CriticalPadicConverse.equations_of_original X Y L A (fun j=>(hroot j).1)
  let D:=normalized_data X Y L s hs A heq hLQ (fun j=>(hroot j).2)
  obtain ⟨hx,hy,hi,hb,hr,h1,h2,h3⟩ :=
    pattern_data hodd X Y L s hs A hprim heq hLQ (fun j=>(hroot j).2)
  have hp : (p:ℚ_[p])≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hAf (j : Fin 4) : A j=(p:ℚ_[p])^s*(D.u j:ℚ_[p]) := by
    rw [D.u_coe j]
    field_simp [hp]
  have hLf : (L:ℚ_[p])=(p:ℚ_[p])^(2*s)*(D.H:ℚ_[p]) := by
    rw [D.H_coe]
    field_simp [hp]
  let den : ℤ_[p] :=(p:ℤ_[p])^s*D.H
  have hd : (den:ℚ_[p])≠0 := by
    change (p:ℚ_[p])^s*(D.H:ℚ_[p])≠0
    exact mul_ne_zero (pow_ne_zero _ hp) (PadicInt.coe_ne_zero.mpr D.H_unit.ne_zero)
  have hf := opposite_parameter_normalization s D.u D.H A L hAf hLf
  have hclear : (2*oppositeParameter A L)*(den:ℚ_[p])^2=
      ((2*normalizedProduct D.u:ℤ_[p]):ℚ_[p]) := by
    rw [hf]
    change (2*((normalizedProduct D.u:ℚ_[p])/(den:ℚ_[p])^2))*(den:ℚ_[p])^2=_
    simp only [PadicInt.coe_mul,(show ((2:ℤ_[p]):ℚ_[p])=2 from rfl)]
    field_simp
  have hsq : IsSquare (PadicInt.toZMod (2*normalizedProduct D.u)) := by
    apply residue_square_of_padic_square
    rw [←hclear]
    exact ht.mul (IsSquare.sq (den:ℚ_[p]))
  refine ⟨iota (p:=p) X Y,step D,radius D 0,radius D 1,radius D 2,radius D 3,
    ⟨hi,hb,h1,h2,h3⟩,hr 0,hr 1,hr 2,hr 3,?_⟩
  simpa only [normalizedProduct,radius,map_mul,map_add,map_ofNat] using hsq

/-- All sign choices in actual completed-field roots are covered by the
three exclusions, with no global rational/integer radius hypothesis. -/
theorem padic_refined_exclusions (hodd : p≠2) (X Y L : ℤ) (s : ℕ) (hs : 1≤s)
    (A : Fin 4 → ℚ_[p])
    (hprim : Nat.gcd (Nat.gcd X.natAbs Y.natAbs) L.natAbs=1)
    (hL : padicValInt p L=2*s)
    (hroot : ∀ j,A j^2=(criticalRadicands X Y L j:ℚ_[p]) ∧ (A j).valuation=(s:ℤ))
    (ht : IsSquare (2*oppositeParameter A L)) : p≠5 ∧ p≠13 ∧ p≠17 :=
  refined_necessary (refined_pattern_of_padic_roots hodd X Y L s hs A hprim hL hroot ht)
end FourCorner.CriticalRefinedCompletion
#print axioms FourCorner.CriticalRefinedCompletion.refined_pattern_of_padic_roots
#print axioms FourCorner.CriticalRefinedCompletion.padic_refined_exclusions
