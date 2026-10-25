import FourCorner.CriticalExcessActual
import FourCorner.CriticalExcessNormalize
import FourCorner.CriticalExcessProduct
import FourCorner.CriticalExcessFinite

namespace FourCorner.IntegralModel

/-- Corollary cor:crit-excess. Every content prime with an excess radius
valuation is critical and satisfies the two stated power-residue restrictions.
The four product-square alternatives are the literal rational parameters. -/
theorem critical_excess (M : IntegralModel) {p : ℕ} (hp : p.Prime)
    (hs : IsSquare M.oppositeProductSum ∨ IsSquare (2 * M.oppositeProductSum) ∨
      IsSquare (M.oppositeProductSum + 1) ∨ IsSquare (2 * (M.oppositeProductSum + 1)))
    (hG : p ∣ M.radiusContent) (j : Fin 4)
    (hex : padicValNat p M.radiusContent < padicValInt p (M.pairRadius j)) :
    padicValInt p M.L = 2 * padicValNat p M.radiusContent ∧
      p % 16 = 1 ∧ (2 : ZMod p)^((p-1)/4) = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by intro he; subst p; exact M.radiusContent_odd hG
  have hcrit := M.excess_critical_valuation hp j hex
  obtain ⟨i,b,hi,hb,h1,h2,h3⟩ := M.critical_prime_square_pattern hp hG hcrit
  have hz := M.excess_reducedRadius_eq_zero hp j hex
  have hz' : (M.criticalReducedRadius 0 : ZMod p) = 0 ∨
      (M.criticalReducedRadius 1 : ZMod p) = 0 ∨
      (M.criticalReducedRadius 2 : ZMod p) = 0 ∨
      (M.criticalReducedRadius 3 : ZMod p) = 0 := by
    fin_cases j
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inr hz))
  have hQ : IsSquare ((M.criticalReducedRadius 0 : ZMod p) * M.criticalReducedRadius 3 +
      (M.criticalReducedRadius 1 : ZMod p) * M.criticalReducedRadius 2) ∨
      IsSquare (2 * ((M.criticalReducedRadius 0 : ZMod p) * M.criticalReducedRadius 3 +
      (M.criticalReducedRadius 1 : ZMod p) * M.criticalReducedRadius 2)) := by
    simpa [criticalProductNumerator, criticalReducedRadius, pairRadius] using
      M.rational_product_square_residue hp hG hs
  obtain ⟨u,v,i',hi',hu,hv,hs'⟩ := FourCorner.critical_zero_corner_normalize
    (M.criticalReducedRadius 0 : ZMod p) (M.criticalReducedRadius 1 : ZMod p)
    (M.criticalReducedRadius 2 : ZMod p) (M.criticalReducedRadius 3 : ZMod p)
    i ((M.criticalReducedRadius 0 : ZMod p)^2) b hi hb rfl h1 h2 h3 hz' hQ
  obtain ⟨hmod,hpow⟩ := FourCorner.critical_excess_residue_conditions hp hp2 i' u v hi' hu hv hs'
  exact ⟨hcrit,hmod,hpow⟩

end FourCorner.IntegralModel
#print axioms FourCorner.IntegralModel.critical_excess
