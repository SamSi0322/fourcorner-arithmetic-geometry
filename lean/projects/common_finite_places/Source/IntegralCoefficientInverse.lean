import GoodPrimeParameters

noncomputable section
namespace FourCorner.IntegralCoefficientInverse
variable {p : ℕ} [Fact p.Prime]

theorem exists_inverse (a : ℤ_[p]) (ha : PadicInt.toZMod a ≠ 0) :
    ∃ ai : ℤ_[p], a*ai=1 ∧ (ai : ℚ_[p])=(a : ℚ_[p])⁻¹ ∧
      PadicInt.toZMod ai=(PadicInt.toZMod a)⁻¹ := by
  obtain ⟨ai,hi⟩ := CommonFinitePlaces.integral_inverse_of_residue_ne_zero a ha
  have hf : (a : ℚ_[p])*(ai : ℚ_[p])=1 :=
    congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hi
  have hres : PadicInt.toZMod a*PadicInt.toZMod ai=1 := by
    simpa only [map_mul,map_one] using congrArg PadicInt.toZMod hi
  have ha0 : (a : ℚ_[p]) ≠ 0 := left_ne_zero_of_mul_eq_one hf
  refine ⟨ai,hi,?_,?_⟩
  · apply mul_left_cancel₀ ha0
    rw [hf,mul_inv_cancel₀ ha0]
  · apply mul_left_cancel₀ ha
    rw [hres,mul_inv_cancel₀ ha]

end FourCorner.IntegralCoefficientInverse
#print axioms FourCorner.IntegralCoefficientInverse.exists_inverse
