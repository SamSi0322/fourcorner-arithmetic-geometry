import Mathlib.RingTheory.Discriminant

noncomputable section
namespace FourCorner.UnitDiscriminantClosure
variable {A F E : Type*} [CommRing A] [Field F] [Field E]
  [Algebra A F] [Algebra F E] [Algebra A E] [IsScalarTower A F E]
  [IsIntegrallyClosed A] [IsFractionRing A F] [Algebra.IsSeparable F E]

/-- A unit discriminant gives the actual full integral closure, not merely
an order contained in it. The proof uses the trace/discriminant denominator bound. -/
theorem integral_mem_adjoin (B : PowerBasis F E) (hB : IsIntegral A B.gen)
    (d : A) (hd : IsUnit d) (hdisc : algebraMap A F d = Algebra.discr F B.basis)
    {x : E} (hx : IsIntegral A x) : x ∈ Algebra.adjoin A ({B.gen} : Set E) := by
  letI : FiniteDimensional F E := B.finite
  have h := Algebra.discr_mul_isIntegral_mem_adjoin F (B := B) hB hx
  rw [← hdisc,IsScalarTower.algebraMap_smul] at h
  obtain ⟨u,rfl⟩ := hd
  have h' := (Algebra.adjoin A ({B.gen} : Set E)).smul_mem h (↑u⁻¹ : A)
  simpa only [smul_smul,Units.inv_mul,one_smul] using h'

theorem integralClosure_eq_adjoin (B : PowerBasis F E) (hB : IsIntegral A B.gen)
    (d : A) (hd : IsUnit d) (hdisc : algebraMap A F d = Algebra.discr F B.basis) :
    integralClosure A E = Algebra.adjoin A ({B.gen} : Set E) := by
  apply le_antisymm
  · intro x hx
    exact integral_mem_adjoin B hB d hd hdisc hx
  · apply Algebra.adjoin_le
    intro x hx
    rcases hx with rfl
    exact hB

end FourCorner.UnitDiscriminantClosure
#print axioms FourCorner.UnitDiscriminantClosure.integralClosure_eq_adjoin
