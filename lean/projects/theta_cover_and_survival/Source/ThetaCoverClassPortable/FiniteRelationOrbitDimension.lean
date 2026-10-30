import ThetaCoverClassPortable.FiniteRelationOrbit
import ThetaCoverClassPortable.ProjectiveTraceRank

namespace FourCorner.FiniteRelationOrbit
open FourCorner.ProjectiveStabilizedDeterminant
noncomputable section
open scoped TensorProduct
universe u
variable {K A B : Type u} [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- The actual scheme-theoretic orbit fibre has dimension n, from the
GIVEN true constant source rank, without presuming any quotient flatness. -/
theorem orbit_finrank (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hfinite : letI := s.toRingHom.toAlgebra;Module.Finite A B)
    (hprojective : letI := s.toRingHom.toAlgebra;Module.Projective A B)
    (n : ℕ)
    (hrank : letI := s.toRingHom.toAlgebra;∀q : PrimeSpectrum A,Module.rankAtStalk B q=n) :
    letI := orbitAlgebra s x
    Module.finrank K (orbit s x)=n := by
  letI := orbitAlgebra s x
  letI := s.toRingHom.toAlgebra
  letI := x.toRingHom.toAlgebra
  letI := hfinite
  letI := hprojective
  let e := RingMapTensorPushout.tensorEquiv x.toRingHom s.toRingHom
  have h := Module.rankAtStalk_baseChange (R:=A) (M:=B) (S:=K) (⟨⊥,inferInstance⟩ : PrimeSpectrum K)
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  exact e.toLinearEquiv.finrank_eq.symm.trans (h.trans (hrank _))

#print axioms orbit_finrank
end
end FourCorner.FiniteRelationOrbit
