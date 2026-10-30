import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.Dimension.Free

namespace Module
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Flat R M]

theorem finrank_baseChange_eq_one_of_rankAtStalk_eq_one
    (h : ∀ p : PrimeSpectrum R, rankAtStalk M p = 1)
    (K : Type w) [Field K] [Algebra R K] : finrank K (K ⊗[R] M) = 1 := by
  let p : PrimeSpectrum K := ⟨⊥, inferInstance⟩
  have he := rankAtStalk_baseChange (R:=R) (M:=M) (S:=K) p
  simpa [rankAtStalk_eq_finrank_of_free, h] using he
end Module
