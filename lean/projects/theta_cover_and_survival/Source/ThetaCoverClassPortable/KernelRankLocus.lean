import ThetaCoverClassPortable.RankLocus
import Mathlib.AlgebraicGeometry.Scheme

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped TensorProduct
namespace TwoChartCech
universe u
variable {R C0 C1 : Type u} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
  [Module.Flat R C0] [Module.Flat R C1]

theorem isClosed_setOf_le_finrank_ker_baseChange_residueField (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] (n : ℕ) :
    IsClosed {p : PrimeSpectrum R | n ≤ Module.finrank p.asIdeal.ResidueField
      (LinearMap.ker (d.baseChange p.asIdeal.ResidueField))} := by
  let kr : PrimeSpectrum R → ℕ := fun p => Module.finrank p.asIdeal.ResidueField
    (LinearMap.ker (d.baseChange p.asIdeal.ResidueField))
  let ck : PrimeSpectrum R → ℕ := fun p => Module.finrank p.asIdeal.ResidueField
    ((p.asIdeal.ResidueField ⊗[R] C1) ⧸ LinearMap.range (d.baseChange p.asIdeal.ResidueField))
  let χ : PrimeSpectrum R → ℤ := fun p => (kr p : ℤ) - ck p
  have hχ : IsLocallyConstant χ := isLocallyConstant_fibreEulerChar d
  have hc : ∀ r : ℕ, IsClosed {p : PrimeSpectrum R | r ≤ ck p} := by
    intro r
    have he : ck = fun p : PrimeSpectrum R => Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R] (C1 ⧸ LinearMap.range d)) := by
      funext p
      exact (FourCorner.FibreSurjectivity.cokernel_baseChange d p.asIdeal.ResidueField).some.finrank_eq
    rw [he]
    exact FourCorner.ClosedKernelRank.finite_module_isClosed_rank_ge r
  have hs : {p : PrimeSpectrum R | n ≤ kr p} =
      ⋃ e ∈ Set.range χ, (χ ⁻¹' {e} ∩ {p | Int.toNat ((n:ℤ)-e) ≤ ck p}) := by
    ext p
    simp only [Set.mem_setOf_eq,Set.mem_iUnion,Set.mem_inter_iff,Set.mem_preimage,
      Set.mem_singleton_iff,Set.mem_range,exists_prop]
    constructor
    · intro hp
      refine ⟨χ p,⟨p,rfl⟩,rfl,?_⟩
      rw [Int.toNat_le]
      dsimp [χ]
      omega
    · rintro ⟨e,_,he,hle⟩
      rw [Int.toNat_le] at hle
      have he' : e = (kr p:ℤ)-ck p := he.symm
      omega
  change IsClosed {p : PrimeSpectrum R | n ≤ kr p}
  rw [hs]
  exact Set.Finite.isClosed_biUnion hχ.range_finite (fun e _ =>
    (hχ.isClosed_fiber e).inter (hc _))

/-- Pull back the genuine closed rank locus along any actual scheme map.
The identity-Spec specialization is the literal original geometric caller. -/
theorem isClosed_setOf_le_finrank_ker_baseChange (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)]
    {T : AlgebraicGeometry.Scheme.{u}} (t : T ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)) (n : ℕ) :
    IsClosed (t.base ⁻¹' {p : PrimeSpectrum R | n ≤ Module.finrank p.asIdeal.ResidueField
      (LinearMap.ker (d.baseChange p.asIdeal.ResidueField))}) :=
  (isClosed_setOf_le_finrank_ker_baseChange_residueField d n).preimage t.continuous

#print axioms isClosed_setOf_le_finrank_ker_baseChange
end TwoChartCech
