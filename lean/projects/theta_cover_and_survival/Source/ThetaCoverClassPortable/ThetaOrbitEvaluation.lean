import ThetaCoverClassPortable.ThetaLineOrbits
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.ThetaLineGaloisAlgebra

/-- The actual stabilizer-fixed values at a native line. -/
def fixedAt (L : KLine) : Subalgebra ℚ K where
  carrier := {z | ∀ σ : G, σ • L = L → σ z = z}
  algebraMap_mem' q σ _ := σ.commutes q
  zero_mem' σ _ := map_zero σ
  one_mem' σ _ := map_one σ
  add_mem' hz hw σ hs := by rw [map_add, hz σ hs, hw σ hs]
  mul_mem' hz hw σ hs := by rw [map_mul, hz σ hs, hw σ hs]

def orbitEvaluation : Associated →ₐ[ℚ] (∀ i : Fin 17, fixedAt (representative i)) where
  toFun f i := ⟨f.1 (representative i), fun σ hσ => by
    rw [← f.2 σ (representative i), hσ]⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- Reconstruction uses a PROVED actual field automorphism carrying the representative
onto each actual native line. Fixed-stabilizer values make it independent of that choice. -/
def orbitReconstruction (p : ∀ i : Fin 17, fixedAt (representative i)) : Associated := by
  refine ⟨fun L => orbitMover L (p (orbitOf L)), ?_⟩
  intro σ L
  change orbitMover (σ • L) (p (orbitOf (σ • L))) = σ (orbitMover L (p (orbitOf L)))
  rw [orbitOf_action]
  let b := orbitMover (σ • L)
  let a := orbitMover L
  let k : G := b⁻¹ * σ * a
  have hb : b • representative (orbitOf L) = σ • L := by
    simpa only [b, orbitOf_action] using orbitMover_spec (σ • L)
  have hk : k • representative (orbitOf L) = representative (orbitOf L) := by
    dsimp only [k, a]
    rw [mul_smul, mul_smul, orbitMover_spec, ← hb, inv_smul_smul]
  have hv : k • (p (orbitOf L) : K) = (p (orbitOf L) : K) := (p (orbitOf L)).2 k hk
  change b • (p (orbitOf L) : K) = σ • (a • (p (orbitOf L) : K))
  calc
    b • (p (orbitOf L) : K) = b • (k • (p (orbitOf L) : K)) := congrArg (b • ·) hv.symm
    _ = σ • (a • (p (orbitOf L) : K)) := by simp only [k, mul_smul, smul_inv_smul]

/-- The associated algebra is isomorphic to the product of its ACTUAL stabilizer fixed
subalgebras. This product is a theorem, not the definition of the associated algebra. -/
def orbitEvaluationEquiv : Associated ≃ₐ[ℚ] (∀ i : Fin 17, fixedAt (representative i)) :=
  AlgEquiv.ofBijective orbitEvaluation (by
    constructor
    · intro f g h
      apply Subtype.ext
      funext L
      have hh := congrArg (fun p : ∀ i : Fin 17, fixedAt (representative i) => (p (orbitOf L) : K)) h
      change f.1 (representative (orbitOf L)) = g.1 (representative (orbitOf L)) at hh
      calc
        f.1 L = orbitMover L (f.1 (representative (orbitOf L))) := by
          rw [← f.2, orbitMover_spec]
        _ = orbitMover L (g.1 (representative (orbitOf L))) := congrArg (orbitMover L) hh
        _ = g.1 L := by rw [← g.2, orbitMover_spec]
    · intro p
      refine ⟨orbitReconstruction p, ?_⟩
      funext i
      apply Subtype.ext
      change orbitMover (representative i) (p (orbitOf (representative i))) = (p i : K)
      rw [orbitOf_representative]
      exact (p i).2 _ (by simpa only [orbitOf_representative] using orbitMover_spec (representative i)))
end FourCorner.ThetaLineGaloisAlgebra
