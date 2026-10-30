import ThetaCoverClassPortable.GaloisAffineCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct Pointwise
namespace FourCorner.ThetaLocalSurvival.ComponentDescent
attribute [local instance high] Algebra.TensorProduct.rightAlgebra
variable {Y : Scheme} (f : Y ⟶ qqBase)

/-- Every fibre of the literal geometric scalar-extension projection is
an ACTUAL Galois orbit. All points in the fibre are covered by the actual
affine tensor chart; no selected-point or fixed-label assertion is used. -/
theorem geometricProjection_fibre_orbit (x y : geometricScheme f)
    (hxy : geometricProjection f x=geometricProjection f y) :
    ∃σ : GaloisGroup,geometricHomeomorph f σ x=y := by
  obtain ⟨A,j,hjOpen,hx,_⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X:=Y) (U:=⊤) (show geometricProjection f x∈(⊤ : Y.Opens) from trivial)
  let qA : ℚ →+* A := (Spec.preimage (j ≫ f)).hom
  letI : Algebra ℚ A := qA.toAlgebra
  letI : IsOpenImmersion j := hjOpen
  have hj : j ≫ f=chartBase A := (Spec.map_preimage (j ≫ f)).symm
  have hxr : x∈Set.range (geometricChartMap f A j hj) := by
    rw [geometricChartMap_range]
    exact hx
  have hyr : y∈Set.range (geometricChartMap f A j hj) := by
    rw [geometricChartMap_range]
    change geometricProjection f y∈Set.range j
    rw [←hxy]
    exact hx
  obtain ⟨p,hp⟩ := hxr
  obtain ⟨q,hq⟩ := hyr
  let inc := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] tensorRing Omega A).toRingHom)
  have h1 := congrArg (fun m : Spec (.of (tensorRing Omega A)) ⟶ Y => m p)
    (geometricChartMap_fst f A j hj)
  have h2 := congrArg (fun m : Spec (.of (tensorRing Omega A)) ⟶ Y => m q)
    (geometricChartMap_fst f A j hj)
  change geometricProjection f (geometricChartMap f A j hj p)=j (inc p) at h1
  change geometricProjection f (geometricChartMap f A j hj q)=j (inc q) at h2
  have hbase : geometricProjection f (geometricChartMap f A j hj p)=
      geometricProjection f (geometricChartMap f A j hj q) := by rw [hp,hq];exact hxy
  have hA : inc p=inc q := j.isOpenEmbedding.injective (h1.symm.trans (hbase.trans h2))
  have hUnder : p.asIdeal.under A=q.asIdeal.under A := by
    change Ideal.comap (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] tensorRing Omega A).toRingHom p.asIdeal=
      Ideal.comap (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] tensorRing Omega A).toRingHom q.asIdeal
    exact congrArg (fun z : Spec (.of A) => z.asIdeal) hA
  obtain ⟨σ,hσ⟩ := tensor_prime_fibre_transitive A p.asIdeal q.asIdeal hUnder
  have hAct : Spec.map (CommRingCat.ofHom (tensorAut Omega A σ.symm).toRingHom) p=q := by
    apply PrimeSpectrum.ext
    exact (tensor_spec_action_ideal A σ p).trans hσ.symm
  have h := congrArg (fun m : Spec (.of (tensorRing Omega A)) ⟶ geometricScheme f => m p)
    (geometricChartMap_action A f j hj σ)
  change geometricAction f σ (geometricChartMap f A j hj p)=
    geometricChartMap f A j hj (Spec.map (CommRingCat.ofHom (tensorAut Omega A σ.symm).toRingHom) p) at h
  rw [hAct,hp,hq] at h
  exact ⟨σ,h⟩

end FourCorner.ThetaLocalSurvival.ComponentDescent
