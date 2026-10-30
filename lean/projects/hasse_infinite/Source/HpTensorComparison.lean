import HpGeometricGenus
import FiniteTensorGenerators
import CommonRootFieldComparison
import CommonConstantTensorInjection
import CommonTensorFlat

namespace FourCorner.HpTensorComparison

open scoped TensorProduct
open HpLiteralField HpFieldGeometry IntermediateField
noncomputable section
variable (K L : Type*) [Field K] [Field L] [NeZero (2 : K)] [NeZero (2 : L)] [Algebra K L]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
local instance constantAlgebra (p : K) : Algebra K (field K p) := HpFieldGeometry.constantAlgebra K p
local instance constantModule (p : K) : Module K (field K p) := Algebra.toModule

theorem radicand_map (p : K) (i : Fin 4) :
    CommonConstantMap.ratMap K L (radicand K p i)=radicand L (algebraMap K L p) i := by
  fin_cases i <;> simp only [radicand,poly,map_mul,map_sub,map_add,map_one,map_ofNat,
    RatFunc.algebraMap_C,RatFunc.algebraMap_X,← RatFunc.algebraMap_eq_C,
    CommonConstantMap.ratMap_X,CommonConstantMap.ratMap_constant]

private theorem range_four {E : Type*} (r : Fin 4 → E) :
    Set.range r={r 0,r 1,r 2,r 3} := by
  ext x
  simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> tauto
  · rintro (h | h | h | h)
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
    · exact ⟨3,h.symm⟩

/-- Actual scalar extension over the rational function fields is the exact
mapped four-root Hasse field, with injectivity proved by degree sixteen. -/
def baseChangeEquiv (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    letI := CommonFieldTensorDomain.ratAlgebra K L
    (RatFunc L) ⊗[RatFunc K] (field K p) ≃ₐ[RatFunc L] field L (algebraMap K L p) := by
  letI := CommonFieldTensorDomain.ratAlgebra K L
  let F := RatFunc K
  let G := RatFunc L
  let E := field K p
  let D := field L (algebraMap K L p)
  let C := AlgebraicClosure G
  letI : FiniteDimensional F E := finite_over_line K p
  let f : E →ₐ[F] C := IsAlgClosed.lift
  have hp' : algebraMap K L p ≠ 0 := (map_ne_zero _).mpr hp
  have ha' : algebraMap K L p-1 ≠ 0 := by
    simpa only [map_sub,map_one] using (map_ne_zero (algebraMap K L)).mpr ha
  have hb' : algebraMap K L p+1 ≠ 0 := by
    simpa only [map_add,map_one] using (map_ne_zero (algebraMap K L)).mpr hb
  letI : FiniteDimensional G D := finite_over_line L (algebraMap K L p)
  let j : D →ₐ[G] C := IsAlgClosed.lift
  let r : Fin 4 → E := root K p
  let s : Fin 4 → D := root L (algebraMap K L p)
  let q : Fin 4 → G := radicand L (algebraMap K L p)
  have hr (i : Fin 4) : f (r i)^2=algebraMap G C (q i) := by
    rw [← map_pow]
    change f (root K p i^2)= _
    rw [root_sq,AlgHom.commutes,IsScalarTower.algebraMap_apply F G C]
    change algebraMap G C (CommonConstantMap.ratMap K L (radicand K p i))= _
    rw [radicand_map]
  have hs (i : Fin 4) : j (s i)^2=algebraMap G C (q i) := by
    rw [← map_pow]
    change j (root L (algebraMap K L p) i^2)= _
    rw [root_sq,AlgHom.commutes]
  have hgen : Algebra.adjoin F (Set.range r)=⊤ := root_generates K p
  have hgenD : Algebra.adjoin G (Set.range s)=⊤ := root_generates L (algebraMap K L p)
  have halg (i : Fin 4) : IsAlgebraic G (f (r i)) := by
    apply IsIntegral.isAlgebraic
    refine ⟨Polynomial.X^2-Polynomial.C (q i),Polynomial.monic_X_pow_sub_C _ (by decide),?_⟩
    simp [hr i]
  let J := IntermediateField.adjoin G (Set.range (fun i => f (r i)))
  let JD := IntermediateField.adjoin G (Set.range (fun i => j (s i)))
  have hJJ : J=JD := CommonRootFieldComparison.adjoin_eq_of_equal_squares _ _
    (fun i => (hr i).trans (hs i).symm)
  have hRange : j.fieldRange=JD := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a,rfl⟩ := hx
      exact FiniteTensorGenerators.map_mem_adjoin (G:=G) j s hgenD a
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨i,rfl⟩
      exact ⟨s i,rfl⟩
  let eD : D ≃ₐ[G] JD := j.equivFieldRange.trans (IntermediateField.equivOfEq hRange)
  let phi : G ⊗[F] E →ₐ[G] J := Algebra.TensorProduct.lift (Algebra.ofId G J)
    (FiniteTensorGenerators.imageHom (G:=G) f r hgen) (fun _ _ => Commute.all _ _)
  have hsurj : Function.Surjective phi := FiniteTensorGenerators.tensor_lift_surjective (G:=G) f r hgen halg
  have hJdim : Module.finrank G J=16 := by
    have heJ : J=IntermediateField.adjoin G {f (r 0),f (r 1),f (r 2),f (r 3)} := by
      dsimp [J]
      rw [range_four (fun i => f (r i))]
    have hd16 : Module.finrank G (IntermediateField.adjoin G {f (r 0),f (r 1),f (r 2),f (r 3)})=16 := by
      apply CommonFourDegree.finrank_four_eq_sixteen_of_products q (fun i => f (r i)) hr
      · simpa only [map_ofNat] using (map_ne_zero (algebraMap L (RatFunc L))).mpr (NeZero.ne (2 : L))
      · exact radicand_product_nonsquare L (algebraMap K L p) hp' ha' hb'
    exact (IntermediateField.equivOfEq heJ).toLinearEquiv.finrank_eq.trans hd16
  have hdim : Module.finrank G J=Module.finrank F E := by
    rw [hJdim,field_degree_sixteen K p hp ha hb]
  letI : FiniteDimensional G J := FiniteDimensional.of_finrank_pos (by rw [hJdim];norm_num)
  have hinj : Function.Injective phi :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [Module.finrank_baseChange,hdim])).mpr hsurj
  exact (AlgEquiv.ofBijective phi ⟨hinj,hsurj⟩).trans ((IntermediateField.equivOfEq hJJ).trans eD.symm)

theorem rational_tensor_domain (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    letI := CommonFieldTensorDomain.ratAlgebra K L
    IsDomain ((RatFunc L) ⊗[RatFunc K] (field K p)) := by
  letI := CommonFieldTensorDomain.ratAlgebra K L
  exact Function.Injective.isDomain (baseChangeEquiv K L p hp ha hb) (baseChangeEquiv K L p hp ha hb).injective

/-- Geometric integrality of the actual constant tensor, rather than a
freshly rebuilt field merely assigned the same defining equations. -/
theorem all_constants_domain (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    IsDomain (L ⊗[K] (field K p)) := by
  letI := CommonFieldTensorDomain.ratAlgebra K L
  letI : Algebra (RatFunc K) (L ⊗[K] RatFunc K) := Algebra.TensorProduct.rightAlgebra
  let f : L ⊗[K] RatFunc K →ₐ[RatFunc K] RatFunc L :=
    { (CommonConstantTensorInjection.tensorMap K L).toRingHom with
      commutes' := by
        intro r
        change CommonConstantTensorInjection.tensorMap K L (1 ⊗ₜ[K] r)=CommonConstantMap.ratMap K L r
        simp only [CommonConstantTensorInjection.tensorMap,Algebra.TensorProduct.lift_tmul,map_one,one_mul]
        rfl }
  letI := rational_tensor_domain K L p hp ha hb
  exact CommonTensorFlat.constant_tensor_isDomain_of_rational_tensor_domain f
    (CommonConstantTensorInjection.tensorMap_injective K L)

#print axioms baseChangeEquiv
#print axioms all_constants_domain

end
end FourCorner.HpTensorComparison
