import Genus17Generators
import FiniteTensorGenerators
import CommonRootFieldComparison

noncomputable section
namespace FourCorner.Genus17TensorComparison
open scoped TensorProduct
open AlgebraicCurve
open Genus17Geometry
variable (K L : Type*) [Field K] [Field L] [CharZero K] [CharZero L] [Algebra K L]
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

lemma value_map (t κ : K) (i : Fin 5) :
    CommonConstantMap.ratMap K L (CommonFiveIndependence.value t κ i) =
      CommonFiveIndependence.value (algebraMap K L t) (algebraMap K L κ) i := by
  fin_cases i <;> simp only [CommonFiveIndependence.value,CommonConstantMap.radicand_map,
    map_div₀,CommonConstantMap.ratMap_X,CommonConstantMap.ratMap_constant]

/-- Extending the rational-function constants gives the actual mapped five-root
field. All five independent squareclasses are used to prove tensor injectivity. -/
def baseChangeEquiv {t κ : K} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    letI := CommonFieldTensorDomain.ratAlgebra K L
    (RatFunc L) ⊗[RatFunc K] (field t κ) ≃ₐ[RatFunc L]
      field (algebraMap K L t) (algebraMap K L κ) := by
  letI := CommonFieldTensorDomain.ratAlgebra K L
  let F := RatFunc K
  let G := RatFunc L
  let E := field t κ
  let D := field (algebraMap K L t) (algebraMap K L κ)
  let C := AlgebraicClosure G
  letI := finite_over_line t κ h0 h1 hm
  letI : FiniteDimensional F E := finite_over_line t κ h0 h1 hm
  let f : E →ₐ[F] C := IsAlgClosed.lift
  have h0' : algebraMap K L t ≠ 0 := (map_ne_zero _).mpr h0
  have h1' : algebraMap K L t ≠ 1 := by simpa only [map_one] using (algebraMap K L).injective.ne h1
  have hm' : algebraMap K L t ≠ -1 := by simpa only [map_neg,map_one] using (algebraMap K L).injective.ne hm
  have hκ' : algebraMap K L κ ≠ 0 := (map_ne_zero _).mpr hκ
  letI : FiniteDimensional G D := finite_over_line (algebraMap K L t) (algebraMap K L κ) h0' h1' hm'
  let j : D →ₐ[G] C := IsAlgClosed.lift
  let r : Fin 5 → E := fiveRoot t κ
  let s : Fin 5 → D := fiveRoot (algebraMap K L t) (algebraMap K L κ)
  let q : Fin 5 → G := CommonFiveIndependence.value (algebraMap K L t) (algebraMap K L κ)
  have hr (i : Fin 5) : f (r i)^2 = algebraMap G C (q i) := by
    rw [← map_pow]
    change f (fiveRoot t κ i ^ 2) = _
    rw [fiveRoot_sq,AlgHom.commutes,IsScalarTower.algebraMap_apply F G C]
    change algebraMap G C (CommonConstantMap.ratMap K L (CommonFiveIndependence.value t κ i)) = _
    rw [value_map]
  have hs (i : Fin 5) : j (s i)^2 = algebraMap G C (q i) := by
    rw [← map_pow]
    change j (fiveRoot (algebraMap K L t) (algebraMap K L κ) i ^ 2) = _
    rw [fiveRoot_sq,AlgHom.commutes]
  have hgen : Algebra.adjoin F (Set.range r) = ⊤ := fiveRoot_generates t κ
  have hgenD : Algebra.adjoin G (Set.range s) = ⊤ := fiveRoot_generates _ _
  have halg (i : Fin 5) : IsAlgebraic G (f (r i)) := by
    apply IsIntegral.isAlgebraic
    refine ⟨Polynomial.X^2-Polynomial.C (q i),Polynomial.monic_X_pow_sub_C _ (by decide),?_⟩
    simp [hr i]
  let J := IntermediateField.adjoin G (Set.range (fun i => f (r i)))
  let JD := IntermediateField.adjoin G (Set.range (fun i => j (s i)))
  have hJJ : J = JD := CommonRootFieldComparison.adjoin_eq_of_equal_squares _ _
    (fun i => (hr i).trans (hs i).symm)
  have hRange : j.fieldRange = JD := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a,rfl⟩ := hx
      exact FiniteTensorGenerators.map_mem_adjoin (G := G) j s hgenD a
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨i,rfl⟩
      exact ⟨s i,rfl⟩
  let eD : D ≃ₐ[G] JD := j.equivFieldRange.trans (IntermediateField.equivOfEq hRange)
  let φ : G ⊗[F] E →ₐ[G] J := Algebra.TensorProduct.lift (Algebra.ofId G J)
    (FiniteTensorGenerators.imageHom (G := G) f r hgen) (fun _ _ => Commute.all _ _)
  have hsurj : Function.Surjective φ := FiniteTensorGenerators.tensor_lift_surjective (G := G) f r hgen halg
  have hdim : Module.finrank G J = Module.finrank F E := by
    rw [FiveSquareDegree.finrank_eq_thirtyTwo q (fun i => f (r i)) hr (by norm_num)
      (CommonFiveIndependence.nonempty_product_nonsquare h0' h1' hm' hκ'),
      degree_thirtyTwo t κ h0 h1 hm hκ]
  letI : FiniteDimensional G J := FiniteDimensional.of_finrank_pos (by rw [hdim]; exact Module.finrank_pos)
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_baseChange,hdim])).mpr hsurj
  exact (AlgEquiv.ofBijective φ ⟨hinj,hsurj⟩).trans ((IntermediateField.equivOfEq hJJ).trans eD.symm)

theorem rational_tensor_domain {t κ : K} (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) (hκ : κ ≠ 0) :
    letI := CommonFieldTensorDomain.ratAlgebra K L
    IsDomain ((RatFunc L) ⊗[RatFunc K] (field t κ)) := by
  letI := CommonFieldTensorDomain.ratAlgebra K L
  exact Function.Injective.isDomain (baseChangeEquiv K L h0 h1 hm hκ)
    (baseChangeEquiv K L h0 h1 hm hκ).injective
end FourCorner.Genus17TensorComparison
#print axioms FourCorner.Genus17TensorComparison.baseChangeEquiv
#print axioms FourCorner.Genus17TensorComparison.rational_tensor_domain
