import CriticalChartJacobian

noncomputable section
namespace FourCorner.CriticalChartSmooth
open Algebra AlgebraicGeometry MvPolynomial CriticalStandardCharts CriticalAmbientChart CriticalScalarGeometry CriticalChartJacobian
universe u
variable {k : Type u} [Field k]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false

def normalizedVector {F : Type*} [Field F] (j : Fin 4) (x : Fin 3 → F) : Fin 4 → F :=
  fun a=>if a=j then 1 else x (drop j a)
lemma normalizedVector_self {F : Type*} [Field F] (j : Fin 4) (x : Fin 3 → F) : normalizedVector j x j=1 := by simp [normalizedVector]
lemma normalizedVector_insert {F : Type*} [Field F] (j : Fin 4) (x : Fin 3 → F) (a : Fin 3) :
    normalizedVector j x (CriticalAmbientChart.insert j a)=x a := by
  simp [normalizedVector,insert_ne,drop_insert]

theorem field_point_coordinates (i : k) (j : Fin 4)
    (F : Type u) [Field F] [Algebra k F] (f : affineRing i j →ₐ[k] F) :
    CriticalElliptic23.CriticalCoordinates (algebraMap k F i)
      (normalizedVector j (fun a=>f (ax i j a))) := by
  have hrel (a : Fin 2) : f (Ideal.Quotient.mk (affineIdeal i j) (affineEquation i j a))=0 := by
    have h : Ideal.Quotient.mk (affineIdeal i j) (affineEquation i j a)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨a,rfl⟩)
    exact (congrArg f h).trans (map_zero f)
  have hc (c : k) : f (Ideal.Quotient.mk (affineIdeal i j) (C c))=algebraMap k F c := f.commutes c
  have h0 := hrel 0
  have h1 := hrel 1
  fin_cases j
  all_goals simp [affineEquation,CriticalQuotientChart.affineEquation,CriticalAmbientChart.dehom,
    CriticalProj23.equation,CriticalProj23.F0,CriticalProj23.F1,drop] at h0 h1
  all_goals erw [hc i] at h0 h1
  · change ((f (Ideal.Quotient.mk (affineIdeal i 0) (X 1)))^2-(1:F)^2=(algebraMap k F i)*((f (Ideal.Quotient.mk (affineIdeal i 0) (X 0)))^2-(1:F)^2)) ∧ ((f (Ideal.Quotient.mk (affineIdeal i 0) (X 2)))^2-(1:F)^2=(1+algebraMap k F i)*((f (Ideal.Quotient.mk (affineIdeal i 0) (X 0)))^2-(1:F)^2))
    constructor
    · linear_combination h0
    · linear_combination h1
  · change ((f (Ideal.Quotient.mk (affineIdeal i 1) (X 1)))^2-(f (Ideal.Quotient.mk (affineIdeal i 1) (X 0)))^2=(algebraMap k F i)*((1:F)^2-(f (Ideal.Quotient.mk (affineIdeal i 1) (X 0)))^2)) ∧ ((f (Ideal.Quotient.mk (affineIdeal i 1) (X 2)))^2-(f (Ideal.Quotient.mk (affineIdeal i 1) (X 0)))^2=(1+algebraMap k F i)*((1:F)^2-(f (Ideal.Quotient.mk (affineIdeal i 1) (X 0)))^2))
    constructor
    · linear_combination h0
    · linear_combination h1
  · change ((1:F)^2-(f (Ideal.Quotient.mk (affineIdeal i 2) (X 0)))^2=(algebraMap k F i)*((f (Ideal.Quotient.mk (affineIdeal i 2) (X 1)))^2-(f (Ideal.Quotient.mk (affineIdeal i 2) (X 0)))^2)) ∧ ((f (Ideal.Quotient.mk (affineIdeal i 2) (X 2)))^2-(f (Ideal.Quotient.mk (affineIdeal i 2) (X 0)))^2=(1+algebraMap k F i)*((f (Ideal.Quotient.mk (affineIdeal i 2) (X 1)))^2-(f (Ideal.Quotient.mk (affineIdeal i 2) (X 0)))^2))
    constructor
    · linear_combination h0
    · linear_combination h1
  · change ((f (Ideal.Quotient.mk (affineIdeal i 3) (X 2)))^2-(f (Ideal.Quotient.mk (affineIdeal i 3) (X 0)))^2=(algebraMap k F i)*((f (Ideal.Quotient.mk (affineIdeal i 3) (X 1)))^2-(f (Ideal.Quotient.mk (affineIdeal i 3) (X 0)))^2)) ∧ ((1:F)^2-(f (Ideal.Quotient.mk (affineIdeal i 3) (X 0)))^2=(1+algebraMap k F i)*((f (Ideal.Quotient.mk (affineIdeal i 3) (X 1)))^2-(f (Ideal.Quotient.mk (affineIdeal i 3) (X 0)))^2))
    constructor
    · linear_combination h0
    · linear_combination h1

lemma pair_nonzero {F : Type*} [Field F] (i : F) (hi : i^2= -1) (h2 : (2:F)≠0)
    (j : Fin 4) (x : Fin 3 → F)
    (hc : CriticalElliptic23.CriticalCoordinates i (normalizedVector j x)) :
    ∃ a : Fin 3, x (columns a 0)≠0 ∧ x (columns a 1)≠0 := by
  have hn : ∃ a,normalizedVector j x a≠0 := ⟨j,by rw [normalizedVector_self];exact one_ne_zero⟩
  have hz (a b : Fin 3) (ha : x a=0) (hb : x b=0) : a=b := by
    have he := zero_unique i hi h2 (normalizedVector j x) hc hn
      (CriticalAmbientChart.insert j a) (CriticalAmbientChart.insert j b)
      (by rw [normalizedVector_insert];exact ha) (by rw [normalizedVector_insert];exact hb)
    have := congrArg (drop j) he
    simpa only [drop_insert] using this
  by_cases h0 : x 0=0
  · refine ⟨2,?_,?_⟩
    · intro h;have := hz 0 1 h0 h;exact (by decide : (0:Fin 3)≠1) this
    · intro h;have := hz 0 2 h0 h;exact (by decide : (0:Fin 3)≠2) this
  by_cases h1 : x 1=0
  · refine ⟨1,h0,?_⟩
    intro h;have := hz 1 2 h1 h;exact (by decide : (1:Fin 3)≠2) this
  · exact ⟨0,h0,h1⟩


theorem field_point_jacobian (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (j : Fin 4)
    (F : Type u) [Field F] [Algebra k F] (f : affineRing i j →ₐ[k] F) :
    ∃ a : Fin 3, f (pres i j a).jacobian≠0 := by
  have hiF : (algebraMap k F i)^2= -(1:F) := by
    rw [←map_pow,hi,map_neg,map_one]
  have h2F : (2:F)≠0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k F)).mpr h2
  have h4F : (4:F)≠0 := by
    convert mul_ne_zero h2F h2F using 1 <;> ring
  obtain ⟨a,ha,hb⟩ := pair_nonzero (algebraMap k F i) hiF h2F j
    (fun b=>f (ax i j b)) (field_point_coordinates i j F f)
  have hab : CriticalAmbientChart.insert j (columns a 0)≠CriticalAmbientChart.insert j (columns a 1) := by
    intro he
    have he' := congrArg (drop j) he
    rw [drop_insert,drop_insert] at he'
    exact (by decide : (0:Fin 2)≠1) ((columns_injective a) he')
  have hm : algebraMap k F (minor i (CriticalAmbientChart.insert j (columns a 0))
      (CriticalAmbientChart.insert j (columns a 1)))≠0 :=
    (map_ne_zero _).mpr (minor_nonzero i hi h2 _ _ hab)
  refine ⟨a,?_⟩
  rw [jacobian_formula,map_mul,map_mul,map_mul,map_ofNat,f.commutes]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h4F hm) ha) hb

/-- Native scheme smoothness, relative dimension one, for every one of the
FOUR actual dehomogenized quotient rings. The span proof uses actual residue
fields of maximal ideals, not a renamed scalar Jacobian predicate. -/
theorem affine_smooth (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) (j : Fin 4) :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap k (affineRing i j)))) := by
  have hs := FiniteJacobianSmooth.jacobian_span_of_field_points (pres i j)
    (field_point_jacobian i hi h2 j)
  have h := FiniteJacobianSmooth.spec_smooth_of_jacobian_span (pres i j) hs
  simpa using h

end FourCorner.CriticalChartSmooth
#print axioms FourCorner.CriticalChartSmooth.field_point_coordinates
#print axioms FourCorner.CriticalChartSmooth.pair_nonzero

#print axioms FourCorner.CriticalChartSmooth.field_point_jacobian
#print axioms FourCorner.CriticalChartSmooth.affine_smooth
