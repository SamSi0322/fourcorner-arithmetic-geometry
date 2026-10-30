import ThetaProjectiveRootPlaceEmbedding

namespace FourCorner.ThetaRootCanonicalSections
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open ThetaDGeometricModel ThetaDFieldCoordinates ThetaDExactChartTransitions ThetaDActualDifferential
open ThetaActualLineDifferentials ThetaContactDifferentialDivisors ThetaDPlaneRegularForms ThetaDGlobalCanonicalCandidate
open ThetaDNaturalGlobalDifferentials ThetaLineRootPointCharts ThetaGeometricResidueCoordinates
open SmoothProperRationalPointPlaces SchemePointStalkEvaluation ResiduePlaceEvaluation
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : ∀w : Place K field,w.DCoordGenerates := dCoordGenerates_of_isCurveOver
local instance : Module K Γ(toBase.kaehler,⊤) :=
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom toBase toBase.kaehler ⊤

 def coefficients : ThetaLine K → Fin 3 → K
  | .affine α β => ![-α,-β,1]
  | .vertical t => ![1,-t,0]
  | .yzero => ![0,1,0]

def globalSection (L : ThetaLine K) : Γ(toBase.kaehler,⊤) :=
  planeGlobalSectionEquiv (dotProductEquiv K (Fin 3) (coefficients L))
def differential (L : ThetaLine K) : Ω[field⁄K] := genericGerm (globalSection L)

 theorem affine_eq (α β : K) : differential (.affine α β)=affineDifferential α β := rfl
 theorem vertical_eq (t : K) : differential (.vertical t)=verticalDifferential t := rfl
 theorem yzero_eq : differential .yzero=y • omega := by
  have he := actual_global_line_germ (![0,1,0]:Fin 3→K)
  change differential .yzero=(algebraMap K field (0:K)+algebraMap K field (0:K)*x+
    algebraMap K field (1:K)*y) • omega at he
  simpa only [map_zero,map_one,zero_mul,zero_add,one_mul] using he

 theorem nonzero (L : ThetaLine K) : differential L≠0 := by
  cases L with
  | affine α β => exact affineDifferential_ne_zero α β
  | vertical t => exact verticalDifferential_ne_zero t
  | yzero => rw [yzero_eq];exact smul_ne_zero ThetaActualLineDifferentials.y_ne_zero omega_ne_zero

 theorem regular (L : ThetaLine K) : differential L∈regularDifferentials K field := germ_regular (globalSection L)

 theorem affine_X_factor (α β : K) :
    differential (.affine α β)=(v-algebraMap K field β*u-algebraMap K field α) • (x • omega) := by
  rw [affine_eq,affineDifferential,affineGlobalSection_germ]
  simp only [smul_smul]
  rw [affineFunction_times_y]
  congr 1
  rw [XZ_transition.1,XZ_transition.2]
  field_simp [x_ne_zero]
  ring

 theorem vertical_Y_factor (t : K) :
    differential (.vertical t)=(uY-algebraMap K field t) • (y • omega) := by
  rw [vertical_eq,verticalDifferential,verticalGlobalSection_germ]
  simp only [smul_smul]
  congr 1
  rw [YZ_transition.1]
  unfold verticalFunction
  field_simp [ThetaActualLineDifferentials.y_ne_zero]

/-- Actual linear equations vanishing at actual chart points lie in the
true maximal ideal, by the already proved genuine residue coordinates. -/
theorem linear_equation_maximal (j : Fin 3) (vals : Fin 2 → K)
    (hv : ∀i : Fin 1,MvPolynomial.aeval vals (ThetaDGeometricChartPoints.equation j i)=0)
    (a b c : K) (he : a*vals 0+b*vals 1+c=0) :
    ∃f : (rationalPlace j vals hv).val.toValuationSubring,
      (f:field)=algebraMap K field a*coordinate j 0+algebraMap K field b*coordinate j 1+algebraMap K field c ∧
        f∈IsLocalRing.maximalIdeal (rationalPlace j vals hv).val.toValuationSubring := by
  let p := rationalPlace j vals hv
  let A := p.val.toValuationSubring
  let e : A →ₐ[K] K := evaluate p.val p.property
  let U : A := coordinateValue j vals hv 0
  let V : A := coordinateValue j vals hv 1
  let f : A := algebraMap K A a*U+algebraMap K A b*V+algebraMap K A c
  refine ⟨f,?_,?_⟩
  · change ((algebraMap K A a:A):field)*(U:field)+((algebraMap K A b:A):field)*(V:field)+
      ((algebraMap K A c:A):field)=_
    rw [Place.coe_algebraMap,Place.coe_algebraMap,Place.coe_algebraMap,
      coordinateValue_coe,coordinateValue_coe]
  · rw [←localEval_kernel e]
    change e f=0
    have ea : e (algebraMap K A a)=a := e.commutes a
    have eb : e (algebraMap K A b)=b := e.commutes b
    have ec : e (algebraMap K A c)=c := e.commutes c
    have hU : e U=vals 0 := evaluate_coordinateValue j vals hv 0
    have hV : e V=vals 1 := evaluate_coordinateValue j vals hv 1
    simpa only [f,map_add,map_mul,ea,eb,ec,hU,hV] using he

 theorem positive_of_maximal_factor (w : Place K field) (η ζ : Ω[field⁄K])
    (hη : η≠0) (hζreg : ζ∈regularDifferentials K field)
    (f : w.toValuationSubring) (hfm : f∈IsLocalRing.maximalIdeal w.toValuationSubring)
    (he : η=(f:field) • ζ) : 0<w.ordDifferential η := by
  have hf : (f:field)≠0 := by intro hz;apply hη;rw [he,hz,zero_smul]
  have hfn : f≠0 := by intro hz;exact hf (congrArg Subtype.val hz)
  have hζ : ζ≠0 := by intro hz;apply hη;rw [he,hz,smul_zero]
  have hp := (Place.mem_maximalIdeal_iff_ord_pos' hfn).mp hfm
  have hb : 0≤w.ordDifferential ζ := w.ord_nonneg_of_mem (coefficient_regular_of_regular hζreg w)
  have hh := w.ordDifferential_smul hf (ThetaContactDifferentialDivisors.coefficient_ne_zero hζ w)
  rw [←he] at hh
  change 0<w.ord (f:field) at hp
  omega

 theorem finite_root_positive (L : ThetaLine K) (t : K) (ht : L.restrict t 1=0) :
    0 < (pointEquivRationalPlace toBase (finiteRootPoint L t ht)).val.ordDifferential (differential L) := by
  cases L with
  | affine α β =>
    have h : thetaF t 1 (α*t+β)=0 := by simpa [ThetaLine.restrict] using ht
    obtain ⟨f,hf,hm⟩ := linear_equation_maximal 1 ![t,α*t+β]
      (ThetaGeometricContactPoints.affine_relations α β t h) (-α) 1 (-β) (by simp)
    apply positive_of_maximal_factor _ _ (y • omega) (nonzero _) yomega_regular f hm
    rw [affine_eq,affineDifferential,affineGlobalSection_germ,hf]
    congr 1
    change affineFunction α β=algebraMap K field (-α)*uY+algebraMap K field (1:K)*vY+algebraMap K field (-β)
    simp only [affineFunction,map_neg,map_one,one_mul]
    ring
  | vertical s =>
    obtain ⟨f,hf,hm⟩ := linear_equation_maximal 2 ![s*t,t]
      (ThetaGeometricContactPoints.vertical_relations s t ht) 1 (-s) 0 (by simp)
    apply positive_of_maximal_factor _ _ omega (nonzero _) omega_regular f hm
    rw [vertical_eq,verticalDifferential,verticalGlobalSection_germ,hf]
    congr 1
    change verticalFunction s=algebraMap K field (1:K)*x+algebraMap K field (-s)*y+algebraMap K field (0:K)
    simp [verticalFunction,sub_eq_add_neg]
  | yzero =>
    obtain ⟨f,hf,hm⟩ := linear_equation_maximal 2 ![t,0] (Z_relations t 0 ht) 0 1 0 (by simp)
    apply positive_of_maximal_factor _ _ omega (nonzero _) omega_regular f hm
    rw [yzero_eq,hf]
    change y • omega=(algebraMap K field (0:K)*x+algebraMap K field (1:K)*y+algebraMap K field (0:K)) • omega
    simp

 theorem infinity_root_positive (L : ThetaLine K) (ht : L.restrict 1 0=0) :
    0 < (pointEquivRationalPlace toBase (infinityRootPoint L ht)).val.ordDifferential (differential L) := by
  cases L with
  | affine α β =>
    have h : thetaF 1 0 α=0 := by simpa [ThetaLine.restrict] using ht
    obtain ⟨f,hf,hm⟩ := linear_equation_maximal 0 ![0,α] (X_relations 0 α h) (-β) 1 (-α) (by simp)
    apply positive_of_maximal_factor _ _ (x • omega) (nonzero _) xomega_regular f hm
    rw [affine_X_factor,hf]
    congr 1
    change v-algebraMap K field β*u-algebraMap K field α=
      algebraMap K field (-β)*u+algebraMap K field (1:K)*v+algebraMap K field (-α)
    simp only [map_neg,map_one,one_mul]
    ring
  | vertical t =>
    have h : thetaF t 1 0=0 := by simpa [ThetaLine.restrict] using ht
    obtain ⟨f,hf,hm⟩ := linear_equation_maximal 1 ![t,0] (Y_relations t 0 h) 1 0 (-t) (by simp)
    apply positive_of_maximal_factor _ _ (y • omega) (nonzero _) yomega_regular f hm
    rw [vertical_Y_factor,hf]
    change (uY-algebraMap K field t) • (y • omega)=
      (algebraMap K field (1:K)*uY+algebraMap K field (0:K)*vY+algebraMap K field (-t)) • (y • omega)
    simp [sub_eq_add_neg]
  | yzero => norm_num [ThetaLine.restrict,thetaF] at ht

/-- Every genuine native projective zero, including the parameter at infinity,
is in the positive support of the SAME natural canonical line section. -/
theorem root_positive (L : ThetaLine K) (P : ThetaProjectiveRootPlaceEmbedding.Root L) :
    0 < (ThetaProjectiveRootPlaceEmbedding.rootPlace L P).ordDifferential (differential L) := by
  unfold ThetaProjectiveRootPlaceEmbedding.rootPlace ThetaProjectiveRootPlaceEmbedding.rootPoint
  split
  · exact infinity_root_positive L _
  · exact finite_root_positive L _ _

#print axioms finite_root_positive
#print axioms infinity_root_positive
#print axioms root_positive

#print axioms yzero_eq
#print axioms nonzero
#print axioms affine_X_factor
#print axioms vertical_Y_factor
#print axioms linear_equation_maximal
#print axioms positive_of_maximal_factor
end
end FourCorner.ThetaRootCanonicalSections
