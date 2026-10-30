import ThetaCoverClassPortable.DNativeSinglePoleCharts
import ThetaCoverClassPortable.DPoleDegree
import ThetaCoverClassPortable.PolynomialChartRank
import ThetaCoverClassPortable.PolynomialLevelFibre

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicCurve
namespace FourCorner.DRationalInputs
open ThetaLiteralModels
local instance : IsIntegral curve := integral
local instance : SmoothOfRelativeDimension 1 toBase := smooth
local instance : IsProper toBase := proper
local instance : Algebra ℚ field := constants

/-- The actual native generic-germ map, preserving the ORIGINAL structural
Q-algebra on the actual single-origin chart. -/
def chartGenericHom {m0 : ℕ} (d : NativeSinglePoleChartData m0) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase) d.U
    Γ(curve,d.U) →ₐ[ℚ] field := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase) d.U
  exact
    { toRingHom := (curve.presheaf.germ d.U (genericPoint curve) d.generic_U).hom
      commutes' := fun a => by
        change (curve.presheaf.germ d.U (genericPoint curve) d.generic_U).hom
          (algebraMap ℚ Γ(curve,d.U) a)=algebraMap ℚ field a
        rw [d.zeroRingEquiv_native,d.zeroRingEquiv_constants]
        rfl }

/-- A's actual chart, this continuation's genuine fraction-ring rank bridge,
and the actual full pole degree give B's precise polynomial rank. -/
theorem chart_polynomialRank_eq_pole {m0 : ℕ} (d : NativeSinglePoleChartData m0) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase) d.U
    PolynomialLevelFibre.polynomialRank (K:=ℚ) d.f=d.poleOrder := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase) d.U
  letI : Nonempty d.U := ⟨⟨genericPoint curve,d.generic_U⟩⟩
  let h := chartGenericHom d
  have hf : h d.f=d.generator := d.native_f
  have hfrac : letI := h.toRingHom.toAlgebra; IsFractionRing Γ(curve,d.U) field := by
    exact functionField_isFractionRing_of_isAffineOpen curve d.U d.affine_U
  have he := PolynomialChartRank.polynomial_rank_eq_field_degree d.f h
    (by rw [hf];exact d.transcendental) hfrac
  rw [hf] at he
  letI := d.fieldFinite
  exact he.trans (actual_field_degree_eq_pole d.generator d.poleOrder d.transcendental d.exact_pole d.regular_away)

/-- A REAL FiniteMapData on the exact original D/Q and exact original OD,
including ALL local base algebras and ALL level scalars with constant FREE
rank. Every defining field is proved from A+B and the actual pole-degree bridge. -/
def actual_finiteMapData (m0 : ℕ) : SmoothProperCurve.FiniteMapData (toBase) OD := by
  let d := actual_native_singlePole_charts m0
  letI : Nonempty d.U := ⟨⟨genericPoint curve,d.generic_U⟩⟩
  refine
    { U := d.U
      V := d.V
      f := d.f
      g := d.g
      m := d.poleOrder
      isAffineOpen_U := d.affine_U
      isAffineOpen_V := d.affine_V
      sup_eq_top := d.cover
      mem_U_iff := fun x => by rw [d.U_eq_originComplement];exact mem_originComplement x
      inf_eq_basicOpen := d.basic_f.symm
      inf_eq_basicOpen_g := d.basic_g.symm
      res_f_mul_res_g := d.reciprocal
      finite_f := d.finite_f
      finite_g := d.finite_g
      levelSet_free := ?_ }
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase) d.U
  intro S _ _ _ s
  have h := PolynomialLevelFibre.local_levelSet_free d.f d.injective_f d.finite_f S s
  exact ⟨h.1,h.2.1,h.2.2.trans (chart_polynomialRank_eq_pole d)⟩

theorem actual_finiteMapData_rank_gt (m0 : ℕ) : m0<(actual_finiteMapData m0).m :=
  (actual_native_singlePole_charts m0).poleOrder_gt

/-- This is EXACTLY the genuine unbounded/unit-rank input required by the
finite-etale HasChartSections source, with no external geometric premise. -/
theorem actual_unbounded_finiteMapData :
    ∀ m0 : ℕ, ∃ F : SmoothProperCurve.FiniteMapData (toBase) OD,
      m0≤F.m ∧ IsUnit (F.m:ℚ) := by
  intro m0
  let F := actual_finiteMapData m0
  have hm : m0<F.m := actual_finiteMapData_rank_gt m0
  refine ⟨F,hm.le,?_⟩
  apply isUnit_iff_ne_zero.mpr
  have hpos : 0<F.m := by omega
  exact_mod_cast Nat.ne_of_gt hpos

#print axioms chartGenericHom
#print axioms chart_polynomialRank_eq_pole
#print axioms actual_finiteMapData
#print axioms actual_unbounded_finiteMapData
end FourCorner.DRationalInputs
