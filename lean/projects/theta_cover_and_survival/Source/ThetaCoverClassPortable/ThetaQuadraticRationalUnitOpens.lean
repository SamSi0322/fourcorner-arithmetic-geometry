import ThetaCoverClassPortable.ThetaQuadraticRationalUnitFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace FourCorner.ThetaQuadraticRationalUnitOpens
open ThetaLiteralModels ThetaDNativeProjRatios ThetaDNativeProjSections ThetaCoverRationalData
local instance : IsIntegral (D ℚ) := ThetaDPlaneChartSections.original_integral
local instance (j : Fin 3) : Nonempty (B j) := basic_nonempty j
abbrev Index := Fin 3 × Bool
abbrev ambient (i : Index) := B (ThetaQuotientCharts.targetIndex i.1)
def aSection (j : Fin 3) : Γ(D ℚ,B (ThetaQuotientCharts.targetIndex j)) :=
  sections _ (ThetaQuotientCharts.a j)
def bSection (j : Fin 3) : Γ(D ℚ,B (ThetaQuotientCharts.targetIndex j)) :=
  sections _ (ThetaQuotientCharts.b j)
def coefficient (i : Index) : Γ(D ℚ,ambient i) := if i.2 then aSection i.1 else bSection i.1
def root (i : Index) : ThetaQuadraticRationalUnitFields.F := if i.2 then ThetaQuadraticRationalUnitFields.qU i.1 else ThetaQuadraticRationalUnitFields.qT i.1
def U (i : Index) : (D ℚ).Opens := (D ℚ).basicOpen (coefficient i)

theorem affine_ambient (i : Index) : IsAffineOpen (ambient i) := by
  rw [ambient,←U_eq_basic]
  exact ThetaDPlaneChartSections.affine_U _
theorem affine_U (i : Index) : IsAffineOpen (U i) := (affine_ambient i).basicOpen _

def localUnit (i : Index) : Γ(D ℚ,U i)ˣ :=
  ((D ℚ).toRingedSpace.isUnit_res_basicOpen (coefficient i)).unit

theorem localUnit_value (i : Index) : (localUnit i : Γ(D ℚ,U i))=
    (D ℚ).presheaf.map (homOfLE ((D ℚ).basicOpen_le (coefficient i))).op (coefficient i) :=
  IsUnit.unit_spec _

theorem field_square (i : Index) :
    algebraMap Γ(D ℚ,ambient i) ThetaQuadraticRationalUnitFields.F (coefficient i)=root i^2*rationalH := by
  rcases i with ⟨j,b⟩
  cases b
  · exact (ThetaQuadraticRationalUnitFields.qT_square j).symm
  · exact (ThetaQuadraticRationalUnitFields.qU_square j).symm

theorem localUnit_square (i : Index) [Nonempty (U i)] :
    algebraMap Γ(D ℚ,U i) ThetaQuadraticRationalUnitFields.F (localUnit i:Γ(D ℚ,U i))=root i^2*rationalH := by
  rw [localUnit_value]
  have hr : algebraMap Γ(D ℚ,U i) ThetaQuadraticRationalUnitFields.F
      ((D ℚ).presheaf.map (homOfLE ((D ℚ).basicOpen_le (coefficient i))).op (coefficient i))=
      algebraMap Γ(D ℚ,ambient i) ThetaQuadraticRationalUnitFields.F (coefficient i) := by
    exact (D ℚ).presheaf.germ_res_apply (homOfLE ((D ℚ).basicOpen_le (coefficient i))) _ _ _
  exact hr.trans (field_square i)

theorem pair_cover (j : Fin 3) :
    U (j,true) ⊔ U (j,false)=B (ThetaQuotientCharts.targetIndex j) := by
  let z := sections (ThetaQuotientCharts.targetIndex j)
    (algebraMap ℚ (ThetaQuotientCharts.R j) (ThetaQuotientCharts.lambda j))
  have hh : aSection j+z*bSection j=1 := by
    have h:=congrArg (sections (ThetaQuotientCharts.targetIndex j)) (ThetaQuotientCharts.base_unit_ideal j)
    simpa only [map_add,map_mul,map_one,aSection,bSection,z] using h
  apply le_antisymm
  · exact sup_le ((D ℚ).basicOpen_le _) ((D ℚ).basicOpen_le _)
  · have hb := (D ℚ).basicOpen_add_le (aSection j) (z*bSection j)
    rw [hh,Scheme.basicOpen_one,Scheme.basicOpen_mul] at hb
    exact hb.trans (sup_le_sup_left inf_le_right _)

theorem cover : ⨆i : Index,U i=⊤ := by
  apply top_unique
  rw [←ThetaProjectionFiniteEtale.target_cover]
  apply iSup_le
  intro j
  change B (ThetaQuotientCharts.targetIndex j)≤_
  rw [←pair_cover]
  exact sup_le (le_iSup U (j,true)) (le_iSup U (j,false))

/-- Removing empty charts changes no point of the true open covering. -/
abbrev NonemptyIndex := {i : Index // Nonempty (U i)}
instance (i : NonemptyIndex) : Nonempty (U i.val) := i.property
abbrev W (i : NonemptyIndex) : (D ℚ).Opens := U i.val

theorem nonempty_cover : ⨆i : NonemptyIndex,W i=⊤ := by
  apply top_unique
  rw [←cover]
  apply iSup_le
  intro i x hx
  exact Opens.mem_iSup.mpr ⟨⟨i,⟨⟨x,hx⟩⟩⟩,hx⟩

theorem affine_inf (i j : NonemptyIndex) : IsAffineOpen (W i ⊓ W j) := by
  letI : IsProper (dToBase ℚ) := d_proper ℚ
  exact isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal (dToBase ℚ)))
    ⊤ (isAffineOpen_top _) (W i) (by simp) (W j) (by simp) (affine_U i.val) (affine_U j.val)

#print axioms cover
#print axioms localUnit_square
end FourCorner.ThetaQuadraticRationalUnitOpens
