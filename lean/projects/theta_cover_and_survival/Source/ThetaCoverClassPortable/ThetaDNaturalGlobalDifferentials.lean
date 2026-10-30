import ThetaCoverClassPortable.ThetaDOriginalCoordinateSections

namespace FourCorner.ThetaDNaturalGlobalDifferentials
open AlgebraicGeometry AlgebraicCurve CategoryTheory Opposite
open ThetaDGeometricModel ThetaDPlaneChartSections ThetaDFieldCoordinates
noncomputable section
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
abbrev V := ThetaDGlobalSheafBasis.planeCover
local instance : Nonempty V.U0 := geoU_nonempty 0
local instance : Nonempty V.U1 := geoU_nonempty 2
local instance : Nonempty (V.U0 ⊓ V.U1 : geometricD.Opens) := by
  refine ⟨⟨genericPoint geometricD,?_,?_⟩⟩
  · exact ((genericPoint_spec geometricD).mem_open_set_iff V.U0.isOpen).mpr (by simpa using (inferInstance : Nonempty V.U0))
  · exact ((genericPoint_spec geometricD).mem_open_set_iff V.U1.isOpen).mpr (by simpa using (inferInstance : Nonempty V.U1))
local instance sectionsAlgebra (U : geometricD.Opens) : Algebra K Γ(geometricD,U) :=
  Scheme.TwoAffineOpenCover.algebraOfHom toBase U
local instance sectionsModule (U : geometricD.Opens) : Module K Γ(toBase.kaehler,U) :=
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom toBase toBase.kaehler U

/-- Unlike the frozen abstract Nonempty endpoint, choose the EXISTENCE
statement that RETAINS the actual restrictions to BOTH opens. -/
def sheafGlueEquiv : Γ(toBase.kaehler,⊤) ≃ₗ[K] (V.sectionsOf toBase toBase.kaehler).H0 :=
  Classical.choose (V.exists_linearEquiv_sectionsOf_H0 toBase toBase.kaehler)

 theorem sheafGlue_restrictions (s : Γ(toBase.kaehler,⊤)) :
    (sheafGlueEquiv s).val=
      (toBase.kaehler.presheaf.map (homOfLE (le_top : V.U0≤⊤)).op s,
        toBase.kaehler.presheaf.map (homOfLE (le_top : V.U1≤⊤)).op s) :=
  Classical.choose_spec (V.exists_linearEquiv_sectionsOf_H0 toBase toBase.kaehler) s

def globalChartEquiv : Γ(toBase.kaehler,⊤) ≃ₗ[K] (V.kaehlerSections toBase).H0 :=
  sheafGlueEquiv.trans (KaehlerSheafBridge.chartH0EquivSheafH0 toBase V).symm

 theorem globalChart_restriction_zero (s : Γ(toBase.kaehler,⊤)) :
    toBase.kaehlerToSections V.U0 (globalChartEquiv s).val.1=
      toBase.kaehler.presheaf.map (homOfLE (le_top : V.U0≤⊤)).op s := by
  have hh : KaehlerSheafBridge.chartH0EquivSheafH0 toBase V (globalChartEquiv s)=sheafGlueEquiv s :=
    (KaehlerSheafBridge.chartH0EquivSheafH0 toBase V).apply_symm_apply (sheafGlueEquiv s)
  have h := congrArg (fun w : (V.sectionsOf toBase toBase.kaehler).H0=>w.val.1) hh
  exact h.trans (congrArg Prod.fst (sheafGlue_restrictions s))

 theorem globalChart_restriction_one (s : Γ(toBase.kaehler,⊤)) :
    toBase.kaehlerToSections V.U1 (globalChartEquiv s).val.2=
      toBase.kaehler.presheaf.map (homOfLE (le_top : V.U1≤⊤)).op s := by
  have hh : KaehlerSheafBridge.chartH0EquivSheafH0 toBase V (globalChartEquiv s)=sheafGlueEquiv s :=
    (KaehlerSheafBridge.chartH0EquivSheafH0 toBase V).apply_symm_apply (sheafGlueEquiv s)
  have h := congrArg (fun w : (V.sectionsOf toBase toBase.kaehler).H0=>w.val.2) hh
  exact h.trans (congrArg Prod.snd (sheafGlue_restrictions s))

/-- Invert the ACTUAL affine sheafification map, not an arbitrary linear
isomorphism of equal-dimensional spaces. Its inverse is unique. -/
def affineSectionsEquiv (U : geometricD.Opens) (hU : IsAffineOpen U) :
    Ω[Γ(geometricD,U)⁄K] ≃ₗ[K] Γ(toBase.kaehler,U) :=
  LinearEquiv.ofBijective (KaehlerSheafBridge.toSectionsLinear toBase U)
    (toBase.kaehlerToSections_bijective_of_isAffineOpen hU)

/-- The true global generic-field map: actual sheaf restriction, inverse
actual affine sheafification, then the ACTUAL Γ→functionField Kähler map. -/
def genericGerm : Γ(toBase.kaehler,⊤) →ₗ[K] Ω[field⁄K] :=
  (kaehlerToFunctionField toBase V.U0).comp
    ((affineSectionsEquiv V.U0 V.isAffineOpen_U0).symm.toLinearMap.comp
      (Scheme.TwoAffineOpenCover.restrictSections toBase toBase.kaehler le_top))

def genericGermOne : Γ(toBase.kaehler,⊤) →ₗ[K] Ω[field⁄K] :=
  (kaehlerToFunctionField toBase V.U1).comp
    ((affineSectionsEquiv V.U1 V.isAffineOpen_U1).symm.toLinearMap.comp
      (Scheme.TwoAffineOpenCover.restrictSections toBase toBase.kaehler le_top))

 theorem affine_inverse_restriction_zero (s : Γ(toBase.kaehler,⊤)) :
    (affineSectionsEquiv V.U0 V.isAffineOpen_U0).symm
      (toBase.kaehler.presheaf.map (homOfLE (le_top : V.U0≤⊤)).op s)=
        (globalChartEquiv s).val.1 := by
  apply (affineSectionsEquiv V.U0 V.isAffineOpen_U0).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (globalChart_restriction_zero s).symm

 theorem affine_inverse_restriction_one (s : Γ(toBase.kaehler,⊤)) :
    (affineSectionsEquiv V.U1 V.isAffineOpen_U1).symm
      (toBase.kaehler.presheaf.map (homOfLE (le_top : V.U1≤⊤)).op s)=
        (globalChartEquiv s).val.2 := by
  apply (affineSectionsEquiv V.U1 V.isAffineOpen_U1).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (globalChart_restriction_one s).symm

 theorem genericGerm_via_chart_zero (s : Γ(toBase.kaehler,⊤)) :
    genericGerm s=kaehlerToFunctionField toBase V.U0 (globalChartEquiv s).val.1 := by
  change kaehlerToFunctionField toBase V.U0
    ((affineSectionsEquiv V.U0 V.isAffineOpen_U0).symm
      (toBase.kaehler.presheaf.map (homOfLE (le_top : V.U0≤⊤)).op s))=_
  rw [affine_inverse_restriction_zero]

 theorem genericGerm_via_chart_one (s : Γ(toBase.kaehler,⊤)) :
    genericGermOne s=kaehlerToFunctionField toBase V.U1 (globalChartEquiv s).val.2 := by
  change kaehlerToFunctionField toBase V.U1
    ((affineSectionsEquiv V.U1 V.isAffineOpen_U1).symm
      (toBase.kaehler.presheaf.map (homOfLE (le_top : V.U1≤⊤)).op s))=_
  rw [affine_inverse_restriction_one]

 theorem genericGerm_chart_independent (s : Γ(toBase.kaehler,⊤)) : genericGerm s=genericGermOne s := by
  rw [genericGerm_via_chart_zero,genericGerm_via_chart_one]
  exact V.kaehlerToFunctionField_fst_eq_snd_of_mem_H0 toBase (globalChartEquiv s)

def chartRegularEquiv : (V.kaehlerSections toBase).H0 ≃ₗ[K] regularDifferentials K field :=
  Classical.choose (V.exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField toBase)

 theorem chartRegular_germ (w : (V.kaehlerSections toBase).H0) :
    (chartRegularEquiv w : Ω[field⁄K])=kaehlerToFunctionField toBase V.U0 w.val.1 :=
  Classical.choose_spec (V.exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField toBase) w

/-- Natural replacement for the abstract frozen globalEquiv: both retained
restriction formulas and the retained actual field-germ formula are proved. -/
def globalRegularEquiv : Γ(toBase.kaehler,⊤) ≃ₗ[K] regularDifferentials K field :=
  globalChartEquiv.trans chartRegularEquiv

 theorem globalRegularEquiv_germ (s : Γ(toBase.kaehler,⊤)) :
    (globalRegularEquiv s : Ω[field⁄K])=genericGerm s := by
  rw [genericGerm_via_chart_zero]
  exact chartRegular_germ (globalChartEquiv s)

/-- Corrected original-coordinate native-dual-plane to ACTUAL global sheaf
sections. The following theorem is about the TRUE generic germ, not a tuple
or an abstract selected vector-space equivalence. -/
def planeGlobalSectionEquiv : Module.Dual K (Fin 3 → K) ≃ₗ[K] Γ(toBase.kaehler,⊤) :=
  ThetaDOriginalCoordinateSections.planeFormEquiv.trans globalRegularEquiv.symm

 theorem actual_global_line_germ (a : Fin 3 → K) :
    genericGerm (planeGlobalSectionEquiv (dotProductEquiv K (Fin 3) a))=
      (algebraMap K field (a 2)+algebraMap K field (a 0)*x+
        algebraMap K field (a 1)*y) • ThetaDActualDifferential.omega := by
  rw [←globalRegularEquiv_germ]
  simp only [planeGlobalSectionEquiv,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  exact ThetaDOriginalCoordinateSections.planeForm_formula a

#print axioms sheafGlue_restrictions
#print axioms globalChart_restriction_zero
#print axioms globalChart_restriction_one
#print axioms genericGerm_chart_independent
#print axioms globalRegularEquiv_germ
#print axioms actual_global_line_germ
end
end FourCorner.ThetaDNaturalGlobalDifferentials
