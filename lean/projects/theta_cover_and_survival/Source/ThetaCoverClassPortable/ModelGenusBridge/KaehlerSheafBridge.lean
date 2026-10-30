import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler

set_option autoImplicit false

noncomputable section
open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace FourCorner.KaehlerSheafBridge

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of R))

abbrev pmap {U V : X.Opens} (h : V ≤ U)
    (w : c.kaehlerPresheaf.obj (op U)) : c.kaehlerPresheaf.obj (op V) :=
  (c.kaehlerPresheaf.map (homOfLE h).op).hom w

theorem res_toSections {U V : X.Opens} (h : V ≤ U)
    (w : c.kaehlerPresheaf.obj (op U)) :
    c.kaehler.presheaf.map (homOfLE h).op (c.kaehlerToSections U w) =
      c.kaehlerToSections V (pmap c h w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    c.kaehlerPresheaf)).naturality (homOfLE h).op
  exact (congrArg (fun φ => φ.hom w) hnat).symm

def toSectionsLinear (U : X.Opens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler U
    Ω[Γ(X, U)⁄R] →ₗ[R] Γ(c.kaehler, U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler U
  letI := Scheme.TwoAffineOpenCover.isScalarTower_sections c c.kaehler U
  exact (show Ω[Γ(X, U)⁄R] →ₗ[Γ(X, U)] Γ(c.kaehler, U) from
    c.kaehlerToSectionsₗ U).restrictScalars R

variable (𝒱 : X.TwoAffineOpenCover)

theorem pmap_r0 (w : (𝒱.kaehlerSections c).M0) :
    pmap c (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0) w = (𝒱.kaehlerSections c).r0 w := by
  rfl

theorem pmap_r1 (w : (𝒱.kaehlerSections c).M1) :
    pmap c (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1) w = (𝒱.kaehlerSections c).r1 w := by
  rfl

def chartH0ToSheafH0 : (𝒱.kaehlerSections c).H0 →ₗ[R] (𝒱.sectionsOf c c.kaehler).H0 where
  toFun w := ⟨(c.kaehlerToSections 𝒱.U0 w.val.1, c.kaehlerToSections 𝒱.U1 w.val.2), by
    rw [TwoChartCech.Sections.mem_H0_iff]
    change c.kaehler.presheaf.map (homOfLE inf_le_left).op (c.kaehlerToSections 𝒱.U0 w.val.1) =
      c.kaehler.presheaf.map (homOfLE inf_le_right).op (c.kaehlerToSections 𝒱.U1 w.val.2)
    rw [res_toSections, res_toSections, pmap_r0, pmap_r1]
    exact congrArg (c.kaehlerToSections _) ((TwoChartCech.Sections.mem_H0_iff _ _).mp w.property)⟩
  map_add' w z := by
    apply Subtype.ext
    exact Prod.ext (c.kaehlerToSections_add 𝒱.U0 _ _) (c.kaehlerToSections_add 𝒱.U1 _ _)
  map_smul' a w := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝒱.U0
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝒱.U1
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler 𝒱.U0
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler 𝒱.U1
    apply Subtype.ext
    exact Prod.ext ((toSectionsLinear c 𝒱.U0).map_smul a w.val.1)
      ((toSectionsLinear c 𝒱.U1).map_smul a w.val.2)

theorem chartH0ToSheafH0_bijective : Function.Bijective (chartH0ToSheafH0 c 𝒱) := by
  constructor
  · intro w z h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    exact Prod.ext
      ((c.kaehlerToSections_bijective_of_isAffineOpen 𝒱.isAffineOpen_U0).1 (congrArg Prod.fst he))
      ((c.kaehlerToSections_bijective_of_isAffineOpen 𝒱.isAffineOpen_U1).1 (congrArg Prod.snd he))
  · rintro ⟨⟨s0, s1⟩, hs⟩
    obtain ⟨w0, hw0⟩ : ∃ w0 : (𝒱.kaehlerSections c).M0, c.kaehlerToSections 𝒱.U0 w0 = s0 :=
      (c.kaehlerToSections_bijective_of_isAffineOpen 𝒱.isAffineOpen_U0).2 s0
    obtain ⟨w1, hw1⟩ : ∃ w1 : (𝒱.kaehlerSections c).M1, c.kaehlerToSections 𝒱.U1 w1 = s1 :=
      (c.kaehlerToSections_bijective_of_isAffineOpen 𝒱.isAffineOpen_U1).2 s1
    have hw : (w0, w1) ∈ (𝒱.kaehlerSections c).H0 := by
      rw [TwoChartCech.Sections.mem_H0_iff]
      apply (c.kaehlerToSections_bijective_of_isAffineOpen 𝒱.isAffineOpen_inf).1
      rw [← pmap_r0, ← pmap_r1, ← res_toSections, ← res_toSections, hw0, hw1]
      exact (TwoChartCech.Sections.mem_H0_iff _ _).mp hs
    refine ⟨⟨(w0, w1), hw⟩, Subtype.ext ?_⟩
    exact Prod.ext hw0 hw1

def chartH0EquivSheafH0 : (𝒱.kaehlerSections c).H0 ≃ₗ[R] (𝒱.sectionsOf c c.kaehler).H0 :=
  LinearEquiv.ofBijective (chartH0ToSheafH0 c 𝒱) (chartH0ToSheafH0_bijective c 𝒱)

theorem exists_globalSectionsEquivChartH0 :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
    Nonempty (Γ(c.kaehler, ⊤) ≃ₗ[R] (𝒱.kaehlerSections c).H0) := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c c.kaehler ⊤
  obtain ⟨e, _⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 c c.kaehler
  exact ⟨e.trans (chartH0EquivSheafH0 c 𝒱).symm⟩

end FourCorner.KaehlerSheafBridge

