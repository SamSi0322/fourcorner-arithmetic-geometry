import ThetaCoverClassPortable.geometry.SchemeModelFiniteExtension
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

/-!
The two affine charts of the constructed finite-extension scheme model.
The opens are the images of the integral-closure charts under the gluing maps.
Coverage and nonempty intersection come from the actual pushout construction;
affineness of the intersection follows from its proper structural morphism.
-/

noncomputable section

namespace FourCorner.SchemeModelFiniteExtension

open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits IntermediateField

universe u

variable (K E : Type u) [Field K] [CharZero K] [Field E] [Algebra K E]

section Generator

variable (t : E) [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ E]
  [FiniteDimensional K⟮t⁻¹⟯ E]

/-- The two original affine charts cover the glued scheme. -/
def gluedTwoAffineOpenCover : (CurveModel.glued K t).TwoAffineOpenCover := by
  let U0 := (CurveModel.ι₀ K t).opensRange
  let U1 := (CurveModel.ιInf K t).opensRange
  have h0 : IsAffineOpen U0 := isAffineOpen_opensRange (CurveModel.ι₀ K t)
  have h1 : IsAffineOpen U1 := isAffineOpen_opensRange (CurveModel.ιInf K t)
  refine
    { U0 := U0
      U1 := U1
      isAffineOpen_U0 := h0
      isAffineOpen_U1 := h1
      sup_eq_top := ?_
      isAffineOpen_inf := ?_ }
  · ext x
    change (x ∈ Set.range (CurveModel.ι₀ K t).base ∨
      x ∈ Set.range (CurveModel.ιInf K t).base) ↔ True
    exact iff_true_intro (CurveModel.mem_range_ι₀_or_mem_range_ιInf K t x)
  · exact isAffineHom_diagonal_iff.mp
      (inferInstance : IsAffineHom (pullback.diagonal (CurveModel.gluedToBase K t)))
      ⊤ (isAffineOpen_top _) U0 (by simp) U1 (by simp) h0 h1

/-- The overlap of the two original charts contains an actual point. -/
theorem gluedTwoAffineOpenCover_overlap_nonempty :
    (((gluedTwoAffineOpenCover K E t).U0 ⊓ (gluedTwoAffineOpenCover K E t).U1 :
      (CurveModel.glued K t).Opens) : Set (CurveModel.glued K t)).Nonempty := by
  obtain ⟨x, h1, h0⟩ := CurveModel.range_ιInf_inter_range_ι₀_nonempty K t
  exact ⟨x, h0, h1⟩

end Generator

variable [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
  [FiniteDimensional (RatFunc K) E]

/-- A genuine two-affine-open cover of the constructed scheme model. -/
def twoAffineOpenCover : (model K E).C.TwoAffineOpenCover := by
  unfold model
  dsimp only [CurveModel.ofGenerator]
  have : Fact (CurveModel.towerGenerator K (L := E) ≠ 0) :=
    ⟨CurveModel.towerGenerator_ne_zero K⟩
  obtain ⟨hfin, hinv⟩ := CurveModel.finiteDimensional_adjoin_towerGenerator K (L := E)
  have := hfin
  have := hinv
  exact gluedTwoAffineOpenCover K E (CurveModel.towerGenerator K (L := E))

/-- The two affine opens have nonempty intersection. -/
theorem twoAffineOpenCover_overlap_nonempty :
    (((twoAffineOpenCover K E).U0 ⊓ (twoAffineOpenCover K E).U1 : (model K E).C.Opens) :
      Set (model K E).C).Nonempty := by
  unfold twoAffineOpenCover model
  have : Fact (CurveModel.towerGenerator K (L := E) ≠ 0) :=
    ⟨CurveModel.towerGenerator_ne_zero K⟩
  rcases h : CurveModel.finiteDimensional_adjoin_towerGenerator K (L := E) with ⟨hfin, hinv⟩
  dsimp only [h]
  have := hfin
  have := hinv
  exact gluedTwoAffineOpenCover_overlap_nonempty K E (CurveModel.towerGenerator K (L := E))

theorem twoAffineOpenCover_U0_nonempty :
    ((twoAffineOpenCover K E).U0 : Set (model K E).C).Nonempty := by
  obtain ⟨x, hx0, _⟩ := twoAffineOpenCover_overlap_nonempty K E
  exact ⟨x, hx0⟩

theorem twoAffineOpenCover_U1_nonempty :
    ((twoAffineOpenCover K E).U1 : Set (model K E).C).Nonempty := by
  obtain ⟨x, _, hx1⟩ := twoAffineOpenCover_overlap_nonempty K E
  exact ⟨x, hx1⟩

instance nonempty_twoAffineOpenCover_U0 : Nonempty (twoAffineOpenCover K E).U0 :=
  (twoAffineOpenCover_U0_nonempty K E).to_subtype

instance nonempty_twoAffineOpenCover_U1 : Nonempty (twoAffineOpenCover K E).U1 :=
  (twoAffineOpenCover_U1_nonempty K E).to_subtype

instance nonempty_twoAffineOpenCover_overlap :
    Nonempty ((twoAffineOpenCover K E).U0 ⊓ (twoAffineOpenCover K E).U1 : (model K E).C.Opens) :=
  (twoAffineOpenCover_overlap_nonempty K E).to_subtype

end FourCorner.SchemeModelFiniteExtension

#check @FourCorner.SchemeModelFiniteExtension.twoAffineOpenCover
#check @FourCorner.SchemeModelFiniteExtension.twoAffineOpenCover_overlap_nonempty
#print axioms FourCorner.SchemeModelFiniteExtension.gluedTwoAffineOpenCover
#print axioms FourCorner.SchemeModelFiniteExtension.gluedTwoAffineOpenCover_overlap_nonempty
#print axioms FourCorner.SchemeModelFiniteExtension.twoAffineOpenCover
#print axioms FourCorner.SchemeModelFiniteExtension.twoAffineOpenCover_overlap_nonempty
#print axioms FourCorner.SchemeModelFiniteExtension.twoAffineOpenCover_U0_nonempty
#print axioms FourCorner.SchemeModelFiniteExtension.twoAffineOpenCover_U1_nonempty
#print axioms FourCorner.SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_U0
#print axioms FourCorner.SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_U1
#print axioms FourCorner.SchemeModelFiniteExtension.nonempty_twoAffineOpenCover_overlap
