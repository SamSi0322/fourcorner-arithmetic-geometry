import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_FGSubalgebra
import ThetaCoverClassPortable.Definitions.Def_Mathlib_Algebra_IsDirectLimit
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.RelPicard.LFP AlgebraicGeometry.Scheme.TwoAffineOpenCover NeronModelInfra

namespace FourCorner.ActualFGModel
variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

abbrev Stage := AlgebraicGeometry.FGSubalgebra R A
abbrev stageRing (i : Stage R A) := ↥i.1
abbrev transition (i j : Stage R A) (h : i ≤ j) : stageRing R A i →+* stageRing R A j :=
  (Subalgebra.inclusion (show i.1 ≤ j.1 from h)).toRingHom
abbrev into (i : Stage R A) : stageRing R A i →+* A := i.1.val.toRingHom

instance stageDirectedSystem : DirectedSystem (stageRing R A) (fun i j h => ⇑(transition R A i j h)) where
  map_self := fun _ _ => rfl
  map_map := fun _ _ _ _ _ _ => rfl

/-- The actual finitely generated subalgebras cover A and detect equality. -/
theorem stage_isDirectLimit :
    IsDirectLimit (fun i j h => ⇑(transition R A i j h)) (fun i => ⇑(into R A i)) where
  surj a := by
    let D : Subalgebra R A := Algebra.adjoin R {a}
    have hD : D.FG := ⟨{a}, by rw [Finset.coe_singleton]⟩
    exact ⟨⟨D,hD⟩,⟨a,Algebra.self_mem_adjoin_singleton R a⟩,rfl⟩
  inj i j x y hxy := by
    let k : Stage R A := ⟨i.1 ⊔ j.1,i.2.sup j.2⟩
    exact ⟨k,(le_sup_left : i.1 ≤ k.1),(le_sup_right : j.1 ≤ k.1),Subtype.ext hxy⟩
  compatibility _ _ _ _ := rfl

abbrev firstStage : Stage R A := ⟨⊥,Subalgebra.fg_bot⟩

variable {A}
variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))

/-- Actual base-change maps compose along actual subalgebra inclusions. -/
theorem baseChange_stage_comp (i k : Stage R A) (h : i ≤ k) :
    baseChangeSnd c (stageHom R k.1.val) ≫
      baseChangeSnd c (stageHom R (Subalgebra.inclusion (show i.1 ≤ k.1 from h))) =
    baseChangeSnd c (stageHom R i.1.val) := by
  rw [baseChangeSnd_comp]
  congr 1
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom k.1.val.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (show i.1 ≤ k.1 from h)).toRingHom) =
    Spec.map (CommRingCat.ofHom i.1.val.toRingHom)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end FourCorner.ActualFGModel
