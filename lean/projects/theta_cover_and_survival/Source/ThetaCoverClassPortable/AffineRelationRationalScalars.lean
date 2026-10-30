import ThetaCoverClassPortable.AffineSchemeProjectionRank
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FourCorner.AffineRelationRank

abbrev invariantRing {X R : Scheme} (s t : R ⟶ X) : Subring Γ(X, ⊤) :=
  s.appTop.hom.eqLocus t.appTop.hom

lemma appLE_top {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.appLE ⊤ ⊤ le_top = f.appTop := by simp [Scheme.Hom.appLE]

/-- The actual common rational structure gives equal actions through s and t. -/
theorem common_rational_action {X R : Scheme} (q : X ⟶ Spec (.of ℚ))
    (s t : R ⟶ X) (hq : s ≫ q = t ≫ q) :
    s.appTop.hom.comp (Scheme.TwoAffineOpenCover.algebraOfHom q ⊤).algebraMap =
      t.appTop.hom.comp (Scheme.TwoAffineOpenCover.algebraOfHom q ⊤).algebraMap := by
  apply RingHom.ext
  intro a
  have h := congrArg (fun f : R ⟶ Spec (.of ℚ) =>
    f.appTop.hom ((Scheme.ΓSpecIso (.of ℚ)).inv.hom a)) hq
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, appLE_top] using h

/-- QQ maps into the LITERAL equality subring of the same two actual Gamma maps. -/
@[instance_reducible]
def invariantRationalAlgebra {X R : Scheme} (q : X ⟶ Spec (.of ℚ))
    (s t : R ⟶ X) (hq : s ≫ q = t ≫ q) : Algebra ℚ (invariantRing s t) :=
  ((Scheme.TwoAffineOpenCover.algebraOfHom q ⊤).algebraMap.codRestrict
    (invariantRing s t) (fun a => RingHom.congr_fun (common_rational_action q s t hq) a)).toAlgebra

/-- The existing invariant inclusion C -> Gamma(X) is retained, and the
QQ -> C -> Gamma(X) tower is proved from the constructed codRestriction. -/
theorem invariantRationalTower {X R : Scheme} (q : X ⟶ Spec (.of ℚ))
    (s t : R ⟶ X) (hq : s ≫ q = t ≫ q) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q ⊤
    letI := invariantRationalAlgebra q s t hq
    IsScalarTower ℚ (invariantRing s t) Γ(X, ⊤) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q ⊤
  letI := invariantRationalAlgebra q s t hq
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rfl

theorem positive_nat_isUnit (C : Type u) [CommRing C] [Algebra ℚ C]
    (n : ℕ) (hn : 0 < n) : IsUnit (n : C) := by
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hu : IsUnit (n : ℚ) := isUnit_iff_ne_zero.mpr hnq
  simpa only [map_natCast] using hu.map (algebraMap ℚ C)

/-- In particular r! is positive and a unit in the SAME literal invariant ring,
including r=0 and zero base rings. No external unit or QQ compatibility is added. -/
theorem factorial_isUnit_invariants {X R : Scheme} (q : X ⟶ Spec (.of ℚ))
    (s t : R ⟶ X) (hq : s ≫ q = t ≫ q) (r : ℕ) :
    letI := invariantRationalAlgebra q s t hq
    0 < r.factorial ∧ IsUnit (r.factorial : invariantRing s t) := by
  letI := invariantRationalAlgebra q s t hq
  exact ⟨Nat.factorial_pos r, positive_nat_isUnit _ _ (Nat.factorial_pos r)⟩

end FourCorner.AffineRelationRank
