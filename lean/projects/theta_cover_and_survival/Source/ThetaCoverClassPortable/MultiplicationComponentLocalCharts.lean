import ThetaCoverClassPortable.EtaleSchemePointLocalHomeomorph
import ThetaCoverClassPortable.MultiplicationComponentEndpoint
import Mathlib.NumberTheory.Padics.PadicNumbers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
open scoped Topology CategoryTheory.MonObj
namespace FourCorner.ThetaLocalSurvival.StrongTopology
open Multiplication Infinitesimal ComponentDescent

variable (K : Type) [NontriviallyNormedField K] [Algebra ℚ K] [CompleteSpace K]

/-- Actual scalar extension of an actual rational section, as a genuine Spec K morphism. -/
def rationalScalarPoint {X : Over base} (O : rationalBase ⟶ X) : KPoints K X :=
  Over.homMk ((pointObject K).hom≫O.left) (by
    rw [Category.assoc,O.w]
    exact Category.comp_id _)

variable (G X : Over base) [GrpObj G] [IsProper G.hom] [GeometricallyIntegral G.hom]
  [IsProper X.hom] (a : X ⟶ G) (O : rationalBase ⟶ X) (hO : O≫a=1) (m : ℕ) (hm : 1≤m)

def distinguishedComponentObject : Over base :=
  Over.mk (multiplicationComponentToBase G X a O hO m hm)

def distinguishedComponentProjection : distinguishedComponentObject G X a O hO m hm ⟶ X :=
  Over.homMk (multiplicationComponentProjection G X a O hO m hm)
    (multiplicationComponentProjection_over G X a O hO m hm)

def distinguishedComponentScalarOrigin : KPoints K (distinguishedComponentObject G X a O hO m hm) :=
  Over.homMk ((pointObject K).hom≫multiplicationComponentOrigin G X a O hO m hm) (by
    change ((pointObject K).hom≫multiplicationComponentOrigin G X a O hO m hm)≫
      multiplicationComponentToBase G X a O hO m hm=(pointObject K).hom
    rw [Category.assoc,multiplicationComponentOrigin_over,Category.comp_id])

@[simp] theorem distinguishedComponentScalarOrigin_projection :
    distinguishedComponentScalarOrigin K G X a O hO m hm ≫
      distinguishedComponentProjection G X a O hO m hm = rationalScalarPoint K O := by
  apply Over.OverMorphism.ext
  change ((pointObject K).hom≫multiplicationComponentOrigin G X a O hO m hm) ≫
    multiplicationComponentProjection G X a O hO m hm = (pointObject K).hom≫O.left
  rw [Category.assoc,multiplicationComponentOrigin_projection]


/-- The actual descended geometric component has local field analytic charts over X,
for every positive multiplication level m and every complete normed QQ-field. -/
theorem distinguishedComponent_points_localHomeomorph :
    IsLocalHomeomorph (fun Q : KPoints K (distinguishedComponentObject G X a O hO m hm) =>
      Q≫distinguishedComponentProjection G X a O hO m hm) := by
  obtain ⟨_,he⟩ := multiplicationComponentProjection_finite_etale G X a O hO m hm
  letI : Etale (distinguishedComponentProjection G X a O hO m hm).left := he
  exact etale_scheme_points_localHomeomorph K (distinguishedComponentProjection G X a O hO m hm)

/-- An actual open neighborhood of O(K) consists entirely of actual images of component
K-points; the neighborhood and lifting quantifiers are on genuine scheme-valued points. -/
theorem distinguishedComponent_origin_open_image :
    ∃ U : Set (KPoints K X), IsOpen U ∧ rationalScalarPoint K O∈U ∧
      ∀ P∈U,∃ Q : KPoints K (distinguishedComponentObject G X a O hO m hm),
        Q≫distinguishedComponentProjection G X a O hO m hm=P := by
  let π := fun Q : KPoints K (distinguishedComponentObject G X a O hO m hm) =>
    Q≫distinguishedComponentProjection G X a O hO m hm
  have h := distinguishedComponent_points_localHomeomorph K G X a O hO m hm
  refine ⟨Set.range π,?_,?_,?_⟩
  · simpa only [Set.image_univ] using h.isOpenMap Set.univ isOpen_univ
  · exact ⟨distinguishedComponentScalarOrigin K G X a O hO m hm,
      distinguishedComponentScalarOrigin_projection K G X a O hO m hm⟩
  · exact fun _ hP => hP

/-- The actual local-image statement simultaneously supplies every rational prime. -/
theorem distinguishedComponent_padic_origin_open_image (p : ℕ) [Fact p.Prime] :
    ∃ U : Set (KPoints ℚ_[p] X), IsOpen U ∧ rationalScalarPoint ℚ_[p] O∈U ∧
      ∀ P∈U,∃ Q : KPoints ℚ_[p] (distinguishedComponentObject G X a O hO m hm),
        Q≫distinguishedComponentProjection G X a O hO m hm=P :=
  distinguishedComponent_origin_open_image ℚ_[p] G X a O hO m hm

/-- The actual distinguished component also supplies an open real neighborhood of O. -/
theorem distinguishedComponent_real_origin_open_image :
    ∃ U : Set (KPoints ℝ X), IsOpen U ∧ rationalScalarPoint ℝ O∈U ∧
      ∀ P∈U,∃ Q : KPoints ℝ (distinguishedComponentObject G X a O hO m hm),
        Q≫distinguishedComponentProjection G X a O hO m hm=P :=
  distinguishedComponent_origin_open_image ℝ G X a O hO m hm

end FourCorner.ThetaLocalSurvival.StrongTopology
