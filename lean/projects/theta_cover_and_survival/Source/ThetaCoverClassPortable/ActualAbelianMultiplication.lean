import Mathlib.AlgebraicGeometry.Group.Abelian
import ThetaCoverClassPortable.EtaleLocallyQuasiFinite

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj
namespace FourCorner.ThetaLocalSurvival.Multiplication

abbrev base := Spec (.of ℚ)
abbrev rationalBase := Over.mk (𝟙 base)

/-- The actual group-scheme multiplication by a natural number, as an
endomorphism in the category over Spec QQ. -/
def multiplicationOver (G : Over base) [GrpObj G] (m : ℕ) : G ⟶ G := (𝟙 G)^m

def multiplication (G : Over base) [GrpObj G] (m : ℕ) : G.left ⟶ G.left :=
  (multiplicationOver G m).left

theorem multiplication_over (G : Over base) [GrpObj G] (m : ℕ) :
    multiplication G m ≫ G.hom=G.hom := (multiplicationOver G m).w

/-- On the actual scheme functor of points, this exact morphism acts as
multiplication by m in the native group of points. -/
theorem multiplication_points (G T : Over base) [GrpObj G] (P : T ⟶ G) (m : ℕ) :
    P ≫ multiplicationOver G m=P^m := by
  rw [multiplicationOver,MonObj.comp_pow,Category.comp_id]

/-- Compatibility with arbitrary change of the test scheme. -/
theorem multiplication_points_natural (G T U : Over base) [GrpObj G]
    (f : U ⟶ T) (P : T ⟶ G) (m : ℕ) :
    f ≫ (P ≫ multiplicationOver G m)=(f ≫ P)^m := by
  rw [←Category.assoc,multiplication_points]

/-- The conventional abelian-variety assumptions imply commutativity of
the actual native group object; no commutativity flag is invented. -/
theorem abelian_variety_commutative (G : Over base) [GrpObj G]
    [IsProper G.hom] [GeometricallyIntegral G.hom] : IsCommMonObj G :=
  isCommMonObj_of_isProper_of_geometricallyIntegral G

theorem multiplication_one (G : Over base) [GrpObj G] : multiplication G 1=𝟙 G.left := by
  simp [multiplication,multiplicationOver]

/-- Properness is genuine properness of the actual multiplication
morphism, obtained from properness over QQ and separatedness of G. -/
theorem multiplication_proper (G : Over base) [GrpObj G] [IsProper G.hom] (m : ℕ) :
    IsProper (multiplication G m) := by
  haveI : IsProper (multiplication G m ≫ G.hom) := by
    simpa only [multiplication_over] using (inferInstance : IsProper G.hom)
  exact IsProper.of_comp (multiplication G m) G.hom

/-- The identity rational point is the genuine unit of the group-scheme
functor of points, written zero in the abelian-variety convention. -/
def zeroPoint (G : Over base) [GrpObj G] : base ⟶ G.left := (1 : rationalBase ⟶ G).left

theorem zeroPoint_over (G : Over base) [GrpObj G] : zeroPoint G ≫ G.hom=𝟙 base :=
  (1 : rationalBase ⟶ G).w

theorem multiplication_zeroPoint (G : Over base) [GrpObj G] (m : ℕ) :
    zeroPoint G ≫ multiplication G m=zeroPoint G := by
  change ((1 : rationalBase ⟶ G) ≫ (𝟙 G)^m).left=(1 : rationalBase ⟶ G).left
  congr 1
  rw [MonObj.comp_pow]
  simp

/-- Literal multiplication pullback from the paper. -/
def cover (G X : Over base) [GrpObj G] (a : X ⟶ G) (m : ℕ) : Scheme :=
  pullback a.left (multiplication G m)

def originLift (G X : Over base) [GrpObj G] (a : X ⟶ G)
    (O : rationalBase ⟶ X) (hO : O ≫ a=1) (m : ℕ) : base ⟶ cover G X a m :=
  pullback.lift O.left (zeroPoint G) (by
    rw [multiplication_zeroPoint]
    exact congrArg (fun f : rationalBase ⟶ G => f.left) hO)

theorem originLift_fst (G X : Over base) [GrpObj G] (a : X ⟶ G)
    (O : rationalBase ⟶ X) (hO : O ≫ a=1) (m : ℕ) :
    originLift G X a O hO m ≫ pullback.fst a.left (multiplication G m)=O.left := by
  simp [originLift]

theorem originLift_snd (G X : Over base) [GrpObj G] (a : X ⟶ G)
    (O : rationalBase ⟶ X) (hO : O ≫ a=1) (m : ℕ) :
    originLift G X a O hO m ≫ pullback.snd a.left (multiplication G m)=zeroPoint G := by
  simp [originLift]

/-- The first multiplication level is exactly the identity morphism. -/
theorem multiplication_one_finite_etale (G : Over base) [GrpObj G] :
    IsFinite (multiplication G 1) ∧ Etale (multiplication G 1) := by
  rw [multiplication_one]
  exact ⟨inferInstance,inferInstance⟩

/-- The genuine scheme-theoretic m-torsion fibre above the identity. -/
def torsionKernel (G : Over base) [GrpObj G] (m : ℕ) : Scheme :=
  pullback (multiplication G m) (zeroPoint G)

theorem torsionKernel_proper (G : Over base) [GrpObj G] [IsProper G.hom] (m : ℕ) :
    IsProper (pullback.snd (multiplication G m) (zeroPoint G)) := by
  letI := multiplication_proper G m
  infer_instance

/-- For this actual morphism, properness removes finiteness from the
remaining finite-etale goal. This is an exact reduction, not an etale proof. -/
theorem finite_etale_iff_etale (G : Over base) [GrpObj G] [IsProper G.hom] (m : ℕ) :
    (IsFinite (multiplication G m) ∧ Etale (multiplication G m)) ↔
      Etale (multiplication G m) := by
  constructor
  · exact And.right
  · intro he
    letI := he
    letI := multiplication_proper G m
    letI := etale_locallyQuasiFinite (multiplication G m)
    exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite (multiplication G m),he⟩

end FourCorner.ThetaLocalSurvival.Multiplication
