import ThetaCoverClassPortable.ThetaQuadraticBoundaryDistinct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits

namespace FourCorner.ThetaQuadraticGeometricContacts
open ThetaQuadraticCurve ThetaQuadraticContactAlgebra ThetaQuadraticContactScheme
abbrev K := ThetaDGeometricModel.K
local instance : Algebra F K := coefficientEmbedding.toRingHom.toAlgebra

def root : K := Classical.choose (IsAlgClosed.exists_pow_nat_eq (2/99:K) (by decide : 0<2))
theorem root_sq : root^2=(2/99:K) := Classical.choose_spec
  (IsAlgClosed.exists_pow_nat_eq (2/99:K) (by decide : 0<2))
theorem root_ne_zero : root≠0 := by
  intro h
  have hh := root_sq
  rw [h,zero_pow (by decide)] at hh
  norm_num at hh

def rootValue (positive : Bool) : K := if positive then root else -root
theorem rootValue_sq (positive : Bool) : rootValue positive^2=(2/99:K) := by
  cases positive <;> simp [rootValue,root_sq]

/-- Actual F-algebra embeddings of the genuine quadratic contact field. -/
def embedding (positive : Bool) : contactField →ₐ[F] K :=
  QuadraticAlgebra.lift ⟨rootValue positive,by
    rw [←pow_two,rootValue_sq]
    simp only [Algebra.smul_def,map_zero,zero_mul,add_zero,mul_one,map_div₀,map_ofNat]⟩

@[simp] theorem embedding_ordinate (positive : Bool) : embedding positive ordinate=rootValue positive := by
  change (0:F) • (1:K)+(1:F) • rootValue positive=rootValue positive
  simp

theorem embedding_radical (positive : Bool) :
    embedding positive radical=ThetaLinesAbsoluteGalois.r := by
  exact (embedding positive).commutes QuadraticAlgebra.omega

/-- These are all embeddings over the actual coefficient embedding. -/
theorem embedding_exhaustive (φ : contactField →ₐ[F] K) :
    φ=embedding true ∨ φ=embedding false := by
  have hh : (φ ordinate)^2=root^2 := by
    rw [←map_pow,ordinate_sq,root_sq]
    simp only [map_div₀,map_ofNat]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hh with h|h
  · left
    apply QuadraticAlgebra.algHom_ext
    change φ ordinate=embedding true ordinate
    simpa only [embedding_ordinate,rootValue,if_true] using h
  · right
    apply QuadraticAlgebra.algHom_ext
    change φ ordinate=embedding false ordinate
    simpa only [embedding_ordinate,rootValue,Bool.false_eq_true,if_false] using h

def rawPoint (plus positive : Bool) : Spec (.of K) ⟶ curve :=
  Spec.map (CommRingCat.ofHom (embedding positive).toRingHom) ≫ contactMap plus

theorem rawPoint_over (plus positive : Bool) : rawPoint plus positive ≫ toBase=extensionMap := by
  rw [rawPoint,Category.assoc,contactMap_toBase]
  change Spec.map (CommRingCat.ofHom (embedding positive).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap F contactField)) =
    Spec.map (CommRingCat.ofHom coefficientEmbedding.toRingHom)
  rw [←Spec.map_comp]
  congr 1
  ext a
  exact (embedding positive).commutes a

def pointInBaseChange (plus positive : Bool) : Spec (.of K) ⟶ geometricBaseChange :=
  pullback.lift (rawPoint plus positive) (𝟙 _)
    (by simpa only [Category.id_comp] using rawPoint_over plus positive)

def point (plus positive : Bool) : Spec (.of K) ⟶ ThetaDGeometricModel.geometricD :=
  pointInBaseChange plus positive ≫ geometricBaseChangeIso.hom

theorem iso_geometricProjection : geometricBaseChangeIso.hom ≫ geometricProjection=
    pullback.fst toBase extensionMap := by
  apply pullback.hom_ext
  · simp only [Category.assoc,geometricProjection_toRational,geometricBaseChangeIso_fst]
  · simp only [Category.assoc,geometricProjection_toBase,geometricBaseChangeIso_snd_assoc]
    exact (pullback.condition (f:=toBase) (g:=extensionMap)).symm

@[reassoc (attr := simp)] theorem point_over (plus positive : Bool) :
    point plus positive ≫ ThetaDGeometricModel.toBase=𝟙 _ := by
  simp [point,pointInBaseChange,Category.assoc]

/-- Equality of the actual geometric point with the actual base-changed
closed quadratic contact diagram. -/
@[reassoc (attr := simp)] theorem point_toQuadratic (plus positive : Bool) :
    point plus positive ≫ geometricProjection=rawPoint plus positive := by
  simp [point,Category.assoc,iso_geometricProjection,pointInBaseChange]

theorem point_toOriginal (plus positive : Bool) :
    point plus positive ≫ pullback.fst (ThetaLiteralModels.dToBase ℚ) ThetaDGeometricModel.qb=
      Spec.map (CommRingCat.ofHom (embedding positive).toRingHom) ≫ rationalChartPoint plus := by
  have h := congrArg (fun f => f ≫ toRational) (point_toQuadratic plus positive)
  simpa only [Category.assoc,geometricProjection_toRational,rawPoint,contactMap_toRational] using h

/-- The two geometric points are proved distinct from their residue-field
embeddings. Their closed F-point is not asserted rational. -/
theorem points_distinct (plus : Bool) : point plus true≠point plus false := by
  intro h
  have hh := congrArg (fun f => f ≫ geometricProjection) h
  rw [point_toQuadratic,point_toQuadratic] at hh
  letI := contactMap_closedImmersion plus
  have hs := (cancel_mono (contactMap plus)).mp hh
  have hr := Spec.map_injective hs
  have he := congrArg (fun f : CommRingCat.of contactField ⟶ .of K => f.hom ordinate) hr
  change embedding true ordinate=embedding false ordinate at he
  simp only [embedding_ordinate,rootValue,Bool.false_eq_true,if_false,if_true] at he
  have hz : (2:K)*root=0 := by linear_combination he
  exact mul_ne_zero (by norm_num) root_ne_zero hz

end FourCorner.ThetaQuadraticGeometricContacts
