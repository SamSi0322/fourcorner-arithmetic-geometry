import ThetaCoverClassPortable.ThetaCoverPointModuleComparison
import ThetaCoverClassPortable.AlgEquivZeroBaseChange
import ThetaCoverClassPortable.DBaseChangeGeometry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra
namespace FourCorner.ThetaCoverAlgEquivZero
open ThetaDGeometricModel ThetaLiteralModels
local instance : IsIntegral geometricD := geometric_integral
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth
local instance : GeometricallyIntegral (dToBase ℚ) := DRationalInputs.geometricallyIntegral
local instance : GeometricallyIntegral toBase := inferInstance
theorem geometric_algEquivZero : RelPicard.IsAlgEquivZero toBase ThetaGeometricKummerLine.L := by
  exact (PointPairTensorFamily.tensor_algEquivZero toBase ThetaActualPointPairs.actualPairs).of_iso
    ThetaCoverPointModuleComparison.actual_module_iso.some.symm

/-- Every algebraically closed field valued base change is obtained using an
actual embedding of Qbar and actual categorical pullback comparison maps. -/
theorem at_field {k : Type} [Field k] [IsAlgClosed k]
    (s : Spec (.of k) ⟶ Spec (.of ℚ)) :
    RelPicard.IsAlgEquivZero (pullback.snd (dToBase ℚ) s)
      ((Scheme.Modules.pullback (pullback.fst (dToBase ℚ) s)).obj ThetaQQKummerLine.L) := by
  let r : ℚ →+* k := (Scheme.Spec.preimage s).unop.hom
  letI : Algebra ℚ k := r.toAlgebra
  let emb : K →ₐ[ℚ] k := IsAlgClosed.lift
  let b : Spec (.of k) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom emb.toRingHom)
  have hb : b ≫ qb = s := by
    change Spec.map (CommRingCat.ofHom emb.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℚ K)) = s
    rw [← Spec.map_comp]
    have hh : (CommRingCat.ofHom (algebraMap ℚ K)) ≫ (CommRingCat.ofHom emb.toRingHom) =
        (Scheme.Spec.preimage s).unop := by
      ext x
      exact emb.commutes x
    rw [hh]
    exact Scheme.Spec.map_preimage s
  let a := pullback.snd (dToBase ℚ) s
  let e : pullback (dToBase ℚ) s ⟶ geometricD :=
    pullback.lift (pullback.fst (dToBase ℚ) s) (a ≫ b) (by
      rw [Category.assoc,hb]; exact pullback.condition)
  let j : pullback (dToBase ℚ) s ⟶ pullback toBase b :=
    pullback.lift e a (by simp only [e,pullback.lift_snd])
  have hj : j ≫ pullback.snd toBase b = a := pullback.lift_snd _ _ _
  have he : j ≫ pullback.fst toBase b ≫ ThetaGeometricKummerLine.projection =
      pullback.fst (dToBase ℚ) s := by simp only [j,e,pullback.lift_fst_assoc,pullback.lift_fst]
  have h := (AlgEquivZeroBaseChange.baseChange toBase b geometric_algEquivZero).pullback j hj
  exact h.of_iso ((Scheme.Modules.pullbackComp _ _).app ThetaGeometricKummerLine.L ≪≫
    (Scheme.Modules.pullbackComp _ _).app ThetaQQKummerLine.L ≪≫
    (Scheme.Modules.pullbackCongr he).app ThetaQQKummerLine.L)

/-- The original QQ rigidified cover line satisfies the literal all-fibre
family predicate, with no degree-zero or torsion shortcut. -/
theorem fibrewise : RelPicard.FibrewiseAlgEquivZero ThetaQQRigidifiedLine.rigidifiedLine := by
  intro k _ _ s
  let c := dToBase ℚ
  let t := 𝟙 (Spec (.of ℚ))
  let a := pullback.snd c t
  let e : pullback a s ⟶ pullback c s :=
    pullback.lift (pullback.fst a s ≫ pullback.fst c t) (pullback.snd a s) (by
      rw [Category.assoc,pullback.condition,Category.comp_id,pullback.condition])
  have he : e ≫ pullback.snd c s = RelPicard.fibreAt c t s := by
    simp only [e,RelPicard.fibreAt,pullback.lift_snd]
    rfl
  have hf : e ≫ pullback.fst c s = pullback.fst a s ≫ pullback.fst c t := by
    simp only [e,pullback.lift_fst]
  have h := (at_field s).pullback e he
  exact h.of_iso ((Scheme.Modules.pullbackComp _ _).app ThetaQQKummerLine.L ≪≫
    (Scheme.Modules.pullbackCongr hf).app ThetaQQKummerLine.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app ThetaQQKummerLine.L).symm)

theorem cut_membership :
    (RelPicard.algEquivZeroCut (dToBase ℚ) ThetaQQRigidifiedLine.origin).P
      (𝟙 (Spec (.of ℚ))) ThetaQQRigidifiedLine.rigidifiedLine := fibrewise

/-- The actual QQ class in the native relative sub-Picard presheaf cut. -/
def rationalSubPicardClass :
    (RelPicard.relSubPicPresheaf (dToBase ℚ) ThetaQQRigidifiedLine.origin
      (RelPicard.algEquivZeroCut (dToBase ℚ) ThetaQQRigidifiedLine.origin)).obj
        (Opposite.op (Over.mk (𝟙 (Spec (.of ℚ))))) :=
  ⟨Quotient.mk _ ThetaQQRigidifiedLine.rigidifiedLine,
    cut_membership⟩

#print axioms fibrewise
#print axioms cut_membership
#print axioms rationalSubPicardClass
#print axioms geometric_algEquivZero
#print axioms at_field
end FourCorner.ThetaCoverAlgEquivZero
