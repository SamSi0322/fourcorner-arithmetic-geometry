import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_DescentAction
import ThetaCoverClassPortable.FlatAlgebraEqualizer
import Mathlib.AlgebraicGeometry.Pullbacks

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite
universe u
namespace FourCorner.AffineDescentCoaction
variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
abbrev s : Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))
abbrev x : Spec (.of A) ⟶ Spec (.of S) := Spec.map (CommRingCat.ofHom (algebraMap S A))
abbrev B := S ⊗[R] A
abbrev iS : S →+* B R S A := algebraMap S (B R S A)
abbrev iA : A →+* B R S A := (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom
lemma x_comp_s : x S A ≫ s R S=Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [x,s,←Spec.map_comp]
  congr 1
  ext r
  exact (IsScalarTower.algebraMap_apply R S A r).symm

/-- The actual tensor-coordinate isomorphism for the action's relation scheme. -/
def q : Spec (.of (B R S A)) ⟶ pullback (x S A ≫ s R S) (s R S) :=
  (pullbackSpecIso R S A).inv ≫
    (pullbackSymmetry (s R S) (Spec.map (CommRingCat.ofHom (algebraMap R A)))).hom ≫
    (pullback.congrHom (x_comp_s R S A).symm rfl).hom
instance q_isIso : IsIso (q R S A) := by dsimp [q];infer_instance

@[reassoc (attr:=simp)] lemma q_fst : q R S A ≫ pullback.fst _ _=Spec.map (CommRingCat.ofHom (iA R S A)) := by
  simp [q,iA]
@[reassoc (attr:=simp)] lemma q_snd : q R S A ≫ pullback.snd _ _=Spec.map (CommRingCat.ofHom (iS R S A)) := by
  simp [q,iS]
  congr 1

variable (𝒜 : DescentAction (s R S) (x S A))
/-- The ACTUAL action on global coordinate rings, transported by q. -/
def delta : A →+* B R S A := (Scheme.Spec.preimage (q R S A ≫ 𝒜.act)).unop.hom
lemma spec_delta : Spec.map (CommRingCat.ofHom (delta R S A 𝒜))=q R S A ≫ 𝒜.act := by
  exact Scheme.Spec.map_preimage _

lemma delta_scalar (a:S) : delta R S A 𝒜 (algebraMap S A a)=iS R S A a := by
  have he : (CommRingCat.ofHom (algebraMap S A)) ≫ CommRingCat.ofHom (delta R S A 𝒜)=
      CommRingCat.ofHom (iS R S A) := by
    apply Spec.map_injective
    rw [Spec.map_comp,spec_delta,Category.assoc,𝒜.act_comp,q_snd]
  exact congrArg (fun f=>f.hom a) he

/-- This ring map is genuinely linear over S, not only over R. -/
def coaction : A →ₐ[S] B R S A :=
  { delta R S A 𝒜 with commutes' := delta_scalar R S A 𝒜 }

@[simp] lemma coaction_apply (a:A) : coaction R S A 𝒜 a=delta R S A 𝒜 a := rfl

/-- Coordinates on the actual triple relation scheme. -/
def q2 : Spec (.of (S ⊗[R] B R S A)) ⟶
    pullback (pullback.snd (x S A ≫ s R S) (s R S) ≫ s R S) (s R S) :=
  q R S (B R S A) ≫
    pullback.map (x S (B R S A) ≫ s R S) (s R S)
      (pullback.snd (x S A ≫ s R S) (s R S) ≫ s R S) (s R S)
      (q R S A) (𝟙 _) (𝟙 _)
      (by simp only [Category.comp_id,Category.id_comp,Category.assoc,q_snd_assoc])
      (by simp)

@[reassoc (attr:=simp)] lemma q2_fst : q2 R S A ≫ pullback.fst _ _=
    Spec.map (CommRingCat.ofHom (iA R S (B R S A))) ≫ q R S A := by
  simp [q2,Category.assoc]
@[reassoc (attr:=simp)] lemma q2_snd : q2 R S A ≫ pullback.snd _ _=
    Spec.map (CommRingCat.ofHom (iS R S (B R S A))) := by
  simp [q2,Category.assoc]

def tensorRho : B R S A →ₐ[R] S ⊗[R] B R S A :=
  Algebra.TensorProduct.map (AlgHom.id R S) ((coaction R S A 𝒜).restrictScalars R)
def tensorUnit : B R S A →ₐ[R] S ⊗[R] B R S A :=
  Algebra.TensorProduct.map (AlgHom.id R S)
    (Algebra.TensorProduct.includeRight : A →ₐ[R] B R S A)

lemma q2_actMap : q2 R S A ≫ DescentAction.actMap 𝒜.act 𝒜.act_comp=
    Spec.map (CommRingCat.ofHom (tensorRho R S A 𝒜).toRingHom) ≫ q R S A := by
  apply pullback.hom_ext
  · simp only [Category.assoc,DescentAction.actMap_fst,q2_fst_assoc,←spec_delta,q_fst,←Spec.map_comp]
    congr 1
    all_goals
      ext a
      change (1:S) ⊗ₜ[R] delta R S A 𝒜 a=tensorRho R S A 𝒜 ((1:S) ⊗ₜ[R] a)
      simp [tensorRho]
  · simp only [Category.assoc,DescentAction.actMap_snd,q2_snd,q_snd,←Spec.map_comp]
    congr 1
    all_goals
      ext s
      change s ⊗ₜ[R] (1:B R S A)=tensorRho R S A 𝒜 (s ⊗ₜ[R] (1:A))
      simp [tensorRho]

lemma q2_proj13 : q2 R S A ≫ DescentAction.proj₁₃ (s R S) (x S A)=
    Spec.map (CommRingCat.ofHom (tensorUnit R S A).toRingHom) ≫ q R S A := by
  apply pullback.hom_ext
  · simp only [Category.assoc,DescentAction.proj₁₃_fst,q2_fst_assoc,q_fst,←Spec.map_comp]
    congr 1
    all_goals
      ext a
      change (1:S) ⊗ₜ[R] ((1:S) ⊗ₜ[R] a)=tensorUnit R S A ((1:S) ⊗ₜ[R] a)
      simp [tensorUnit]
  · simp only [Category.assoc,DescentAction.proj₁₃_snd,q2_snd,q_snd,←Spec.map_comp]
    congr 1
    all_goals
      ext s
      change s ⊗ₜ[R] (1:B R S A)=tensorUnit R S A (s ⊗ₜ[R] (1:A))
      simp [tensorUnit]

lemma ring_coassoc (a:A) : tensorRho R S A 𝒜 (coaction R S A 𝒜 a)=
    tensorUnit R S A (coaction R S A 𝒜 a) := by
  have h : Spec.map (CommRingCat.ofHom (delta R S A 𝒜) ≫
      CommRingCat.ofHom (tensorRho R S A 𝒜).toRingHom)=
      Spec.map (CommRingCat.ofHom (delta R S A 𝒜) ≫
      CommRingCat.ofHom (tensorUnit R S A).toRingHom) := by
    rw [Spec.map_comp,Spec.map_comp,spec_delta]
    rw [←Category.assoc,←q2_actMap,←Category.assoc,←q2_proj13]
    simpa only [Category.assoc] using congrArg (fun f=>q2 R S A ≫ f) 𝒜.trans
  exact congrArg (fun f=>f.hom a) (Spec.map_injective h)

lemma tensorRho_eq (b:B R S A) : tensorRho R S A 𝒜 b=
    ((coaction R S A 𝒜).toLinearMap.restrictScalars R).lTensor S b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | add b c hb hc => rw [map_add,map_add,hb,hc]
  | tmul s a => simp [tensorRho]
lemma tensorUnit_eq (b:B R S A) : tensorUnit R S A b=
    (TensorProduct.mk R S A 1).lTensor S b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | add b c hb hc => rw [map_add,map_add,hb,hc]
  | tmul s a => simp [tensorUnit]

theorem coassoc (a:A) : ((coaction R S A 𝒜).toLinearMap.restrictScalars R).lTensor S
      (coaction R S A 𝒜 a)=
    (TensorProduct.mk R S A 1).lTensor S (coaction R S A 𝒜 a) := by
  rw [←tensorRho_eq,←tensorUnit_eq]
  exact ring_coassoc R S A 𝒜 a

/-- The actual multiplication map in coordinates of the diagonal. -/
def multiplication : B R S A →ₐ[S] A :=
  { (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S A)
      (AlgHom.id R A) (fun _ _=>Commute.all _ _)).toRingHom with
    commutes' := by
      intro s
      change (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S A)
        (AlgHom.id R A) (fun _ _=>Commute.all _ _)) (s ⊗ₜ[R] 1)=algebraMap S A s
      rw [Algebra.TensorProduct.lift_tmul]
      change algebraMap S A s * 1=algebraMap S A s
      exact mul_one _ }
@[simp] lemma multiplication_tmul (s:S) (a:A) : multiplication R S A (s ⊗ₜ[R] a)=s • a := by
  change algebraMap S A s * a=s • a
  exact (Algebra.smul_def s a).symm

lemma spec_multiplication_q : Spec.map (CommRingCat.ofHom (multiplication R S A).toRingHom) ≫ q R S A=
    DescentAction.unitMap (s R S) (x S A) := by
  apply pullback.hom_ext
  · simp only [Category.assoc,q_fst,DescentAction.unitMap_fst,←Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (iA R S A) ≫
      CommRingCat.ofHom (multiplication R S A).toRingHom)=𝟙 _
    have h : CommRingCat.ofHom (iA R S A) ≫
        CommRingCat.ofHom (multiplication R S A).toRingHom=𝟙 (CommRingCat.of A) := by
      ext a
      change multiplication R S A ((1:S) ⊗ₜ[R] a)=a
      rw [multiplication_tmul,one_smul]
    rw [h]
    exact Spec.map_id _
  · simp only [Category.assoc,q_snd,DescentAction.unitMap_snd,←Spec.map_comp]
    congr 1
    ext s
    change multiplication R S A ((algebraMap S S) s ⊗ₜ[R] (1:A))=algebraMap S A s
    simp only [Algebra.algebraMap_self,multiplication_tmul,Algebra.smul_def,mul_one,RingHom.id_apply]

lemma multiplication_eq_action (b:B R S A) : multiplication R S A b=
    Module.FaithfullyFlat.tensorAction (R:=R) b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | add b c hb hc => rw [map_add,map_add,hb,hc]
  | tmul s a => rw [multiplication_tmul,Module.FaithfullyFlat.tensorAction_tmul]

theorem counit (a:A) : Module.FaithfullyFlat.tensorAction (R:=R) (coaction R S A 𝒜 a)=a := by
  have h : Spec.map (CommRingCat.ofHom (delta R S A 𝒜) ≫
      CommRingCat.ofHom (multiplication R S A).toRingHom)=Spec.map (𝟙 (CommRingCat.of A)) := by
    rw [Spec.map_comp,spec_delta,←Category.assoc,spec_multiplication_q,𝒜.unit_act,Spec.map_id]
  have hh := congrArg (fun f=>f.hom a) (Spec.map_injective h)
  rw [←multiplication_eq_action]
  exact hh
end FourCorner.AffineDescentCoaction
