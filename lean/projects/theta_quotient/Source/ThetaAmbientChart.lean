import Slot02HighRatios
import Mathlib.Logic.Equiv.Fin.Basic
import geometry.ProjectiveLocalization

noncomputable section
open AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace FourCorner.ThetaAmbientChart
universe u
variable (K : Type u) [Field K]
variable (n : ℕ) [NeZero n]
abbrev ambient := MvPolynomial (Fin (n+1)) K
abbrev affineAmbient := MvPolynomial (Fin n) K
abbrev grading := homogeneousSubmodule (Fin (n+1)) K

def insert (j : Fin (n+1)) : Fin n → Fin (n+1) := j.succAbove
def drop (j : Fin (n+1)) (a : Fin (n+1)) : Fin n :=
  if ha : a≠j then (finSuccAboveEquiv j).symm ⟨a,ha⟩ else 0
lemma insert_ne (j : Fin (n+1)) (a : Fin n) : insert n j a≠j := Fin.succAbove_ne _ _
lemma drop_insert (j : Fin (n+1)) (a : Fin n) : drop n j (insert n j a)=a := by
  unfold drop
  rw [dif_pos (insert_ne n j a)]
  exact (finSuccAboveEquiv j).symm_apply_apply a
lemma insert_drop (j a : Fin (n+1)) (ha : a≠j) : insert n j (drop n j a)=a := by
  unfold drop
  rw [dif_pos ha]
  exact congrArg Subtype.val ((finSuccAboveEquiv j).apply_symm_apply ⟨a,ha⟩)

def dehom (j : Fin (n+1)) : ambient K n →+* affineAmbient K n :=
  eval₂Hom C (fun a => if a=j then 1 else X (drop n j a))
abbrev ambientAway (j : Fin (n+1)) := Away (grading K n) (X j)

def ambientDehom (j : Fin (n+1)) : ambientAway K n j →+* affineAmbient K n :=
  (IsLocalization.Away.lift (S:=Localization.Away (X j : ambient K n)) (X j) (g:=dehom K n j)
    (by simpa [dehom] using (isUnit_one : IsUnit (1:affineAmbient K n)))).comp (algebraMap _ _)

lemma ambientDehom_mk (j : Fin (n+1)) (d : ℕ) (p : ambient K n)
    (hp : p∈grading K n (d • 1)) :
    ambientDehom K n j (Away.mk (grading K n) (Slot02HighProjSpace.X_mem_one K n j) d p hp)=dehom K n j p := by
  let l : Localization.Away (X j : ambient K n) →+* affineAmbient K n :=
    IsLocalization.Away.lift (X j) (g:=dehom K n j) (by simpa [dehom] using (isUnit_one : IsUnit (1:affineAmbient K n)))
  have h : l (Localization.mk p ⟨X j^d,⟨d,rfl⟩⟩)*
      l (algebraMap (ambient K n) (Localization.Away (X j : ambient K n)) (X j^d))=l (algebraMap _ _ p) := by
    rw [←map_mul,Localization.mk_eq_mk',IsLocalization.mk'_spec]
  simpa [ambientDehom,l,IsLocalization.Away.lift_eq,dehom] using h

lemma ambientDehom_ratio (j a : Fin (n+1)) :
    ambientDehom K n j (Slot02HighProjSpace.ratio K n j a)=dehom K n j (X a) :=
  ambientDehom_mk K n j 1 _ _

def ambientInverse (j : Fin (n+1)) : affineAmbient K n →+* ambientAway K n j :=
  eval₂Hom (algebraMap K _) (fun a => Slot02HighProjSpace.ratio K n j (insert n j a))

lemma ambientDehom_inverse (j : Fin (n+1)) :
    (ambientDehom K n j).comp (ambientInverse K n j)=RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,ambientInverse,coe_eval₂Hom,eval₂_C,RingHom.id_apply]
    change ambientDehom K n j (Away.mk (grading K n) (Slot02HighProjSpace.X_mem_one K n j) 0 (C a) _)=C a
    rw [ambientDehom_mk]
    simp [dehom]
  · intro a
    simp only [RingHom.comp_apply,ambientInverse,coe_eval₂Hom,eval₂_X,RingHom.id_apply,ambientDehom_ratio]
    simp only [dehom,coe_eval₂Hom,eval₂_X,if_neg (insert_ne n j a),drop_insert]

lemma ambientInverse_dehom_ratio (j a : Fin (n+1)) :
    ambientInverse K n j (ambientDehom K n j (Slot02HighProjSpace.ratio K n j a))=Slot02HighProjSpace.ratio K n j a := by
  rw [ambientDehom_ratio]
  by_cases ha : a=j
  · subst a
    simp [dehom,Slot02HighProjSpace.ratio_self]
  · simp only [dehom,coe_eval₂Hom,eval₂_X,if_neg ha,ambientInverse,insert_drop n j a ha]

lemma ambientInverse_dehom (j : Fin (n+1)) :
    (ambientInverse K n j).comp (ambientDehom K n j)=RingHom.id _ := by
  apply RingHom.ext
  intro z
  change ambientInverse K n j (ambientDehom K n j z)=z
  have hz : z∈Algebra.adjoin K (Set.range (Slot02HighProjSpace.ratio K n j)) := by
    rw [Slot02HighProjSpace.adjoin_range_ratio];trivial
  induction hz using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨a,rfl⟩:=hx; exact ambientInverse_dehom_ratio K n j a
  | algebraMap a =>
    have h : ambientDehom K n j (algebraMap K _ a)=C a := by
      change ambientDehom K n j (Away.mk (grading K n) (Slot02HighProjSpace.X_mem_one K n j) 0 (C a) _)=C a
      rw [ambientDehom_mk];simp [dehom]
    rw [h]
    simp [ambientInverse]
  | add x y hx hy hxe hye => simpa only [map_add] using congrArg₂ (·+·) hxe hye
  | mul x y hx hy hxe hye => simpa only [map_mul] using congrArg₂ (·*·) hxe hye

def ambientEquiv (j : Fin (n+1)) : ambientAway K n j ≃+* affineAmbient K n :=
  RingEquiv.ofRingHom (ambientDehom K n j) (ambientInverse K n j)
    (ambientDehom_inverse K n j) (ambientInverse_dehom K n j)
end FourCorner.ThetaAmbientChart
#print axioms FourCorner.ThetaAmbientChart.ambientEquiv
