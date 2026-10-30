import Slot02HighRatios
import geometry.ProjectiveLocalization

noncomputable section
open AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace FourCorner.CriticalAmbientChart
universe u
variable (K : Type u) [Field K]
abbrev ambient := MvPolynomial (Fin 4) K
abbrev affineAmbient := MvPolynomial (Fin 3) K
abbrev grading := homogeneousSubmodule (Fin 4) K

def insert (j : Fin 4) : Fin 3 → Fin 4
  | a => ![![1,2,3],![0,2,3],![0,1,3],![0,1,2]] j a
def drop (j : Fin 4) : Fin 4 → Fin 3
  | a => ![![0,0,1,2],![0,0,1,2],![0,1,0,2],![0,1,2,0]] j a
lemma insert_ne (j : Fin 4) (a : Fin 3) : insert j a≠j := by
  fin_cases j <;> fin_cases a <;> decide
lemma drop_insert (j : Fin 4) (a : Fin 3) : drop j (insert j a)=a := by
  fin_cases j <;> fin_cases a <;> rfl
lemma insert_drop (j a : Fin 4) (ha : a≠j) : insert j (drop j a)=a := by
  fin_cases j <;> fin_cases a <;> first | rfl | exact (ha rfl).elim

def dehom (j : Fin 4) : ambient K →+* affineAmbient K :=
  eval₂Hom C (fun a => if a=j then 1 else X (drop j a))
abbrev ambientAway (j : Fin 4) := Away (grading K) (X j)

def ambientDehom (j : Fin 4) : ambientAway K j →+* affineAmbient K :=
  (IsLocalization.Away.lift (S:=Localization.Away (X j : ambient K)) (X j) (g:=dehom K j)
    (by simpa [dehom] using (isUnit_one : IsUnit (1:affineAmbient K)))).comp (algebraMap _ _)

lemma ambientDehom_mk (j : Fin 4) (d : ℕ) (p : ambient K)
    (hp : p∈grading K (d • 1)) :
    ambientDehom K j (Away.mk (grading K) (Slot02HighProjSpace.X_mem_one K 3 j) d p hp)=dehom K j p := by
  let l : Localization.Away (X j : ambient K) →+* affineAmbient K :=
    IsLocalization.Away.lift (X j) (g:=dehom K j) (by simpa [dehom] using (isUnit_one : IsUnit (1:affineAmbient K)))
  have h : l (Localization.mk p ⟨X j^d,⟨d,rfl⟩⟩)*
      l (algebraMap (ambient K) (Localization.Away (X j : ambient K)) (X j^d))=l (algebraMap _ _ p) := by
    rw [←map_mul,Localization.mk_eq_mk',IsLocalization.mk'_spec]
  simpa [ambientDehom,l,IsLocalization.Away.lift_eq,dehom] using h

lemma ambientDehom_ratio (j a : Fin 4) :
    ambientDehom K j (Slot02HighProjSpace.ratio K 3 j a)=dehom K j (X a) :=
  ambientDehom_mk K j 1 _ _

def ambientInverse (j : Fin 4) : affineAmbient K →+* ambientAway K j :=
  eval₂Hom (algebraMap K _) (fun a => Slot02HighProjSpace.ratio K 3 j (insert j a))

lemma ambientDehom_inverse (j : Fin 4) :
    (ambientDehom K j).comp (ambientInverse K j)=RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply,ambientInverse,coe_eval₂Hom,eval₂_C,RingHom.id_apply]
    change ambientDehom K j (Away.mk (grading K) (Slot02HighProjSpace.X_mem_one K 3 j) 0 (C a) _)=C a
    rw [ambientDehom_mk]
    simp [dehom]
  · intro a
    simp only [RingHom.comp_apply,ambientInverse,coe_eval₂Hom,eval₂_X,RingHom.id_apply,ambientDehom_ratio]
    simp only [dehom,coe_eval₂Hom,eval₂_X,if_neg (insert_ne j a),drop_insert]

lemma ambientInverse_dehom_ratio (j a : Fin 4) :
    ambientInverse K j (ambientDehom K j (Slot02HighProjSpace.ratio K 3 j a))=Slot02HighProjSpace.ratio K 3 j a := by
  rw [ambientDehom_ratio]
  by_cases ha : a=j
  · subst a
    simp [dehom,Slot02HighProjSpace.ratio_self]
  · simp only [dehom,coe_eval₂Hom,eval₂_X,if_neg ha,ambientInverse,insert_drop j a ha]

lemma ambientInverse_dehom (j : Fin 4) :
    (ambientInverse K j).comp (ambientDehom K j)=RingHom.id _ := by
  apply RingHom.ext
  intro z
  change ambientInverse K j (ambientDehom K j z)=z
  have hz : z∈Algebra.adjoin K (Set.range (Slot02HighProjSpace.ratio K 3 j)) := by
    rw [Slot02HighProjSpace.adjoin_range_ratio];trivial
  induction hz using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨a,rfl⟩:=hx; exact ambientInverse_dehom_ratio K j a
  | algebraMap a =>
    have h : ambientDehom K j (algebraMap K _ a)=C a := by
      change ambientDehom K j (Away.mk (grading K) (Slot02HighProjSpace.X_mem_one K 3 j) 0 (C a) _)=C a
      rw [ambientDehom_mk];simp [dehom]
    rw [h]
    simp [ambientInverse]
  | add x y hx hy hxe hye => simpa only [map_add] using congrArg₂ (·+·) hxe hye
  | mul x y hx hy hxe hye => simpa only [map_mul] using congrArg₂ (·*·) hxe hye

def ambientEquiv (j : Fin 4) : ambientAway K j ≃+* affineAmbient K :=
  RingEquiv.ofRingHom (ambientDehom K j) (ambientInverse K j)
    (ambientDehom_inverse K j) (ambientInverse_dehom K j)
end FourCorner.CriticalAmbientChart
#print axioms FourCorner.CriticalAmbientChart.ambientEquiv
