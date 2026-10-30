import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Algebra.Module.Projective

/-! Genuine consequences of the exact all-commutative-ring relation
hypotheses. No quotient, C→A flatness, or effectiveness is assumed here. -/
namespace FourCorner.FiniteRelationQuotient
noncomputable section
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- Precisely the source caller's ring-point relation, for every test ring. -/
def Related (s t : A →+* B) {T : Type u} [CommRing T] (x y : A →+* T) : Prop :=
  ∃φ : B →+* T,φ.comp s=x ∧ φ.comp t=y

/-- Joint generation gives uniqueness on EVERY target ring, including
nonreduced rings; no restriction to fields or geometric points occurs. -/
theorem joint_ext (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    {T : Type u} [CommRing T] (f g : B →+* T)
    (hs : f.comp s=g.comp s) (ht : f.comp t=g.comp t) : f=g := by
  have hS : s.range ≤ f.eqLocus g := by
    rintro _ ⟨a,rfl⟩
    exact RingHom.congr_fun hs a
  have hT : t.range ≤ f.eqLocus g := by
    rintro _ ⟨a,rfl⟩
    exact RingHom.congr_fun ht a
  have hall : (⊤ : Subring B) ≤ f.eqLocus g := hgen ▸ sup_le hS hT
  exact RingHom.ext fun b=>hall (Subring.mem_top b)

theorem diagonal_exists (s t : A →+* B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    ∃e : B →+* A,e.comp s=RingHom.id A ∧ e.comp t=RingHom.id A :=
  (heq A).refl (RingHom.id A)

 def diagonal (s t : A →+* B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) : B →+* A :=
  (diagonal_exists s t heq).choose
 theorem diagonal_source (s t : A →+* B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    (diagonal s t heq).comp s=RingHom.id A := (diagonal_exists s t heq).choose_spec.1
 theorem diagonal_target (s t : A →+* B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    (diagonal s t heq).comp t=RingHom.id A := (diagonal_exists s t heq).choose_spec.2

 theorem inverse_exists (s t : A →+* B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    ∃i : B →+* B,i.comp s=t ∧ i.comp t=s := by
  apply (heq B).symm
  exact ⟨RingHom.id B,rfl,rfl⟩
 def inverseMap (s t : A →+* B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) : B →+* B :=
  (inverse_exists s t heq).choose
 theorem inverse_source (s t : A →+* B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    (inverseMap s t heq).comp s=t := (inverse_exists s t heq).choose_spec.1
 theorem inverse_target (s t : A →+* B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    (inverseMap s t heq).comp t=s := (inverse_exists s t heq).choose_spec.2

 theorem inverse_involutive (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    (inverseMap s t heq).comp (inverseMap s t heq)=RingHom.id B := by
  apply joint_ext s t hgen
  · rw [RingHom.comp_assoc,inverse_source,inverse_target,RingHom.id_comp]
  · rw [RingHom.comp_assoc,inverse_target,inverse_source,RingHom.id_comp]

 def inverseEquiv (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) : B ≃+* B where
  __ := inverseMap s t heq
  invFun := inverseMap s t heq
  left_inv b := RingHom.congr_fun (inverse_involutive s t hgen heq) b
  right_inv b := RingHom.congr_fun (inverse_involutive s t hgen heq) b

#print axioms joint_ext
#print axioms diagonal_exists
#print axioms inverseEquiv
end
end FourCorner.FiniteRelationQuotient
