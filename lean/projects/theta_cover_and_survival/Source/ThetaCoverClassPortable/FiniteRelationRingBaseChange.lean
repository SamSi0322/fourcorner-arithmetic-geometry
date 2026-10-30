import ThetaCoverClassPortable.TensorRingPoints
import ThetaCoverClassPortable.FiniteRelationStructure

namespace FourCorner.FiniteRelationRingBaseChange
open FourCorner.FiniteRelationQuotient FourCorner.TensorRingPoints
noncomputable section
open scoped TensorProduct
universe u
variable {C A B S : Type u} [CommRing C] [CommRing A] [CommRing B] [CommRing S]
variable [Algebra C A] [Algebra C B] [Algebra C S]

 def changeMap (f : A →ₐ[C] B) : S ⊗[C] A →ₐ[S] S ⊗[C] B :=
  Algebra.TensorProduct.map (AlgHom.id S S) f

 theorem changeMap_scalar (f : A →ₐ[C] B) :
    (changeMap (S:=S) f).toRingHom.comp scalarLeg=scalarLeg := by
  apply RingHom.ext
  intro s
  change s ⊗ₜ[C] f 1=s ⊗ₜ[C] (1 : B)
  rw [map_one]

 theorem changeMap_variable (f : A →ₐ[C] B) :
    (changeMap (S:=S) f).toRingHom.comp variableLeg=variableLeg.comp f.toRingHom := by
  apply RingHom.ext
  intro a
  rfl

/-- Original all-ring relation after TRUE arbitrary scalar extension:
related tensor ring points are exactly same scalar map plus original
related restrictions. No flatness/reducedness restriction on S or T. -/
theorem related_change_iff (s t : A →ₐ[C] B) {T : Type u} [CommRing T]
    (x y : S ⊗[C] A →+* T) :
    Related (changeMap (S:=S) s).toRingHom (changeMap (S:=S) t).toRingHom x y ↔
      x.comp scalarLeg=y.comp scalarLeg ∧
      Related s.toRingHom t.toRingHom (x.comp variableLeg) (y.comp variableLeg) := by
  constructor
  · rintro ⟨φ,hφs,hφt⟩
    constructor
    · rw [← hφs,← hφt,RingHom.comp_assoc,RingHom.comp_assoc,changeMap_scalar,changeMap_scalar]
    · refine ⟨φ.comp variableLeg,?_,?_⟩
      · rw [RingHom.comp_assoc,← changeMap_variable,← RingHom.comp_assoc,hφs]
      · rw [RingHom.comp_assoc,← changeMap_variable,← RingHom.comp_assoc,hφt]
  · rintro ⟨hscalar,ψ,hψs,hψt⟩
    have hc : (x.comp scalarLeg).comp (algebraMap C S)=ψ.comp (algebraMap C B) := by
      rw [RingHom.comp_assoc,legs_compatible,← RingHom.comp_assoc,← hψs,RingHom.comp_assoc]
      have hs : s.toRingHom.comp (algebraMap C A)=algebraMap C B := s.comp_algebraMap
      rw [hs]
    obtain ⟨φ,hφS,hφB⟩ := hom_lift (x.comp scalarLeg) ψ hc
    refine ⟨φ,?_,?_⟩
    · apply hom_ext
      · rw [RingHom.comp_assoc,changeMap_scalar,hφS]
      · rw [RingHom.comp_assoc,changeMap_variable,← RingHom.comp_assoc,hφB,hψs]
    · apply hom_ext
      · rw [RingHom.comp_assoc,changeMap_scalar,hφS,hscalar]
      · rw [RingHom.comp_assoc,changeMap_variable,← RingHom.comp_assoc,hφB,hψt]

/-- The ACTUAL base-changed relation is an equivalence on EVERY
commutative test ring. This is proved, not imported as a new fibre premise. -/
theorem equivalence_change (s t : A →ₐ[C] B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T)))
    (T : Type u) [CommRing T] :
    Equivalence (Related (changeMap (S:=S) s).toRingHom (changeMap (S:=S) t).toRingHom (T:=T)) := by
  constructor
  · intro x
    exact (related_change_iff s t x x).mpr ⟨rfl,(heq T).refl _⟩
  · intro x y hxy
    obtain ⟨hs,hr⟩ := (related_change_iff s t x y).mp hxy
    exact (related_change_iff s t y x).mpr ⟨hs.symm,(heq T).symm hr⟩
  · intro x y z hxy hyz
    obtain ⟨hs,hr⟩ := (related_change_iff s t x y).mp hxy
    obtain ⟨hs',hr'⟩ := (related_change_iff s t y z).mp hyz
    exact (related_change_iff s t x z).mpr ⟨hs.trans hs',(heq T).trans hr hr'⟩

/-- Joint generation is also preserved on the ACTUAL tensor ring,
including arbitrary nonflat scalar extensions. -/
theorem joint_generation_change (s t : A →ₐ[C] B)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤) :
    (changeMap (S:=S) s).toRingHom.range ⊔ (changeMap (S:=S) t).toRingHom.range=⊤ := by
  let E := (changeMap (S:=S) s).toRingHom.range ⊔ (changeMap (S:=S) t).toRingHom.range
  have hl (k : S) : (scalarLeg (R:=C) (S:=S) (A:=B)) k∈E := by
    apply (le_sup_left : (changeMap (S:=S) s).toRingHom.range≤E)
    exact ⟨scalarLeg k,RingHom.congr_fun (changeMap_scalar s) k⟩
  have hs : s.toRingHom.range≤E.comap (variableLeg (R:=C) (S:=S) (A:=B)) := by
    rintro _ ⟨a,rfl⟩
    apply (le_sup_left : (changeMap (S:=S) s).toRingHom.range≤E)
    exact ⟨variableLeg a,RingHom.congr_fun (changeMap_variable s) a⟩
  have ht : t.toRingHom.range≤E.comap (variableLeg (R:=C) (S:=S) (A:=B)) := by
    rintro _ ⟨a,rfl⟩
    apply (le_sup_right : (changeMap (S:=S) t).toRingHom.range≤E)
    exact ⟨variableLeg a,RingHom.congr_fun (changeMap_variable t) a⟩
  have hb (b : B) : (variableLeg (R:=C) (S:=S) (A:=B)) b∈E :=
    (hgen ▸ sup_le hs ht) (Subring.mem_top b)
  have hall (z : S ⊗[C] B) : z∈E := by
    induction z using TensorProduct.induction_on with
    | zero => exact E.zero_mem
    | tmul k b =>
        have h : k ⊗ₜ[C] b=(scalarLeg (R:=C) (S:=S) (A:=B)) k*variableLeg b := by simp [scalarLeg,variableLeg]
        rw [h]
        exact E.mul_mem (hl k) (hb b)
    | add x y hx hy => exact E.add_mem hx hy
  exact eq_top_iff.mpr (fun z _=>hall z)

#print axioms joint_generation_change

#print axioms related_change_iff
#print axioms equivalence_change
end
end FourCorner.FiniteRelationRingBaseChange
