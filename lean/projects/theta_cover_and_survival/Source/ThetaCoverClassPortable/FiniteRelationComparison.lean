import ThetaCoverClassPortable.FiniteRelationStructure

namespace FourCorner.FiniteRelationQuotient
noncomputable section
open scoped TensorProduct
universe u
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A]

/-- Exact transport from the source caller's arbitrary embedded invariant
ring C to the literal standard RingHom equalizer. -/
def invariantRingEquiv (s t : A →+* B) (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀a : A,s a=t a ↔ a∈Set.range (algebraMap C A)) : C ≃+* s.eqLocus t := by
  let f : C →+* s.eqLocus t := (algebraMap C A).codRestrict (s.eqLocus t)
    (fun c=>(hinv _).mpr ⟨c,rfl⟩)
  apply RingEquiv.ofBijective f
  constructor
  · intro c d h
    exact hinj (congrArg Subtype.val h)
  · intro a
    obtain ⟨c,hc⟩ := (hinv a.val).mp a.property
    exact ⟨c,Subtype.ext hc⟩

abbrev relationAlgebra (s : A →+* B) : Algebra C B := (s.comp (algebraMap C A)).toAlgebra

 def sourceAlg (s : A →+* B) : letI := relationAlgebra (C:=C) s;A →ₐ[C] B := by
  letI := relationAlgebra (C:=C) s
  exact {s with commutes':=fun _=>rfl}
 def targetAlg (s t : A →+* B)
    (hinv : ∀a : A,s a=t a ↔ a∈Set.range (algebraMap C A)) :
    letI := relationAlgebra (C:=C) s;A →ₐ[C] B := by
  letI := relationAlgebra (C:=C) s
  exact {t with commutes':=fun c=>((hinv _).mpr ⟨c,rfl⟩).symm}

/-- The ACTUAL canonical comparison A⊗C A→B. Its injectivity is NOT assumed
or asserted here; proving it remains part of the missing quotient theorem. -/
def canonicalComparison (s t : A →+* B)
    (hinv : ∀a : A,s a=t a ↔ a∈Set.range (algebraMap C A)) : letI := relationAlgebra (C:=C) s;A ⊗[C] A →ₐ[C] B := by
  letI := relationAlgebra (C:=C) s
  exact Algebra.TensorProduct.lift (sourceAlg (C:=C) s) (targetAlg s t hinv) (fun _ _=>Commute.all _ _)

 theorem comparison_left (s t : A →+* B)
    (hinv : ∀a : A,s a=t a ↔ a∈Set.range (algebraMap C A)) (a : A) :
    canonicalComparison s t hinv (a ⊗ₜ[C] 1)=s a := by
  letI := relationAlgebra (C:=C) s
  rw [canonicalComparison,Algebra.TensorProduct.lift_tmul]
  change s a*t 1=s a
  rw [map_one,mul_one]
 theorem comparison_right (s t : A →+* B)
    (hinv : ∀a : A,s a=t a ↔ a∈Set.range (algebraMap C A)) (a : A) :
    canonicalComparison s t hinv (1 ⊗ₜ[C] a)=t a := by
  letI := relationAlgebra (C:=C) s
  rw [canonicalComparison,Algebra.TensorProduct.lift_tmul]
  change s 1*t a=t a
  rw [map_one,one_mul]

/-- The original joint-generation hypothesis proves genuine surjectivity
of the comparison ring map; this is not a claimed effective quotient. -/
theorem canonicalComparison_surjective (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (hinv : ∀a : A,s a=t a ↔ a∈Set.range (algebraMap C A)) :
    Function.Surjective (canonicalComparison s t hinv) := by
  letI := relationAlgebra (C:=C) s
  let f := (canonicalComparison s t hinv).toRingHom
  have hs : s.range ≤ f.range := by
    rintro _ ⟨a,rfl⟩
    exact ⟨a ⊗ₜ[C] 1,comparison_left s t hinv a⟩
  have ht : t.range ≤ f.range := by
    rintro _ ⟨a,rfl⟩
    exact ⟨1 ⊗ₜ[C] a,comparison_right s t hinv a⟩
  have hall : (⊤ : Subring B) ≤ f.range := hgen ▸ sup_le hs ht
  intro b
  exact hall (Subring.mem_top b)

#print axioms invariantRingEquiv
#print axioms canonicalComparison
#print axioms canonicalComparison_surjective
end
end FourCorner.FiniteRelationQuotient
