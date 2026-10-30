import ThetaCoverClassPortable.FiniteRelationFaithfullyFlat
import ThetaCoverClassPortable.ProjectiveNormVanishing
import ThetaCoverClassPortable.ProjectiveNormBaseChange

namespace FourCorner.FiniteRelationQuotient
noncomputable section
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- A ring retraction is an ACTUAL algebra augmentation for the given
source algebra structure, without adding any quotient-flatness premise. -/
def augmentation (s : A →+* B) (e : B →+* A) (he : e.comp s=RingHom.id A) :
    letI := s.toAlgebra;B →ₐ[A] A := by
  letI := s.toAlgebra
  exact {e with commutes':=fun a=>RingHom.congr_fun he a}

/-- True finite-projective algebra norm vanishing at the kernel of an
actual augmentation. No global freeness or reducedness is assumed. -/
theorem norm_zero_of_augmentation (s : A →+* B) (e : B →+* A) (he : e.comp s=RingHom.id A)
    (hfinite : letI := s.toAlgebra;Module.Finite A B)
    (hproj : letI := s.toAlgebra;Module.Projective A B) (b : B) (hb : e b=0) :
    letI := s.toAlgebra
    letI : Module.Finite A B := hfinite
    letI : Module.Projective A B := hproj
    ProjectiveStabilizedDeterminant.norm A B (LinearMap.mulLeft A b)=0 := by
  letI := s.toAlgebra
  letI : Module.Finite A B := hfinite
  letI : Module.Projective A B := hproj
  let l := (augmentation s e he).toLinearMap
  apply ProjectiveStabilizedDeterminant.norm_zero_of_left_annihilator _ l 1
  · exact e.map_one
  · apply LinearMap.ext
    intro x
    change e (b*x)=0
    rw [map_mul,hb,zero_mul]

/-- The original relation already supplies a genuine norm annihilator
for EVERY t(a)-s(a), including nilpotent collisions. This does not assert
that all polynomial norm coefficients lie in C or that C→A is flat. -/
theorem relation_difference_norm_zero (s t : A →+* B)
    (hfinite : letI := s.toAlgebra;Module.Finite A B)
    (hproj : letI := s.toAlgebra;Module.Projective A B)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) (a : A) :
    letI := s.toAlgebra
    letI : Module.Finite A B := hfinite
    letI : Module.Projective A B := hproj
    ProjectiveStabilizedDeterminant.norm A B (LinearMap.mulLeft A (t a-s a))=0 := by
  apply norm_zero_of_augmentation s (diagonal s t heq) (diagonal_source s t heq) hfinite hproj
  rw [map_sub]
  have hs := RingHom.congr_fun (diagonal_source s t heq) a
  have ht := RingHom.congr_fun (diagonal_target s t heq) a
  exact sub_eq_zero.mpr (ht.trans hs.symm)

#print axioms augmentation
#print axioms norm_zero_of_augmentation
#print axioms relation_difference_norm_zero
end
end FourCorner.FiniteRelationQuotient
