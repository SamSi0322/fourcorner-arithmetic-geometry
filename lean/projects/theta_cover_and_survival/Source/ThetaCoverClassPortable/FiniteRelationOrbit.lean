import ThetaCoverClassPortable.RingMapTensorPushout
import ThetaCoverClassPortable.FiniteRelationComposition

namespace FourCorner.FiniteRelationOrbit
open CategoryTheory CategoryTheory.Limits FourCorner.FiniteRelationQuotient
noncomputable section
open scoped TensorProduct
universe u
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

abbrev orbit (s : A →ₐ[K] B) (x : A →ₐ[K] K) : CommRingCat.{u} :=
  RingMapTensorPushout.point x.toRingHom s.toRingHom
abbrev orbitLeft (s : A →ₐ[K] B) (x : A →ₐ[K] K) : K →+* orbit s x :=
  (RingMapTensorPushout.left x.toRingHom s.toRingHom).hom
abbrev orbitArrow (s : A →ₐ[K] B) (x : A →ₐ[K] K) : B →+* orbit s x :=
  (RingMapTensorPushout.right x.toRingHom s.toRingHom).hom
abbrev orbitAlgebra (s : A →ₐ[K] B) (x : A →ₐ[K] K) : Algebra K (orbit s x) :=
  RingMapTensorPushout.pointAlgebra x.toRingHom s.toRingHom

 theorem orbit_source (s : A →ₐ[K] B) (x : A →ₐ[K] K) (a : A) :
    orbitArrow s x (s a)=orbitLeft s x (x a) := by
  exact (congrArg (fun f : CommRingCat.of A ⟶ orbit s x=>f.hom a)
    (pushout.condition (f:=CommRingCat.ofHom x.toRingHom) (g:=CommRingCat.ofHom s.toRingHom))).symm

 def orbitTarget (s t : A →ₐ[K] B) (x : A →ₐ[K] K) :
    letI := orbitAlgebra s x;A →ₐ[K] orbit s x := by
  letI := orbitAlgebra s x
  refine { (orbitArrow s x).comp t.toRingHom with commutes':=?_ }
  intro k
  change orbitArrow s x (t (algebraMap K A k))=orbitLeft s x k
  rw [t.commutes,← s.commutes,orbit_source,x.commutes]
  rfl

/-- Actual source fibre B_x and its original target map: joint generation
makes this target a SCHEME-THEORETIC closed orbit (a surjective ring map),
not merely a set of field points. No reducedness or effectivity premise. -/
theorem orbitTarget_surjective (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (hgen : s.toRingHom.range ⊔ t.toRingHom.range=⊤) :
    Function.Surjective (orbitTarget s t x) := by
  letI := orbitAlgebra s x
  let E := (orbitTarget s t x).toRingHom.range
  have hl (k : K) : orbitLeft s x k∈E :=
    ⟨algebraMap K A k,(orbitTarget s t x).commutes k⟩
  have hs : s.toRingHom.range≤E.comap (orbitArrow s x) := by
    rintro _ ⟨a,rfl⟩
    change orbitArrow s x (s a)∈E
    rw [orbit_source]
    exact hl _
  have ht : t.toRingHom.range≤E.comap (orbitArrow s x) := by
    rintro _ ⟨a,rfl⟩
    exact ⟨a,rfl⟩
  have hb (b : B) : orbitArrow s x b∈E :=
    (hgen ▸ sup_le hs ht) (Subring.mem_top b)
  intro d
  letI := x.toRingHom.toAlgebra
  letI := s.toRingHom.toAlgebra
  obtain ⟨z,rfl⟩ := (RingMapTensorPushout.tensorEquiv x.toRingHom s.toRingHom).surjective d
  change RingMapTensorPushout.tensorEquiv x.toRingHom s.toRingHom z∈E
  induction z using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using E.zero_mem
  | tmul k b =>
      rw [RingMapTensorPushout.tensorEquiv_tmul]
      exact E.mul_mem (hl k) (hb b)
  | add y z hy hz =>
      rw [map_add]
      exact E.add_mem hy hz

/-- The actual diagonal gives an augmentation of the actual orbit fibre,
so the orbit is nonzero whenever the base is. -/
def orbitAugmentation (s t : A →ₐ[K] B) (x : A →ₐ[K] K)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s.toRingHom t.toRingHom (T:=T))) :
    orbit s x →+* K := by
  let e := x.toRingHom.comp (diagonal s.toRingHom t.toRingHom heq)
  have hc : CommRingCat.ofHom x.toRingHom ≫ CommRingCat.ofHom (RingHom.id K)=
      CommRingCat.ofHom s.toRingHom ≫ CommRingCat.ofHom e := by
    apply CommRingCat.hom_ext
    change x.toRingHom=e.comp s.toRingHom
    dsimp only [e]
    rw [RingHom.comp_assoc,diagonal_source,RingHom.comp_id]
  exact (pushout.desc (CommRingCat.ofHom (RingHom.id K)) (CommRingCat.ofHom e) hc).hom

abbrev orbitTargetHom (s t : A →ₐ[K] B) (x : A →ₐ[K] K) : A →+* orbit s x :=
  (orbitArrow s x).comp t.toRingHom

#print axioms orbitTarget_surjective
#print axioms orbitAugmentation
end
end FourCorner.FiniteRelationOrbit
