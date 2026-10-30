import ThetaCoverClassPortable.PairTargetLinearity
import ThetaCoverClassPortable.FiniteRelationComposition

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
namespace FourCorner.PairCoactionTransfer
open FourCorner.FiniteRelationQuotient FourCorner.RingMapTensorPushout
universe u
variable (K A D B : Type u) [CommRing K] [CommRing A] [CommRing D] [CommRing B]
variable [Algebra K A] [Algebra K D] [Algebra K B] [Algebra A D] [Algebra A B]
variable [IsScalarTower K A D] [IsScalarTower K A B]

/-- The actual coefficient map supplied by the over-D pair isomorphism. -/
def pairMap (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) : B →ₐ[K] D ⊗[K] D :=
  (e.toAlgHom.restrictScalars K).comp
    ((Algebra.TensorProduct.includeRight : B →ₐ[A] D ⊗[A] B).restrictScalars K)

@[simp] theorem pairMap_apply (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (b : B) :
    pairMap K A D B e b = e ((1 : D) ⊗ₜ[A] b) := rfl

/-- Source coordinate is forced by balancing and the over-D property. -/
theorem pairMap_source (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (a : A) :
    pairMap K A D B e (algebraMap A B a) = algebraMap A D a ⊗ₜ[K] (1 : D) := by
  rw [pairMap_apply]
  have h : ((1 : D) ⊗ₜ[A] algebraMap A B a) =
      algebraMap A D a ⊗ₜ[A] (1 : B) := by
    simpa only [Algebra.smul_def, mul_one] using
      (TensorProduct.smul_tmul (R := A) a (1 : D) (1 : B)).symm
  rw [h]
  exact e.commutes (algebraMap A D a)

abbrev tripleRing : Type u := D ⊗[K] (D ⊗[K] D)

def tripleSource : D →ₐ[K] tripleRing K D := Algebra.TensorProduct.includeLeft

def tripleTarget : D →ₐ[K] tripleRing K D :=
  (Algebra.TensorProduct.includeRight : D ⊗[K] D →ₐ[K] tripleRing K D).comp
    (Algebra.TensorProduct.includeLeft : D →ₐ[K] D ⊗[K] D)

def tripleMiddle : D →ₐ[K] tripleRing K D :=
  (Algebra.TensorProduct.includeRight : D ⊗[K] D →ₐ[K] tripleRing K D).comp
    (Algebra.TensorProduct.includeRight : D →ₐ[K] D ⊗[K] D)

/-- First arrow has (source,target)=(middle,target). -/
def leftPair : D ⊗[K] D →ₐ[K] tripleRing K D :=
  Algebra.TensorProduct.lift (tripleMiddle K D) (tripleTarget K D) (fun _ _ => Commute.all _ _)

/-- Second arrow has (source,target)=(source,middle). -/
def rightPair : D ⊗[K] D →ₐ[K] tripleRing K D :=
  Algebra.TensorProduct.lift (tripleSource K D) (tripleMiddle K D) (fun _ _ => Commute.all _ _)

/-- Composite arrow has (source,target)=(source,target), omitting middle. -/
def directPair : D ⊗[K] D →ₐ[K] tripleRing K D :=
  Algebra.TensorProduct.lift (tripleSource K D) (tripleTarget K D) (fun _ _ => Commute.all _ _)

@[simp] theorem leftPair_tmul (ds dt : D) :
    leftPair K D (ds ⊗ₜ[K] dt) = (1 : D) ⊗ₜ[K] (dt ⊗ₜ[K] ds) := by
  simp [leftPair, tripleMiddle, tripleTarget]

@[simp] theorem rightPair_tmul (ds dt : D) :
    rightPair K D (ds ⊗ₜ[K] dt) = ds ⊗ₜ[K] ((1 : D) ⊗ₜ[K] dt) := by
  simp [rightPair, tripleSource, tripleMiddle]

@[simp] theorem directPair_tmul (ds dt : D) :
    directPair K D (ds ⊗ₜ[K] dt) = ds ⊗ₜ[K] (dt ⊗ₜ[K] (1 : D)) := by
  simp [directPair, tripleSource, tripleTarget]

def leftArrow (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) : B →ₐ[K] tripleRing K D :=
  (leftPair K D).comp (pairMap K A D B e)

def rightArrow (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) : B →ₐ[K] tripleRing K D :=
  (rightPair K D).comp (pairMap K A D B e)

abbrev reversePoint (t : A →ₐ[K] B) : CommRingCat.{u} :=
  point (algebraMap A B) t.toRingHom

/-- The two actual triple-coordinate arrows agree precisely on source(first)=target(second). -/
theorem triple_balance (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (t : A →ₐ[K] B)
    (ht : ∀ a, pairMap K A D B e (t a) = (1 : D) ⊗ₜ[K] algebraMap A D a) :
    (leftArrow K A D B e).toRingHom.comp (algebraMap A B) =
      (rightArrow K A D B e).toRingHom.comp t.toRingHom := by
  ext a
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    leftArrow, rightArrow, AlgHom.comp_apply, pairMap_source, ht]
  simp [leftPair, rightPair]

/-- A genuine map out of the reverse composable pushout, built from its universal property. -/
def tripleCoordinates (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (t : A →ₐ[K] B)
    (ht : ∀ a, pairMap K A D B e (t a) = (1 : D) ⊗ₜ[K] algebraMap A D a) :
    reversePoint K A B t →+* tripleRing K D :=
  (pushout.desc (CommRingCat.ofHom (leftArrow K A D B e).toRingHom)
    (CommRingCat.ofHom (rightArrow K A D B e).toRingHom)
    (CommRingCat.hom_ext (triple_balance K A D B e t ht))).hom

@[simp] theorem tripleCoordinates_left
    (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (t : A →ₐ[K] B)
    (ht : ∀ a, pairMap K A D B e (t a) = (1 : D) ⊗ₜ[K] algebraMap A D a) (b : B) :
    tripleCoordinates K A D B e t ht ((left (algebraMap A B) t.toRingHom).hom b) =
      leftArrow K A D B e b := by
  have h : left (algebraMap A B) t.toRingHom ≫
      CommRingCat.ofHom (tripleCoordinates K A D B e t ht) =
      CommRingCat.ofHom (leftArrow K A D B e).toRingHom := by
    exact pushout.inl_desc _ _ _
  exact congrArg (fun f : CommRingCat.of B ⟶ CommRingCat.of (tripleRing K D) => f.hom b) h

@[simp] theorem tripleCoordinates_right
    (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (t : A →ₐ[K] B)
    (ht : ∀ a, pairMap K A D B e (t a) = (1 : D) ⊗ₜ[K] algebraMap A D a) (b : B) :
    tripleCoordinates K A D B e t ht ((right (algebraMap A B) t.toRingHom).hom b) =
      rightArrow K A D B e b := by
  have h : right (algebraMap A B) t.toRingHom ≫
      CommRingCat.ofHom (tripleCoordinates K A D B e t ht) =
      CommRingCat.ofHom (rightArrow K A D B e).toRingHom := by
    exact pushout.inr_desc _ _ _
  exact congrArg (fun f : CommRingCat.of B ⟶ CommRingCat.of (tripleRing K D) => f.hom b) h

/-- Triple coordinates of the actual coring coefficient map are proved from
its ORIGINAL source/target endpoints and genuine joint generation of B.
The desired pair-coaction equality is not assumed. -/
theorem tripleCoordinates_delta
    (e : D ⊗[A] B ≃ₐ[D] D ⊗[K] D) (t : A →ₐ[K] B)
    (ht : ∀ a, pairMap K A D B e (t a) = (1 : D) ⊗ₜ[K] algebraMap A D a)
    (hgen : (algebraMap A B).range ⊔ t.toRingHom.range = ⊤)
    (delta : B →+* reversePoint K A B t)
    (hs : delta.comp (algebraMap A B) =
      (right (algebraMap A B) t.toRingHom).hom.comp (algebraMap A B))
    (htt : delta.comp t.toRingHom =
      (left (algebraMap A B) t.toRingHom).hom.comp t.toRingHom) :
    (tripleCoordinates K A D B e t ht).comp delta =
      ((directPair K D).comp (pairMap K A D B e)).toRingHom := by
  apply joint_ext (algebraMap A B) t.toRingHom hgen
  · ext a
    change tripleCoordinates K A D B e t ht (delta (algebraMap A B a)) =
      directPair K D (pairMap K A D B e (algebraMap A B a))
    have ha : delta (algebraMap A B a) =
        (right (algebraMap A B) t.toRingHom).hom (algebraMap A B a) :=
      RingHom.congr_fun hs a
    rw [ha, tripleCoordinates_right]
    change rightPair K D (pairMap K A D B e (algebraMap A B a)) =
      directPair K D (pairMap K A D B e (algebraMap A B a))
    rw [pairMap_source]
    simp [rightPair, directPair]
  · ext a
    change tripleCoordinates K A D B e t ht (delta (t a)) =
      directPair K D (pairMap K A D B e (t a))
    have ha : delta (t a) = (left (algebraMap A B) t.toRingHom).hom (t a) :=
      RingHom.congr_fun htt a
    rw [ha, tripleCoordinates_left]
    change leftPair K D (pairMap K A D B e (t a)) =
      directPair K D (pairMap K A D B e (t a))
    rw [ht]
    simp [leftPair, directPair]

end FourCorner.PairCoactionTransfer
