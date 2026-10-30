import ThetaCoverClassPortable.geometry.MultiquadraticTower
import ThetaCoverClassPortable.geometry.AdjoinRootInjective
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Localization.FractionRing

/-!
# A genuine coordinate algebra for the three-radical field

The ring is obtained by successively quotienting polynomial rings by the three
literal monic equations. The maps into the constructed field send each new
coordinate to its corresponding square root.
-/

noncomputable section

namespace FourCorner.Multiquadratic.GeneratedFractionField

variable (R F A E : Type*) [CommRing R] [Field F] [CommRing A] [Field E]
  [Algebra R F] [IsFractionRing R F] [Algebra R A]
  [Algebra R E] [Algebra F E] [Algebra A E]
  [IsScalarTower R F E] [IsScalarTower R A E] [FaithfulSMul A E]

include R

/-- An embedded algebra whose image generates E over Frac(R) has fraction field E.
No finiteness or integrality assumption is needed. -/
theorem of_adjoin_image_eq_top
    (hgen : Algebra.adjoin F (Set.range (algebraMap A E)) = ⊤) : IsFractionRing A E := by
  let S : Subfield E := Subfield.closure (algebraMap A E).range
  have hR (r : R) : algebraMap R E r ∈ S := by
    apply Subfield.subset_closure
    exact ⟨algebraMap R A r, (IsScalarTower.algebraMap_apply R A E r).symm⟩
  have hF (f : F) : algebraMap F E f ∈ S := by
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective R f
    simpa only [map_div₀, ← IsScalarTower.algebraMap_apply R F E] using
      S.div_mem (hR x) (hR y)
  let J : IntermediateField F E := S.toIntermediateField hF
  have hJ : J = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le
    exact Subfield.subset_closure
  apply IsFractionRing.of_field
  intro z
  have hz : z ∈ S := by
    change z ∈ J
    rw [hJ]
    trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Subfield.mem_closure_iff.mp hz
  rw [Subring.closure_eq] at hx hy
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  exact ⟨u, v, hxy.symm⟩

/-- Convenient form for an explicit set of generators in the embedded ring. -/
theorem of_adjoin_eq_top (S : Set E)
    (hgen : Algebra.adjoin F S = ⊤)
    (hS : S ⊆ Set.range (algebraMap A E)) : IsFractionRing A E := by
  apply of_adjoin_image_eq_top R F A E
  apply top_unique
  rw [← hgen]
  exact Algebra.adjoin_mono hS

end FourCorner.Multiquadratic.GeneratedFractionField


namespace FourCorner.Multiquadratic.CoordinateAlgebra

open Polynomial

variable (R : Type*) [CommRing R]

/-- First literal quadratic equation. -/
def equation₁ (a : R) : R[X] := X ^ 2 - C a

abbrev Stage₁ (a : R) := AdjoinRoot (equation₁ R a)

/-- Second literal quadratic equation, with coefficients in the first quotient. -/
def equation₂ (a b : R) : (Stage₁ R a)[X] :=
  X ^ 2 - C (algebraMap R (Stage₁ R a) b)

abbrev Stage₂ (a b : R) := AdjoinRoot (equation₂ R a b)

/-- Third literal quadratic equation, with coefficients in the second quotient. -/
def equation₃ (a b c : R) : (Stage₂ R a b)[X] :=
  X ^ 2 - C (algebraMap R (Stage₂ R a b) c)

abbrev Stage₃ (a b c : R) := AdjoinRoot (equation₃ R a b c)

theorem equation₁_monic (a : R) : (equation₁ R a).Monic :=
  monic_X_pow_sub_C a (by decide)

theorem equation₂_monic (a b : R) : (equation₂ R a b).Monic :=
  monic_X_pow_sub_C _ (by decide)

theorem equation₃_monic (a b c : R) : (equation₃ R a b c).Monic :=
  monic_X_pow_sub_C _ (by decide)

def basis₁ (a : R) := (AdjoinRoot.powerBasis' (equation₁_monic R a)).basis
def basis₂ (a b : R) := (basis₁ R a).smulTower
  (AdjoinRoot.powerBasis' (equation₂_monic R a b)).basis
def basis₃ (a b c : R) := (basis₂ R a b).smulTower
  (AdjoinRoot.powerBasis' (equation₃_monic R a b c)).basis

instance free₁ (a : R) : Module.Free R (Stage₁ R a) :=
  Module.Free.of_basis (basis₁ R a)
instance finite₁ (a : R) : Module.Finite R (Stage₁ R a) :=
  Module.Finite.of_basis (basis₁ R a)
instance free₂ (a b : R) : Module.Free R (Stage₂ R a b) :=
  Module.Free.of_basis (basis₂ R a b)
instance finite₂ (a b : R) : Module.Finite R (Stage₂ R a b) :=
  Module.Finite.of_basis (basis₂ R a b)
instance free₃ (a b c : R) : Module.Free R (Stage₃ R a b c) :=
  Module.Free.of_basis (basis₃ R a b c)
instance finite₃ (a b c : R) : Module.Finite R (Stage₃ R a b c) :=
  Module.Finite.of_basis (basis₃ R a b c)

instance free₂_over₁ (a b : R) : Module.Free (Stage₁ R a) (Stage₂ R a b) :=
  (equation₂_monic R a b).free_adjoinRoot
instance finite₂_over₁ (a b : R) : Module.Finite (Stage₁ R a) (Stage₂ R a b) :=
  (equation₂_monic R a b).finite_adjoinRoot
instance free₃_over₂ (a b c : R) : Module.Free (Stage₂ R a b) (Stage₃ R a b c) :=
  (equation₃_monic R a b c).free_adjoinRoot
instance finite₃_over₂ (a b c : R) : Module.Finite (Stage₂ R a b) (Stage₃ R a b c) :=
  (equation₃_monic R a b c).finite_adjoinRoot

lemma finrank₁ [Nontrivial R] (a : R) : Module.finrank R (Stage₁ R a) = 2 := by
  exact (AdjoinRoot.powerBasis' (equation₁_monic R a)).finrank.trans natDegree_X_pow_sub_C

instance nontrivial₁ [Nontrivial R] (a : R) : Nontrivial (Stage₁ R a) :=
  (Module.finrank_pos_iff_of_free (R := R) (M := Stage₁ R a)).mp (by rw [finrank₁]; decide)

lemma finrank₂_over₁ [Nontrivial R] (a b : R) :
    Module.finrank (Stage₁ R a) (Stage₂ R a b) = 2 := by
  exact (AdjoinRoot.powerBasis' (equation₂_monic R a b)).finrank.trans natDegree_X_pow_sub_C

lemma finrank₂ [Nontrivial R] (a b : R) : Module.finrank R (Stage₂ R a b) = 4 := by
  rw [Module.finrank_eq_card_basis (basis₂ R a b)]
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  change (equation₁ R a).natDegree * (equation₂ R a b).natDegree = 4
  simp only [equation₁, equation₂, natDegree_X_pow_sub_C]

instance nontrivial₂ [Nontrivial R] (a b : R) : Nontrivial (Stage₂ R a b) :=
  (Module.finrank_pos_iff_of_free (R := R) (M := Stage₂ R a b)).mp (by rw [finrank₂]; decide)

lemma finrank₃_over₂ [Nontrivial R] (a b c : R) :
    Module.finrank (Stage₂ R a b) (Stage₃ R a b c) = 2 := by
  exact (AdjoinRoot.powerBasis' (equation₃_monic R a b c)).finrank.trans natDegree_X_pow_sub_C

lemma finrank₃ [Nontrivial R] (a b c : R) : Module.finrank R (Stage₃ R a b c) = 8 := by
  rw [Module.finrank_eq_card_basis (basis₃ R a b c)]
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
  change (equation₁ R a).natDegree * (equation₂ R a b).natDegree *
    (equation₃ R a b c).natDegree = 8
  simp only [equation₁, equation₂, equation₃, natDegree_X_pow_sub_C]

instance nontrivial₃ [Nontrivial R] (a b c : R) : Nontrivial (Stage₃ R a b c) :=
  (Module.finrank_pos_iff_of_free (R := R) (M := Stage₃ R a b c)).mp (by rw [finrank₃]; decide)

/-- The first coordinate, carried to the final quotient. -/
def coordinate₁ (a b c : R) : Stage₃ R a b c :=
  algebraMap (Stage₁ R a) (Stage₃ R a b c) (AdjoinRoot.root (equation₁ R a))

/-- The second coordinate, carried to the final quotient. -/
def coordinate₂ (a b c : R) : Stage₃ R a b c :=
  algebraMap (Stage₂ R a b) (Stage₃ R a b c) (AdjoinRoot.root (equation₂ R a b))

/-- The third coordinate of the final quotient. -/
def coordinate₃ (a b c : R) : Stage₃ R a b c := AdjoinRoot.root (equation₃ R a b c)

@[simp] theorem coordinate₁_sq (a b c : R) :
    coordinate₁ R a b c ^ 2 = algebraMap R (Stage₃ R a b c) a := by
  have h : AdjoinRoot.root (equation₁ R a) ^ 2 = algebraMap R (Stage₁ R a) a := by
    have h := AdjoinRoot.eval₂_root (equation₁ R a)
    change (X ^ 2 - C a : R[X]).eval₂ (AdjoinRoot.of (equation₁ R a))
      (AdjoinRoot.root (equation₁ R a)) = 0 at h
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
    exact h
  rw [coordinate₁, ← map_pow, h, ← IsScalarTower.algebraMap_apply R (Stage₁ R a)]

@[simp] theorem coordinate₂_sq (a b c : R) :
    coordinate₂ R a b c ^ 2 = algebraMap R (Stage₃ R a b c) b := by
  have h : AdjoinRoot.root (equation₂ R a b) ^ 2 =
      algebraMap (Stage₁ R a) (Stage₂ R a b) (algebraMap R (Stage₁ R a) b) := by
    have h := AdjoinRoot.eval₂_root (equation₂ R a b)
    change (X ^ 2 - C (algebraMap R (Stage₁ R a) b) : (Stage₁ R a)[X]).eval₂
      (AdjoinRoot.of (equation₂ R a b)) (AdjoinRoot.root (equation₂ R a b)) = 0 at h
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
    exact h
  rw [coordinate₂, ← map_pow, h, ← IsScalarTower.algebraMap_apply R (Stage₁ R a),
    ← IsScalarTower.algebraMap_apply R (Stage₂ R a b)]

@[simp] theorem coordinate₃_sq (a b c : R) :
    coordinate₃ R a b c ^ 2 = algebraMap R (Stage₃ R a b c) c := by
  have h := AdjoinRoot.eval₂_root (equation₃ R a b c)
  change (X ^ 2 - C (algebraMap R (Stage₂ R a b) c) : (Stage₂ R a b)[X]).eval₂
    (AdjoinRoot.of (equation₃ R a b c)) (AdjoinRoot.root (equation₃ R a b c)) = 0 at h
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
  exact h

variable (F : Type*) [Field F] [Algebra R F]

abbrev field₁ (a : R) := Tower.first F (algebraMap R F a)
abbrev field₂ (a b : R) := Tower.second F (algebraMap R F a) (algebraMap R F b)
abbrev field₃ (a b c : R) := Tower.third F (algebraMap R F a) (algebraMap R F b)
  (algebraMap R F c)

def coefficientMap₁ (a : R) : R →+* field₁ R F a :=
  (algebraMap F (field₁ R F a)).comp (algebraMap R F)

theorem root₁_equation (a : R) :
    (equation₁ R a).eval₂ (coefficientMap₁ R F a)
      (Tower.stepRoot₁ F (algebraMap R F a)) = 0 := by
  simp only [equation₁, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    Tower.stepRoot₁_sq, coefficientMap₁, RingHom.comp_apply, sub_self]

/-- The first quotient embeds by sending its coordinate to the first radical. -/
def map₁ (a : R) : Stage₁ R a →+* field₁ R F a :=
  AdjoinRoot.lift (coefficientMap₁ R F a)
    (Tower.stepRoot₁ F (algebraMap R F a)) (root₁_equation R F a)

@[simp] theorem map₁_root (a : R) :
    map₁ R F a (AdjoinRoot.root (equation₁ R a)) =
      Tower.stepRoot₁ F (algebraMap R F a) := AdjoinRoot.lift_root _

@[simp] theorem map₁_algebraMap (a x : R) :
    map₁ R F a (algebraMap R (Stage₁ R a) x) =
      algebraMap F (field₁ R F a) (algebraMap R F x) := by
  exact AdjoinRoot.lift_of (root₁_equation R F a)

def coefficientMap₂ (a b : R) : Stage₁ R a →+* field₂ R F a b :=
  (algebraMap (field₁ R F a) (field₂ R F a b)).comp (map₁ R F a)

theorem root₂_equation (a b : R) :
    (equation₂ R a b).eval₂ (coefficientMap₂ R F a b)
      (Tower.stepRoot₂ F (algebraMap R F a) (algebraMap R F b)) = 0 := by
  simp only [equation₂, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    Tower.stepRoot₂_sq, coefficientMap₂, RingHom.comp_apply, map₁_algebraMap, sub_self]

/-- The second quotient map extends the first through the actual field inclusion. -/
def map₂ (a b : R) : Stage₂ R a b →+* field₂ R F a b :=
  AdjoinRoot.lift (coefficientMap₂ R F a b)
    (Tower.stepRoot₂ F (algebraMap R F a) (algebraMap R F b)) (root₂_equation R F a b)

@[simp] theorem map₂_root (a b : R) :
    map₂ R F a b (AdjoinRoot.root (equation₂ R a b)) =
      Tower.stepRoot₂ F (algebraMap R F a) (algebraMap R F b) := AdjoinRoot.lift_root _

@[simp] theorem map₂_of (a b : R) (x : Stage₁ R a) :
    map₂ R F a b (algebraMap (Stage₁ R a) (Stage₂ R a b) x) =
      algebraMap (field₁ R F a) (field₂ R F a b) (map₁ R F a x) :=
  AdjoinRoot.lift_of (root₂_equation R F a b)

@[simp] theorem map₂_algebraMap (a b x : R) :
    map₂ R F a b (algebraMap R (Stage₂ R a b) x) =
      algebraMap F (field₂ R F a b) (algebraMap R F x) := by
  rw [IsScalarTower.algebraMap_apply R (Stage₁ R a) (Stage₂ R a b), map₂_of,
    map₁_algebraMap, ← IsScalarTower.algebraMap_apply F (field₁ R F a) (field₂ R F a b)]

def coefficientMap₃ (a b c : R) : Stage₂ R a b →+* field₃ R F a b c :=
  (algebraMap (field₂ R F a b) (field₃ R F a b c)).comp (map₂ R F a b)

theorem root₃_equation (a b c : R) :
    (equation₃ R a b c).eval₂ (coefficientMap₃ R F a b c)
      (Tower.stepRoot₃ F (algebraMap R F a) (algebraMap R F b) (algebraMap R F c)) = 0 := by
  simp only [equation₃, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C,
    Tower.stepRoot₃_sq, coefficientMap₃, RingHom.comp_apply, map₂_algebraMap, sub_self]

/-- The third quotient map extends the second through the actual field inclusion. -/
def map₃ (a b c : R) : Stage₃ R a b c →+* field₃ R F a b c :=
  AdjoinRoot.lift (coefficientMap₃ R F a b c)
    (Tower.stepRoot₃ F (algebraMap R F a) (algebraMap R F b) (algebraMap R F c))
    (root₃_equation R F a b c)

@[simp] theorem map₃_root (a b c : R) :
    map₃ R F a b c (AdjoinRoot.root (equation₃ R a b c)) =
      Tower.stepRoot₃ F (algebraMap R F a) (algebraMap R F b) (algebraMap R F c) :=
  AdjoinRoot.lift_root _

@[simp] theorem map₃_of (a b c : R) (x : Stage₂ R a b) :
    map₃ R F a b c (algebraMap (Stage₂ R a b) (Stage₃ R a b c) x) =
      algebraMap (field₂ R F a b) (field₃ R F a b c) (map₂ R F a b x) :=
  AdjoinRoot.lift_of (root₃_equation R F a b c)

@[simp] theorem map₃_algebraMap (a b c x : R) :
    map₃ R F a b c (algebraMap R (Stage₃ R a b c) x) =
      algebraMap F (field₃ R F a b c) (algebraMap R F x) := by
  rw [IsScalarTower.algebraMap_apply R (Stage₂ R a b) (Stage₃ R a b c), map₃_of,
    map₂_algebraMap, ← IsScalarTower.algebraMap_apply F (field₂ R F a b) (field₃ R F a b c)]

@[simp] theorem map₃_coordinate₁ (a b c : R) :
    map₃ R F a b c (coordinate₁ R a b c) =
      root₁ F (algebraMap R F a) (algebraMap R F b) (algebraMap R F c) := by
  rw [coordinate₁, IsScalarTower.algebraMap_apply (Stage₁ R a) (Stage₂ R a b),
    map₃_of, map₂_of, map₁_root]
  apply Subtype.ext
  rfl

@[simp] theorem map₃_coordinate₂ (a b c : R) :
    map₃ R F a b c (coordinate₂ R a b c) =
      root₂ F (algebraMap R F a) (algebraMap R F b) (algebraMap R F c) := by
  rw [coordinate₂, map₃_of, map₂_root]
  apply Subtype.ext
  rfl

@[simp] theorem map₃_coordinate₃ (a b c : R) :
    map₃ R F a b c (coordinate₃ R a b c) =
      root₃ F (algebraMap R F a) (algebraMap R F b) (algebraMap R F c) :=
  map₃_root R F a b c

private theorem quadratic_irreducible {L : Type*} [Field L] (d : L)
    (hd : ¬ IsSquare d) : Irreducible (X ^ 2 - C d : L[X]) := by
  apply (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
  intro u hu
  exact hd ⟨u, by simpa only [sq] using hu.symm⟩

/-- The second radicand is still a nonsquare in the first actual field. -/
theorem second_nonsquare (a b : R) (h2 : (2 : F) ≠ 0)
    (ha : ¬ IsSquare (algebraMap R F a)) (hb : ¬ IsSquare (algebraMap R F b))
    (hab : ¬ IsSquare (algebraMap R F a * algebraMap R F b)) :
    ¬ IsSquare (algebraMap F (field₁ R F a) (algebraMap R F b)) := by
  intro h
  rcases QuadraticSquareCriterion.square_criterion (algebraMap R F a) (algebraMap R F b)
    (radical F (algebraMap R F a)) (radical_sq F _) ha h2 h with h | h
  · exact hb h
  · exact hab h

/-- The third radicand is still a nonsquare in the second actual field. -/
theorem third_nonsquare (a b c : R) (h2 : (2 : F) ≠ 0)
    (hind : IndependentSquareclasses F (algebraMap R F a) (algebraMap R F b)
      (algebraMap R F c)) :
    ¬ IsSquare (algebraMap F (field₂ R F a b) (algebraMap R F c)) := by
  intro h
  rcases QuadraticSquareCriterion.biquadratic_square_criterion
    (algebraMap R F a) (algebraMap R F b) (algebraMap R F c)
    (radical F (algebraMap R F a)) (radical F (algebraMap R F b))
    (radical_sq F _) (radical_sq F _) hind.first hind.second hind.first_second h2 h
      with h | h | h | h
  · exact hind.third h
  · exact hind.first_third h
  · exact hind.second_third h
  · exact hind.all_three (by simpa only [mul_assoc] using h)

/-- Injectivity of the first coordinate map follows from its irreducible generic equation. -/
theorem map₁_injective (a : R) (hi : Function.Injective (algebraMap R F))
    (ha : ¬ IsSquare (algebraMap R F a)) : Function.Injective (map₁ R F a) := by
  have hirr : Irreducible ((equation₁ R a).map (algebraMap R F)) := by
    simpa only [equation₁, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C] using quadratic_irreducible _ ha
  exact AdjoinRootInjective.lift_injective_of_monic_of_irreducible_map
    (algebraMap R F) hi (equation₁ R a) (equation₁_monic R a)
    (algebraMap F (field₁ R F a)) (Tower.stepRoot₁ F (algebraMap R F a)) hirr
    (root₁_equation R F a)

/-- Injectivity of the second coordinate map is derived over the first actual field. -/
theorem map₂_injective (a b : R) (hi : Function.Injective (algebraMap R F))
    (h2 : (2 : F) ≠ 0) (ha : ¬ IsSquare (algebraMap R F a))
    (hb : ¬ IsSquare (algebraMap R F b))
    (hab : ¬ IsSquare (algebraMap R F a * algebraMap R F b)) :
    Function.Injective (map₂ R F a b) := by
  have hirr : Irreducible ((equation₂ R a b).map (map₁ R F a)) := by
    simpa only [equation₂, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, map₁_algebraMap] using
      quadratic_irreducible _ (second_nonsquare R F a b h2 ha hb hab)
  exact AdjoinRootInjective.lift_injective_of_monic_of_irreducible_map
    (map₁ R F a) (map₁_injective R F a hi ha) (equation₂ R a b) (equation₂_monic R a b)
    (algebraMap (field₁ R F a) (field₂ R F a b))
    (Tower.stepRoot₂ F (algebraMap R F a) (algebraMap R F b)) hirr (root₂_equation R F a b)

/-- The entire coordinate algebra embeds in the actual three-radical field. -/
theorem map₃_injective (a b c : R) (hi : Function.Injective (algebraMap R F))
    (h2 : (2 : F) ≠ 0)
    (hind : IndependentSquareclasses F (algebraMap R F a) (algebraMap R F b)
      (algebraMap R F c)) : Function.Injective (map₃ R F a b c) := by
  have hirr : Irreducible ((equation₃ R a b c).map (map₂ R F a b)) := by
    simpa only [equation₃, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, map₂_algebraMap] using
      quadratic_irreducible _ (third_nonsquare R F a b c h2 hind)
  exact AdjoinRootInjective.lift_injective_of_monic_of_irreducible_map
    (map₂ R F a b) (map₂_injective R F a b hi h2 hind.first hind.second hind.first_second)
    (equation₃ R a b c) (equation₃_monic R a b c)
    (algebraMap (field₂ R F a b) (field₃ R F a b c))
    (Tower.stepRoot₃ F (algebraMap R F a) (algebraMap R F b) (algebraMap R F c))
    hirr (root₃_equation R F a b c)

/-- The final coordinate ring is a domain, proved by its explicit field embedding. -/
theorem stage₃_isDomain (a b c : R) (hi : Function.Injective (algebraMap R F))
    (h2 : (2 : F) ≠ 0)
    (hind : IndependentSquareclasses F (algebraMap R F a) (algebraMap R F b)
      (algebraMap R F c)) : IsDomain (Stage₃ R a b c) :=
  Function.Injective.isDomain (map₃ R F a b c) (map₃_injective R F a b c hi h2 hind)

/-- The base-ring algebra structure on the actual target field. -/
instance (priority := 900) targetAlgebra (a b c : R) : Algebra R (field₃ R F a b c) :=
  ((algebraMap F (field₃ R F a b c)).comp (algebraMap R F)).toAlgebra

/-- The target field is an algebra over the coordinate ring via the explicit map. -/
instance coordinateAlgebra (a b c : R) : Algebra (Stage₃ R a b c) (field₃ R F a b c) :=
  (map₃ R F a b c).toAlgebra

instance targetScalarTower (a b c : R) : IsScalarTower R F (field₃ R F a b c) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance coordinateScalarTower (a b c : R) :
    IsScalarTower R (Stage₃ R a b c) (field₃ R F a b c) :=
  IsScalarTower.of_algebraMap_eq fun x => (map₃_algebraMap R F a b c x).symm

/-- If `F` is the fraction field of the coefficient ring, the constructed
three-radical field is the fraction field of the actual coordinate ring. -/
theorem isFractionRing_stage₃ [IsFractionRing R F] (a b c : R)
    (h2 : (2 : F) ≠ 0)
    (hind : IndependentSquareclasses F (algebraMap R F a) (algebraMap R F b)
      (algebraMap R F c)) : IsFractionRing (Stage₃ R a b c) (field₃ R F a b c) := by
  have : FaithfulSMul (Stage₃ R a b c) (field₃ R F a b c) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (map₃_injective R F a b c (IsFractionRing.injective R F) h2 hind)
  let S : Set (field₃ R F a b c) :=
    {root₁ F (algebraMap R F a) (algebraMap R F b) (algebraMap R F c),
     root₂ F (algebraMap R F a) (algebraMap R F b) (algebraMap R F c),
     root₃ F (algebraMap R F a) (algebraMap R F b) (algebraMap R F c)}
  apply GeneratedFractionField.of_adjoin_eq_top R F (Stage₃ R a b c)
    (field₃ R F a b c) S
  · apply (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
      (fun x _ => (IsIntegral.of_finite F x).isAlgebraic)).mp
    exact roots_generate F _ _ _
  · intro x hx
    rcases hx with h | h | h
    · exact ⟨coordinate₁ R a b c, (map₃_coordinate₁ R F a b c).trans h.symm⟩
    · exact ⟨coordinate₂ R a b c, (map₃_coordinate₂ R F a b c).trans h.symm⟩
    · exact ⟨coordinate₃ R a b c, (map₃_coordinate₃ R F a b c).trans h.symm⟩

end FourCorner.Multiquadratic.CoordinateAlgebra

#print axioms FourCorner.Multiquadratic.CoordinateAlgebra.map₃_algebraMap

#print axioms FourCorner.Multiquadratic.CoordinateAlgebra.map₃_injective
#print axioms FourCorner.Multiquadratic.CoordinateAlgebra.stage₃_isDomain

#print axioms FourCorner.Multiquadratic.CoordinateAlgebra.finrank₃
#print axioms FourCorner.Multiquadratic.CoordinateAlgebra.isFractionRing_stage₃

#print axioms FourCorner.Multiquadratic.CoordinateAlgebra.coordinate₁_sq
#print axioms FourCorner.Multiquadratic.CoordinateAlgebra.coordinate₂_sq
#print axioms FourCorner.Multiquadratic.CoordinateAlgebra.coordinate₃_sq
