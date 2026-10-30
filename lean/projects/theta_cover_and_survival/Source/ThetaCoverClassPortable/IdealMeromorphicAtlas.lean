import ThetaCoverClassPortable.CartierWeilInjectivity
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module_and_exists_presentation_isFrameOn
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
namespace FourCorner.IdealMeromorphicAtlas
variable {X : Scheme} [IsIntegral X] (I : X.IdealSheafData) (hI : I.IsInvertible)

structure Generator (x : X) where
  U : X.affineOpens
  mem : x∈(U : X.Opens)
  g : Γ(X,U)
  regular : g∈nonZeroDivisors Γ(X,U)
  ideal : I.ideal U=Ideal.span {g}

include hI in
theorem generator_exists (x : X) : Nonempty (Generator I x) := by
  obtain ⟨U,f,hxf,g,hg,hIg⟩ := hI x
  exact ⟨⟨X.affineBasicOpen f,hxf,g,hg,hIg⟩⟩

def generator (x : X) : Generator I x := (generator_exists I hI x).some
abbrev U (x : X) : X.Opens := (generator I hI x).U
instance chart_nonempty (x : X) : Nonempty (U I hI x) := ⟨⟨x,(generator I hI x).mem⟩⟩
lemma affine (x : X) : IsAffineOpen (U I hI x) := (generator I hI x).U.property
lemma cover : ⨆x,U I hI x=⊤ := by
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x,(generator I hI x).mem⟩

def presentation : ∀V : X.Opens,Γ(I.module,V)→+ X.functionField :=
  (hI.isInvertible_module_and_exists_presentation_isFrameOn).2.choose

lemma presentation_res (V W : X.Opens) (h : W≤V) [Nonempty W] (m : Γ(I.module,V)) :
    presentation I hI W (I.module.presheaf.map (homOfLE h).op m)=presentation I hI V m :=
  (hI.isInvertible_module_and_exists_presentation_isFrameOn).2.choose_spec.1 V W h inferInstance m

lemma presentation_smul (V : X.Opens) [Nonempty V] (r : Γ(X,V)) (m : Γ(I.module,V)) :
    presentation I hI V (r•m)=algebraMap Γ(X,V) X.functionField r*presentation I hI V m :=
  (hI.isInvertible_module_and_exists_presentation_isFrameOn).2.choose_spec.2.1 V r m

lemma frame_exists (x : X) : ∃m : Γ(I.module,U I hI x),
    IsFrameOn m (U I hI x) ∧ presentation I hI (U I hI x) m=
      algebraMap Γ(X,U I hI x) X.functionField (generator I hI x).g := by
  exact (hI.isInvertible_module_and_exists_presentation_isFrameOn).2.choose_spec.2.2.2
    (generator I hI x).U inferInstance (generator I hI x).g
    (generator I hI x).regular (generator I hI x).ideal

def frame (x : X) : Γ(I.module,U I hI x) := (frame_exists I hI x).choose
lemma frame_isFrame (x : X) : IsFrameOn (frame I hI x) (U I hI x) := (frame_exists I hI x).choose_spec.1

def q (x : X) : X.functionField := algebraMap Γ(X,U I hI x) X.functionField (generator I hI x).g
lemma frame_value (x : X) : presentation I hI (U I hI x) (frame I hI x)=q I hI x := (frame_exists I hI x).choose_spec.2
lemma q_ne_zero (x : X) : q I hI x≠0 := by
  intro hz
  have hg : (generator I hI x).g=0 := X.germToFunctionField_injective (U I hI x) (by exact hz.trans (map_zero _).symm)
  exact (mem_nonZeroDivisors_iff_ne_zero.mp (generator I hI x).regular) hg

def cc : UnitCocycle (U I hI) :=
  (exists_unitCocycle_map_eq_smul_of_isFrameOn (frame I hI) (frame_isFrame I hI)).choose
lemma transition (x y : X) :
    I.module.presheaf.map (homOfLE (inf_le_right : U I hI x ⊓ U I hI y ≤ U I hI y)).op (frame I hI y)=
      (cc I hI).u x y • I.module.presheaf.map (homOfLE inf_le_left).op (frame I hI x) :=
  (exists_unitCocycle_map_eq_smul_of_isFrameOn (frame I hI) (frame_isFrame I hI)).choose_spec x y

local instance pair_nonempty (x y : X) : Nonempty ((U I hI x ⊓ U I hI y : X.Opens) : Scheme) := KummerUnitCocycle.nonempty_inf _ _

lemma transition_field (x y : X) :
    algebraMap Γ(X,U I hI x ⊓ U I hI y) X.functionField ((cc I hI).u x y)=q I hI y/q I hI x := by
  have ht := congrArg (presentation I hI (U I hI x ⊓ U I hI y)) (transition I hI x y)
  rw [presentation_smul,presentation_res,presentation_res,frame_value,frame_value] at ht
  exact (eq_div_iff (q_ne_zero I hI x)).mpr ht.symm

theorem actual_module_glue :
    ∃e : I.module ≅ glueOfCocycle (cc I hI),∀x,e.hom.app (U I hI x) (frame I hI x)=glueFrame (cc I hI) x :=
  exists_iso_glueOfCocycle_app_eq_glueFrame (cover I hI) (cc I hI) (frame I hI) (frame_isFrame I hI) (transition I hI)

#print axioms actual_module_glue
end FourCorner.IdealMeromorphicAtlas
