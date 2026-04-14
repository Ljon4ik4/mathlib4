import Mathlib.Algebra.LieRinehartAlgebra.Defs
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.Lie.Derivation.BaseChange
import Mathlib.Algebra.Lie.SemiDirect


section

/-
# Todos:
- `TensorProduct.AlgebraTensorModule.ker_mapOfCompatibleSMul` is a bad namespace it should be just
int the `TensorProduct` namespace, as indicated in the doc of the surjectivity of the map

-/


section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {s : Set M}
open AddSubmonoid Submodule Function Set Pointwise in
/-- A variant of `span_induction` that combines `∀ x ∈ s, p x` and `∀ r x, p x → p (r • x)`
into a single condition `∀ r, ∀ x ∈ s, p (r • x)`, which can be easier to verify. -/
@[elab_as_elim]
theorem closure_induction' {p : (x : M) → x ∈ span R s → Prop}
    (zero : p 0 (Submodule.zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (Submodule.add_mem _ ‹_› ‹_›))
    (mem : ∀ (x) (h : x ∈ s), p x (subset_span h))
    (smul_set : ∀ (r : R) (x : M) (h : x ∈ s),  (r • x) ∈ s) {x}
    (hx : x ∈ span R s) : p x hx := by
  refine Submodule.closure_induction (p := p) zero add ?_ hx  
  simp_all
end
 

section
variable {R : Type*} {A : Type*} {M : Type*}
variable [CommSemiring R] [CommSemiring A] [AddCommMonoid M]
variable [Algebra R A]
variable [Module R M] [Module A M]


theorem Derivation.coe_sum_linear_maps {ι : Type*} (t : Finset ι) (f : ι → (Derivation R A M)) :
    ↑(∑ i ∈ t, f i) = ∑ i ∈ t, (f i : A →ₗ[R] M) :=
  _root_.map_sum
    (show AddMonoidHom (Derivation R A M) (A →ₗ[R] M)
      from { toFun := toLinearMap,
             map_zero' := rfl
             map_add' := fun _ _ => rfl }) _ _

theorem Derivation.sum_apply {ι : Type*} (t : Finset ι) (f : ι → (Derivation R A M)) (a : A) :
    (∑ i ∈ t, f i) a = ∑ i ∈ t, (f i a) := by
  rw [← Derivation.coeFn_coe, Derivation.coe_sum_linear_maps, LinearMap.sum_apply]
  simp


variable {B : Type*} [CommSemiring B] [Algebra R B] [Algebra A B] [Module B M]
[IsScalarTower R A B] [IsScalarTower A B M] [IsScalarTower R B M]
theorem Derivation.leibniz_smul (d : Derivation R B M) (a : A) (b : B) : d (a • b) =
    a • (d b) + b • (d.compAlgebraMapL R A B M a) := by
  simp [Algebra.smul_def]

end



section

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {A' : Type*} [CommRing A'] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']

variable {L : Type*} [LieRing L] [Module A L] [LieRingModule L A] [LieRinehartRing A L]
    [LieAlgebra R L] [LieRinehartAlgebra R A L]


open TensorProduct

private def anchor_comp := LinearMap.liftBaseChange (A := A')
  (((Algebra.ofId A A').toLinearMap.compDer) ∘ₗ (LieRinehartAlgebra.anchor R A L).toLinearMap')

private lemma anchor_comp_apply (a : A') (l : L) (z : A) : anchor_comp (R := R) (a⊗ₜl) (z) =
    ⁅l, z⁆ • a := by
  simp [Algebra.smul_def, mul_comm]
  rfl

variable (R A A' L) in
def Basechange : Submodule A'  ((A' ⊗[A] L) × (Derivation R A' A')) where
  carrier := {x | anchor_comp (x.1) = (Derivation.compAlgebraMapL R A A' A') x.2 }
  zero_mem' := by simp
  add_mem' {_ _} _ _ := by simp_all
  smul_mem' _ _ _ := by simp_all


variable (R A A' L) in
private abbrev preBasechange :
    LieSubalgebra R  ((A' ⊗[R] L) ⋊⁅(Lie.Derivation.ofDerivation L)⁆ (Derivation R A' A')) where
  carrier := {x | anchor_comp ((mapOfCompatibleSMul A R A A' L) (x.left))
    = (Derivation.compAlgebraMapL R A A' A') x.right }
  zero_mem' := by simp
  add_mem' {_ _} _ _ := by simp_all
  smul_mem' _ _ _:= by simp_all
  lie_mem' {x y} hx hy := by
    replace hx (t : A) := congrArg (fun f => f t) hx
    replace hy (t : A) := congrArg (fun f => f t) hy
    ext z
    rw [← sub_eq_zero]
    obtain ⟨Sx, h_x_as_sum⟩ := exists_finset (x.left)
    obtain ⟨Sy, h_y_as_sum⟩ := exists_finset (y.left)
    -- should 'only' be added to the simps here?
    simp_all [Derivation.commutator_apply, sum_lie_sum, Derivation.sum_apply, anchor_comp_apply]
    simp [← hx, ← hy, Derivation.leibniz_smul, sub_smul, Finset.sum_add_distrib]
    ring_nf
    simp_rw [Finset.mul_sum, (Finset.sum_comm (s:=Sy) (t := Sx))]
    simp only [← Finset.sum_sub_distrib, Algebra.mul_smul_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero ?_
    intro _ _
    refine Finset.sum_eq_zero ?_
    intro _ _
    ring_nf

variable (R A A' L) in
private abbrev pr : (preBasechange R A A' L) →ₗ[R] (Basechange R A A' L) where
  toFun x := ⟨((TensorProduct.mapOfCompatibleSMul A R A A' L x.val.left), x.val.right), by
    have hx : (_ = _) := x.property
    change (_ = _)
    simpa using hx⟩
  map_add'  := by simp
  map_smul' := by simp

private lemma pr_surjective : Function.Surjective (pr R A A' L) := by
  intro y
  have hy : (_ = _) := y.property
  let x1 := Function.surjInv (mapOfCompatibleSMul_surjective A R A A' L) y.val.1
  have hx : ((mapOfCompatibleSMul A R A A' L) x1) = y.val.1 := by simp [x1, Function.surjInv_eq]
  use ⟨⟨x1, y.val.2⟩, by simp [hx, hy]⟩
  simp [pr, hx]

variable (R A A' L) in
def basechange_ker : LieIdeal R (preBasechange R A A' L) where
  __ := LinearMap.ker (pr R A A' L)
  lie_mem := by
    rintro ⟨x, hx⟩ ⟨m, _⟩ hm
    -- first we simplify and apply the condition on `m`
    have ⟨hmleft, hmright⟩: (m.left ∈ (mapOfCompatibleSMul A R A A' L).ker) ∧ m.right = 0 :=
      by simp_all
    rw [TensorProduct.AlgebraTensorModule.ker_mapOfCompatibleSMul] at hmleft
    convert_to (mapOfCompatibleSMul A R A A' L) ⁅x.left, m.left⁆ +
      (mapOfCompatibleSMul A R A A' L) ((LinearMap.rTensor L ↑x.right) m.left) = 0
    · simp [hmright, Lie.Derivation.ofDerivation_apply]
    refine closure_induction' (by simp) (by grind only [= map_add, lie_add]) ?_ ?_ hmleft
    · rintro a x ⟨b, b', l, h⟩
      use b, a • b', l
      simp_rw [← h, smul_sub, smul_tmul']
      rw [← sub_eq_zero, smul_comm]
      abel_nf
    rintro y ⟨b, a', l, hy⟩
    rw [hy.symm]
    -- now we rewrite the target s.th. we can replace x.right
    simp only [lie_sub, map_sub, LinearMap.rTensor_tmul, Derivation.coeFn_coe,
      mapOfCompatibleSMul_tmul, tmul_smul]
    simp_rw [Derivation.leibniz_smul, hx.symm, add_tmul, smul_tmul', add_sub_cancel_left]
    refine x.left.induction_on (by simp) ?_ ?_
    · intros c z
      rw [mapOfCompatibleSMul_tmul, anchor_comp_apply]
      simp [tmul_add, smul_tmul']
      ring_nf
      abel_nf
    · rintro p q hp hq
      simp_rw [add_lie, map_add, Derivation.add_apply, smul_add, add_tmul]
      grind
    

private noncomputable abbrev iso : ((preBasechange R A A' L) ⧸ (basechange_ker R A A' L))
    ≃ₗ[R] (Basechange R A A' L)
  := LinearMap.quotKerEquivOfSurjective (pr R A A' L) (pr_surjective)

noncomputable instance : LieRing (Basechange R A A' L) where
  bracket x y := iso ⁅ iso.symm x, iso.symm y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _  := by simp
  leibniz_lie _ _ _ := by simp

private lemma bracket_unfold (x y : (Basechange R A A' L)) : ⁅x, y⁆ = iso ⁅ iso.symm x, iso.symm y⁆
  := rfl

noncomputable instance : LieAlgebra R (Basechange R A A' L) where
  lie_smul _ _ _ := by simp [bracket_unfold]

private noncomputable def iso' : ((preBasechange R A A' L) ⧸ (basechange_ker R A A' L))
    ≃ₗ⁅R⁆ (Basechange R A A' L) where
  __ := iso
  map_lie' {_ _} := by simp [bracket_unfold]

noncomputable def snd : (Basechange R A A' L) →ₗ⁅R⁆ Derivation R A' A' where
  __ := (LinearMap.snd R (A' ⊗[A] L) (Derivation R A' A')) ∘ₗ ((Basechange R A A' L).subtype)
  map_lie' {x y} := by
    simp only [bracket_unfold, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_comp,
      LinearMap.coe_snd, LinearMap.coe_restrictScalars, Submodule.coe_subtype, Function.comp_apply]
    have h_iso : ∀ x y : (preBasechange R A A' L) ⧸ (basechange_ker R A A' L), -- autogen, to improve
      (iso ⁅x, y⁆).val.2 = ⁅(iso x).val.2, (iso y).val.2⁆ := by
      intro x y
      induction x using Quotient.inductionOn
      induction y using Quotient.inductionOn
      rfl
    convert h_iso (iso.symm x) (iso.symm y)
    · simp
    · simp

noncomputable instance : LieRingModule  (Basechange R A A' L) A' where
  bracket x a := (snd x) a
  add_lie _ _ := by simp
  lie_add _ _ := by simp
  leibniz_lie _ _ _ := by
    rw [LieHom.map_lie, Derivation.commutator_apply]
    simp

private lemma lbracket_apply (x : (Basechange R A A' L)) (a : A') : ⁅x, a⁆ = (snd x) a := rfl

noncomputable instance : LieRinehartRing A' (Basechange R A A' L) where
  lie_smul_eq_mul' _ _ x := by
    obtain ⟨_, _⟩ := x --why needed?
    simp
    rfl
  leibniz_mul_right' x a b := by simp [lbracket_apply, mul_comm]
  leibniz_smul_right' x y a := by
    simp [lbracket_apply]
    sorry



end
end
