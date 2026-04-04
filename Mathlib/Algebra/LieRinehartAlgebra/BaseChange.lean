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


private abbrev auxA : A' ⊗[A] L →ₗ[A'] Derivation R A A' where
  toFun := TensorProduct.lift ((LinearMap.lsmul A' (Derivation R A A')).restrictScalars₁₂ A A)
    ∘ₗ (((Algebra.ofId A A').toLinearMap.compDer)
    ∘ₗ (LieRinehartAlgebra.anchor R A L).toLinearMap').lTensor A'
  map_add' _ _ := by simp
  map_smul' _ x := by
    refine x.induction_on ?_ ?_ ?_
    · simp
    · intros _ _
      ext _
      simp [smul_tmul', Derivation.smul_apply]
      ring
    · simp_all

variable (R A A' L) in
def Basechange : Submodule A'  ((A' ⊗[A] L) × (Derivation R A' A')) where
  carrier := {x | auxA (x.1) = (Derivation.compAlgebraMapL R A A' A') x.2 }
  zero_mem' := by simp
  add_mem' {_ _} _ _ := by simp_all
  smul_mem' _ _ hx := by
    rw [Set.mem_setOf_eq] at *
    simp [hx]

private abbrev auxR :  A' ⊗[R] L →ₗ[A] Derivation R A A' :=
auxA (R:=R) (A:=A) (A':=A') (L:=L) ∘ₗ (TensorProduct.mapOfCompatibleSMul A R A A' L)

private lemma aux_ext_apply' (a : A') (l : L) (z : A) : auxR (R:=R) (a⊗ₜl) (z) =
    ⁅l, z⁆ • a := by
  simp [Algebra.smul_def, mul_comm]
  rfl


variable (R A A' L) in
def preBasechange :
    LieSubalgebra R  ((A' ⊗[R] L) ⋊⁅(Lie.Derivation.ofDerivation L)⁆ (Derivation R A' A')) where
  carrier := {x | auxR (x.left) = (Derivation.compAlgebraMapL R A A' A') x.right }
  zero_mem' := by simp
  add_mem' {_ _} hx hy := by simp_all
  smul_mem' r x hx:= by simp_all
  lie_mem' {x y} hx hy := by
    -- helpful identities
    have CompL_apply (d : Derivation R A' A') (z : A) :
      ((Derivation.compAlgebraMapL R A A' A') d) z = d ((Algebra.ofId A A') z) := rfl
    -- obtaining sum of elementary tensors representations of x and y and simifying the hypotheses
    classical
    obtain ⟨Sx, h_x_as_sum⟩ := exists_finset (x.left)
    replace hx (t : A) := congrArg (fun f => f t) hx
    simp_rw [h_x_as_sum, map_sum, Derivation.sum_apply, aux_ext_apply', CompL_apply] at hx
    obtain ⟨Sy, h_y_as_sum⟩ := exists_finset (y.left)
    replace hy (t : A) := congrArg (fun f => f t) hy
    simp only [h_y_as_sum, map_sum, Derivation.sum_apply, aux_ext_apply', CompL_apply] at hy
    -- simplifying the main goal
    ext z
    simp_rw [LieAlgebra.SemiDirectSum.lie_eq_mk]
    -- transform RHS
    simp_rw [CompL_apply, Derivation.commutator_apply, ← hx,← hy, map_sum,
      Derivation.leibniz_smul, smul_eq_mul, CompL_apply, ← hx,← hy, Finset.sum_add_distrib,
      ← smul_eq_mul, Finset.smul_sum]
    -- transform LHS
    simp_rw [h_x_as_sum, h_y_as_sum, sum_lie_sum, map_sum, Lie.Derivation.ofDerivation_apply,
      LinearMap.rTensor_tmul, map_sub,map_add, map_sum, Derivation.sub_apply, Derivation.add_apply,
      Derivation.sum_apply, LieAlgebra.ExtendScalars.bracket_tmul, aux_ext_apply', lie_lie,sub_smul,
      smul_eq_mul, Finset.sum_sub_distrib]
    -- make them cancel
    rw [← sub_eq_zero]
    simp_rw [← sub_sub, ← sub_add, ← sub_sub, (Finset.sum_comm (s:=Sy) (t := Sx))]
    simp only [Derivation.coeFn_coe]
    ring_nf
    abel_nf
    simp_rw [neg_smul, one_smul, Algebra.mul_smul_comm, neg_add_cancel_comm_assoc, mul_comm,
      add_neg_cancel]

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
  use ⟨⟨x1, y.val.2⟩, by
    simp only [preBasechange, LinearMap.coe_comp, Function.comp_apply, LieSubalgebra.mem_mk_iff',
      Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    simp [hx, hy]⟩
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
    refine Submodule.closure_induction (by simp) (by grind only [= map_add, lie_add]) ?_ hmleft
    clear hm hmright hmleft
    -- since the set generating the span is multiplicatively closed we may assume `a = 1`
    intro a
    wlog ha : a = 1 generalizing a with H
    · rintro q ⟨b,b',l,hq⟩
      simp only [forall_eq, one_smul] at H
      refine H (a • q) ⟨b, a • b', l, ?_⟩
      simp_rw [hq.symm,  smul_sub, smul_tmul']
      rw [← sub_eq_zero, smul_comm]
      abel_nf
    rintro y ⟨b, a', l, hy⟩
    rw [ha, one_smul, hy.symm]
    -- now we rewrite the target s.th. we can replace x.right
    simp only [lie_sub, map_sub, LinearMap.rTensor_tmul, Derivation.coeFn_coe,
      mapOfCompatibleSMul_tmul, tmul_smul]
    simp_rw [Derivation.leibniz_smul, hx.symm, add_tmul, smul_tmul', add_sub_cancel_left]
    --
    refine x.left.induction_on (by simp) ?_ ?_
    · intros c z
      rw [aux_ext_apply']
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
