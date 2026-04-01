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
  rw [← Derivation.coeFn_coe]
  rw [Derivation.coe_sum_linear_maps]
  rw [LinearMap.sum_apply]
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

private abbrev auxA : A' ⊗[A] L →ₗ[A] Derivation R A A' :=
    TensorProduct.lift ((LinearMap.lsmul A' (Derivation R A A')).restrictScalars₁₂ A A)
    ∘ₗ (((Algebra.ofId A A').toLinearMap.compDer)
    ∘ₗ (LieRinehartAlgebra.anchor R A L).toLinearMap').lTensor A'

private abbrev auxRR :  A' ⊗[R] L →ₗ[A] Derivation R A A' :=
auxA (R:=R) (A:=A) (A':=A') (L:=L) ∘ₗ (TensorProduct.mapOfCompatibleSMul A R A A' L)

private lemma aux_ext_apply (a : A') (l : L) (z : A) : auxRR (R:=R) (a⊗ₜl) (z) =
    a •  (Algebra.ofId A A') ⁅l, z⁆ := by
  simp
  rfl

variable (R A A' L) in
def preBasechange :
    LieSubalgebra R  ((A' ⊗[R] L) ⋊⁅(Lie.Derivation.ofDerivation L)⁆ (Derivation R A' A')) where
  carrier := {x | auxRR (x.left) = (Derivation.compAlgebraMapL R A A' A') x.right }
  zero_mem' := by simp
  add_mem' {_ _} hx hy := by
    rw [Set.mem_setOf,← LieAlgebra.SemiDirectSum.projl_mk,←LieAlgebra.SemiDirectSum.projr_mk] at *
    repeat rw [map_add]
    rw [hx,hy]
  smul_mem' r x hx:= by
    simp_all
  lie_mem' {x y} hx hy := by
    -- helpful identities
    have CompL_apply (d : Derivation R A' A') (z : A) :
      ((Derivation.compAlgebraMapL R A A' A') d) z = d ((Algebra.ofId A A') z) := rfl
    -- obtaining sum of elementary tensors representations of x and y and simifying the hypotheses
    classical
    obtain ⟨Sx, h_x_as_sum⟩ := exists_finset (x.left)
    replace hx (t : A) := congrArg (fun f => f t) hx
    simp only [h_x_as_sum, map_sum, Derivation.sum_apply, aux_ext_apply, CompL_apply] at hx
    obtain ⟨Sy, h_y_as_sum⟩ := exists_finset (y.left)
    replace hy (t : A) := congrArg (fun f => f t) hy
    simp only [h_y_as_sum, map_sum, Derivation.sum_apply, aux_ext_apply, CompL_apply] at hy
    -- simplifying the main goal
    ext z
    simp_rw [LieAlgebra.SemiDirectSum.lie_eq_mk]
    -- transform RHS
    simp_rw [CompL_apply, Derivation.commutator_apply, ← hx,← hy, map_sum, smul_eq_mul,
      Derivation.leibniz, smul_eq_mul, ← hx,← hy, Finset.sum_add_distrib,← smul_eq_mul,
        Finset.smul_sum]
    -- transform LHS
    simp_rw [h_x_as_sum, h_y_as_sum, sum_lie_sum, map_sum, Lie.Derivation.ofDerivation_apply,
      LinearMap.rTensor_tmul, map_sub,map_add, map_sum, Derivation.sub_apply, Derivation.add_apply,
      Derivation.sum_apply, LieAlgebra.ExtendScalars.bracket_tmul, aux_ext_apply, lie_lie, map_sub,
      smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    -- make them cancel
    rw [← sub_eq_zero]
    simp_rw [← sub_sub, ← sub_add, ← sub_sub, (Finset.sum_comm (s:=Sy) (t := Sx))]
    simp only [Algebra.ofId_apply, Derivation.coeFn_coe]
    ring_nf
    grind


variable (R A A' L) in
def Basechange : Submodule A  ((A' ⊗[A] L) × (Derivation R A' A')) where
  carrier := {x | auxA (x.1) = (Derivation.compAlgebraMapL R A A' A') x.2 }
  zero_mem' := by simp
  add_mem' {_ _} hx hy := by
    simp at *
    grind
  smul_mem' _ _ hx:= by
    simp at *
    simp [hx]

variable (R A A' L) in
abbrev pr : (preBasechange R A A' L) →ₗ[R] (Basechange R A A' L) where
  toFun x := ⟨((TensorProduct.mapOfCompatibleSMul A R A A' L x.val.left), x.val.right),by
    have hx : (_ = _) := x.property
    change (_ = _)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hx
    simpa using hx⟩
  map_add'  := by simp
  map_smul' := by simp

lemma pr_surjective : Function.Surjective (pr R A A' L) := by
  intro y
  have hy : (_ = _) := y.property
  let x1 := Function.surjInv (mapOfCompatibleSMul_surjective A R A A' L) y.val.1
  have hx : ((mapOfCompatibleSMul A R A A' L) x1) = y.val.1 := by simp [x1, Function.surjInv_eq]
  use ⟨⟨x1, y.val.2⟩, by
    simp only [preBasechange, LinearMap.coe_comp, Function.comp_apply, LieSubalgebra.mem_mk_iff',
      Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    simpa [hx, hy]⟩
  simp [pr, hx]


variable (R A A' L) in
def kr : LieIdeal R (preBasechange R A A' L) where
  __ := LinearMap.ker (pr R A A' L)
  lie_mem := by
    intros x m hm
    -- sum desxription of `x`
    have hx : ( _ = _ ) := x.property
    obtain ⟨Sx, h_x_as_sum⟩ := exists_finset (x.val.left)
    -- obtain properties of `m`
    simp only [Submodule.carrier_eq_coe, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_mk,
      AddHom.coe_mk, Submodule.mk_eq_zero, Prod.mk_eq_zero] at hm
    obtain ⟨hmleft, hmright⟩ := hm
    change m.val.left ∈ (mapOfCompatibleSMul A R A A' L).ker at hmleft
    rw [TensorProduct.AlgebraTensorModule.ker_mapOfCompatibleSMul] at hmleft
    -- simplify the goal
    simp only [hmright, Submodule.carrier_eq_coe, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_mk,
      AddHom.coe_mk, LieSubalgebra.coe_bracket, LieAlgebra.SemiDirectSum.lie_eq_mk,
      Lie.Derivation.ofDerivation_apply, map_zero, LieDerivation.coe_zero, Pi.zero_apply,
      sub_zero, lie_zero, map_add, Submodule.mk_eq_zero, Prod.mk_eq_zero, and_true]
    -- show the goal by induction on `m`
    refine Submodule.closure_induction ?_ ?_ ?_ hmleft
    · simp
    · intros u v hu hv hxu hxv
      rw [lie_add,map_add]
      grind
    · rintro a y ⟨b, a', l, hy⟩
      -- simplify the expression by grouping `a•a'`
      let b' := a • a'
      have hz:  (b • b') ⊗ₜ[R] l - b' ⊗ₜ[R] (b • l) = a • y := by
        unfold b'
        simp_rw [hy.symm, smul_sub, smul_tmul']
        rw [← sub_eq_zero, smul_comm]
        abel_nf
      simp_rw [hz.symm]
      --
      simp_rw [lie_sub, map_sub, LinearMap.rTensor_tmul, Derivation.coeFn_coe, mapOfCompatibleSMul_tmul,
        tmul_smul, Derivation.leibniz_smul, hx.symm, add_tmul, smul_tmul']
      simp_rw [h_x_as_sum, sum_lie, map_sum, Derivation.sum_apply, aux_ext_apply]
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, Algebra.mul_smul_comm,
        mapOfCompatibleSMul_tmul, LieRinehartAlgebra.LieRinehartRing.leibniz_smul_right,
        Algebra.ofId_apply, smul_eq_mul, add_sub_cancel_left, tmul_add]
      repeat rw [← smul_eq_mul, Finset.smul_sum, sum_tmul]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero ?_
      intro t _
      simp only [smul_tmul, tmul_smul, map_add, mapOfCompatibleSMul_tmul, sub_add_cancel_left,
        smul_eq_mul]
      rw [← neg_smul, smul_tmul', ← add_tmul]
      rw [add_comm, Algebra.smul_def, neg_eq_neg_one_mul]
      simp
      ring_nf
      exact zero_tmul A' l

end
end
