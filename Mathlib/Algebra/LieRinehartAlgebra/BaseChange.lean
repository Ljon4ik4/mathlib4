import Mathlib.Algebra.LieRinehartAlgebra.Derivation_additions
import Mathlib.Algebra.LieRinehartAlgebra.TensorStuff
import Mathlib.Algebra.LieRinehartAlgebra.Defs
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Finiteness



section
--this should be in Defs
variable {A L : Type*} [CommRing A] [LieRing L] [Module A L] [LieRingModule L A]
    [LieRinehartRing A L]

@[simp]
lemma LieRinehartRing.lie_smul_eq_mul' (a b : A) (x : L) : ⁅a • x, b⁆ = a * ⁅x, b⁆ :=
  LieRinehartRing.lie_smul_eq_mul a b x

@[simp]
lemma LieRinehartRing.leibniz_mul_right' (x : L) (a b : A) :
    ⁅x, a * b⁆ = a • ⁅x, b⁆ + ⁅x, a⁆ * b := LieRinehartRing.leibniz_mul_right x a b

@[simp]
lemma LieRinehartRing.leibniz_smul_right' (x y : L) (a : A) :
    ⁅x, a • y⁆ = a • ⁅x, y⁆ + ⁅x, a⁆ • y := LieRinehartRing.leibniz_smul_right x y a

end


section

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {A' : Type*} [CommRing A'] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']

variable {L : Type*} [LieRing L] [Module A L] [LieRingModule L A] [LieRinehartRing A L]
    [LieAlgebra R L] [LieRinehartAlgebra R A L]

-- this should be in Defs.lean, also maybe anchor should be moved out of the hom namespace
lemma anchor_apply (l : L) (a : A) : (LieRinehartAlgebra.Hom.anchor R A L l) a = ⁅l, a⁆ := rfl



open TensorProduct


private abbrev auxA : A' ⊗[A] L →ₗ[A] Derivation R A A' :=
    TensorProduct.lift ((LinearMap.lsmul A' (Derivation R A A')).restrictScalars₁₂ A A)
    ∘ₗ (((Algebra.ofId A A').toLinearMap.compDer)
    ∘ₗ (LieRinehartAlgebra.Hom.anchor R A L).toLinearMap').lTensor A'

private abbrev auxRR :  A' ⊗[R] L →ₗ[R] Derivation R A A' :=
auxA (R:=R) (A:=A) (A':=A') (L:=L) ∘ₗ (TensorProduct.mapOfCompatibleSMul A R A' L)


private lemma aux_ext_apply (a : A') (l : L) (z : A) : auxRR (R:=R) (a⊗ₜl) (z) =
    a •  (Algebra.ofId A A') ⁅l, z⁆ := by
  simp only [LinearMap.coe_comp, LinearMap.restrictScalars_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, mapOfCompatibleSMul_tmul, LinearMap.lTensor_tmul, lift.tmul,
    LinearMap.restrictScalars₁₂_apply_apply, LinearMap.lsmul_apply, Derivation.coe_smul,
    Derivation.coe_comp, AlgHom.coe_toLinearMap, Derivation.coeFn_coe, Pi.smul_apply,
    Algebra.ofId_apply, smul_eq_mul]
  rw [LieRinehartAlgebra.Hom.toLinearMap'_apply]
  simp [anchor_apply]


variable (R A A' L) in
def preBasechange :
    LieSubalgebra R  ((A' ⊗[R] L) ⋊⁅(ExtendDerToLieDerHom R A' L)⁆ (Derivation R A' A')) where
  carrier := {x | auxRR (x.left) = (Derivation.compAlgebraMapL R A A' A') x.right }
  zero_mem' := by simp
  add_mem' {_ _} hx hy := by
    rw [Set.mem_setOf,← LieAlgebra.SemiDirectSum.projl_mk,←LieAlgebra.SemiDirectSum.projr_mk] at *
    repeat rw [map_add]
    rw [hx,hy]
  smul_mem' r x hx:= by
    rw [Set.mem_setOf,←LieAlgebra.SemiDirectSum.projl_mk,←LieAlgebra.SemiDirectSum.projr_mk] at *
    rw [map_smul, map_smul,map_smul, hx]
    simp
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
    simp_rw [h_x_as_sum, h_y_as_sum, sum_lie_sum, map_sum, ExtendDerToLieDerHom_apply,
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
def pr : (preBasechange R A A' L) →ₗ[R] (Basechange R A A' L) where
  toFun x := ⟨((TensorProduct.mapOfCompatibleSMul A R A' L x.val.left), x.val.right),by
    have hx : (_ = _) := x.property
    change (_ = _)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hx
    simpa using hx⟩
  map_add'  := by simp
  map_smul' := by simp

lemma pr_surjective : Function.Surjective (pr R A A' L) := by
  intro y
  have hy : (_ = _) := y.property
  let x1 := Function.surjInv (mapOfCompatibleSMul_surjective A R A' L) y.val.1
  have hx : ((mapOfCompatibleSMul A R A' L) x1) = y.val.1 := by simp [x1, Function.surjInv_eq]
  use ⟨⟨x1, y.val.2⟩, by
    simp only [preBasechange, LinearMap.coe_comp, LinearMap.restrictScalars_comp,
      LinearMap.coe_restrictScalars, Function.comp_apply, LieSubalgebra.mem_mk_iff',
      Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    simpa [hx, hy]⟩
  simp [pr, hx]


open scoped Pointwise
variable (R A A' L) in
def kr : LieIdeal R (preBasechange R A A' L) where
  __ := LinearMap.ker (pr R A A' L)
  lie_mem := by
    intros x m
    have hx : ( _ = _ ) := x.property
    intro hm
    simp only [pr, Submodule.carrier_eq_coe, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_mk,
      AddHom.coe_mk, Submodule.mk_eq_zero, Prod.mk_eq_zero] at hm
    obtain ⟨hmleft, hmright⟩ := hm
    change m.val.left ∈ (mapOfCompatibleSMul' A R A' L).ker at hmleft
    rw [CompatibleSMul_ker_eq_span] at hmleft
    simp only [pr, Submodule.carrier_eq_coe, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_mk,
      AddHom.coe_mk, LieSubalgebra.coe_bracket, LieAlgebra.SemiDirectSum.lie_eq_mk,
      ExtendDerToLieDerHom_apply, hmright, map_zero, LieDerivation.coe_zero, Pi.zero_apply,
      sub_zero, lie_zero, map_add, Submodule.mk_eq_zero, Prod.mk_eq_zero, and_true]
    obtain ⟨Sx, h_x_as_sum⟩ := exists_finset (x.val.left)
    rw [← Submodule.mem_toAddSubmonoid, Submodule.span_eq_closure] at hmleft
    have helper :  ( (@Set.univ A) • (elementary_rel R A A' L)) = elementary_rel R A A' L := by
      refine Set.Subset.antisymm ?_ ?_
      · refine Set.smul_subset_iff.mpr ?_
        intros a ha b hb
        simp_rw [(smul_elementary_rel a b hb)]
      · intros x hx
        refine Set.mem_smul.mpr ?_
        use (1 : A)
        refine ⟨trivial, ?_⟩
        use x
        refine ⟨hx, by simp⟩
    rw [helper] at hmleft
    refine AddSubmonoid.closure_induction ?_ ?_ ?_ hmleft
    · intro y hy
      obtain ⟨a, a', l, h⟩ := hy
      simp_rw [← h, h_x_as_sum]
      simp only [lie_sub, sum_lie, LieAlgebra.ExtendScalars.bracket_tmul, Algebra.mul_smul_comm,
        LieRinehartRing.leibniz_smul_right', map_sub, map_sum, mapOfCompatibleSMul_tmul,
        LinearMap.rTensor_tmul, Derivation.coeFn_coe, tmul_smul]
      rw [← (algebraMap_smul A' a a'), smul_eq_mul, Derivation.leibniz, add_tmul, smul_tmul']
      simp_rw [(algebraMap_smul A' a _)]
      simp only [smul_eq_mul, add_sub_cancel_left]
      have h : x.val.right ((algebraMap A A') a)
          = ((Derivation.compAlgebraMapL R A A' A') x.val.right) a := by simp
      rw [h, ← hx, h_x_as_sum]
      simp_rw [map_sum, Derivation.sum_apply, aux_ext_apply, Finset.mul_sum]
      simp_rw [tmul_add, ← Finset.sum_sub_distrib, sum_tmul, ← Finset.sum_add_distrib]
      simp_rw [tmul_smul, smul_tmul']
      abel_nf
      simp_rw [smul_tmul', ← add_tmul, smul_eq_mul]
      conv =>
        lhs
        enter [2, x, 2, 2, 2]
        rw [mul_comm, ← smul_eq_mul, Algebra.ofId_apply, algebraMap_smul]
      simp [mul_comm]
    · simp
    · intros u v hu hv hxu hxv
      rw [lie_add,map_add]
      grind

-- next steps: transfer the Lie algebra structure to Basechange
-- show the other axioms of LieRinehartAlgebra


end
