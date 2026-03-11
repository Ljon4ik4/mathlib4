import Mathlib.Algebra.LieRinehartAlgebra.RelatedDer
import Mathlib.Algebra.LieRinehartAlgebra.Defs
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib





section
variable {R : Type*} {A : Type*} {M : Type*}
variable [CommSemiring R] [CommSemiring A] [AddCommMonoid M]
variable [Algebra R A]
variable [Module A M] [Module R M]


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



end





section

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {A' : Type*} [CommRing A'] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']

variable {L : Type*} [LieRing L] [Module A L] [LieRingModule L A] [LieRinehartRing A L]
    [LieAlgebra R L] [LieRinehartAlgebra R A L]

open TensorProduct



private abbrev aux : A' ⊗[R] L →ₗ[R] Derivation R A A':=
  (TensorProduct.lift ((LinearMap.lsmul A' (Derivation R A A')).restrictScalars₁₂ R R))
  ∘ₗ (((((Algebra.ofId A A').toLinearMap.compDer).restrictScalars R)
  ∘ₗ (LieRinehartAlgebra.Hom.anchor R A L).toLinearMap).lTensor A')

variable (R A A' L) in
def PrePull : LieSubalgebra R  ((A' ⊗[R] L) ⋊⁅(ExtendDerToLieDerHom R A' L)⁆ (Derivation R A' A'))
    where
  carrier := {x | aux (x.left) = (Derivation.compAlgebraMapL R A A' A') x.right }
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
    have aux_ext_apply (a : A') (l : L) (z : A) : aux (R:=R) (a⊗ₜl) (z) =
      a •  (Algebra.ofId A A') ⁅ l, z⁆ := by simp [LieRinehartAlgebra.Hom.anchor]
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
    simp_rw [LieAlgebra.SemiDirectSum.lie_eq_mk, CompL_apply, Derivation.commutator_apply]
    simp_rw [h_x_as_sum, h_y_as_sum, ← hx,← hy, sum_lie_sum, map_sum, ExtendDerToLieDerHom_apply]
    simp_rw [map_tmul, LinearMap.id_apply]
    simp_rw [map_sub,map_add, map_sum, Derivation.sub_apply, Derivation.add_apply]
    simp_rw [Derivation.sum_apply, aux_ext_apply]
    simp_rw [LieAlgebra.ExtendScalars.bracket_tmul, aux_ext_apply]
    simp_rw [smul_eq_mul, Derivation.leibniz, ← hx,←hy, Finset.smul_sum]
    simp only [lie_lie, Algebra.ofId_apply, map_sub, Derivation.coeFn_coe, smul_eq_mul]
    rw [← sub_eq_zero]
    repeat simp_rw [Finset.sum_add_distrib]
    simp_rw [← sub_sub, ← sub_add, ← sub_sub]
    repeat simp_rw [mul_sub]
    repeat simp_rw [Finset.sum_sub_distrib]
    simp_rw [(Finset.sum_comm (s:=Sy) (t := Sx))]
    ring_nf
    grind



end
