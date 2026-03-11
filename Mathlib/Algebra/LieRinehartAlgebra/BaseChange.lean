import Mathlib.Algebra.LieRinehartAlgebra.Derivation_additions
import Mathlib.Algebra.LieRinehartAlgebra.Defs
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness




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
      a •  (Algebra.ofId A A') ⁅l, z⁆ := by simp [LieRinehartAlgebra.Hom.anchor]
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
    simp_rw [h_x_as_sum, h_y_as_sum, sum_lie_sum, map_sum, ExtendDerToLieDerHom_apply, map_tmul,
      LinearMap.id_apply, map_sub,map_add, map_sum, Derivation.sub_apply, Derivation.add_apply,
      Derivation.sum_apply, LieAlgebra.ExtendScalars.bracket_tmul, aux_ext_apply, lie_lie, map_sub,
      smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    -- make them cancel
    rw [← sub_eq_zero]
    simp_rw [← sub_sub, ← sub_add, ← sub_sub, (Finset.sum_comm (s:=Sy) (t := Sx))]
    simp only [Algebra.ofId_apply, Derivation.coeFn_coe]
    ring_nf
    grind



end
