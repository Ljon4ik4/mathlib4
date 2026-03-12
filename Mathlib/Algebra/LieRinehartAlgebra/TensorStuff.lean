import Mathlib


variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (N : Type*) [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

open TensorProduct


abbrev span_of_smul_tmul :=
  (Submodule.span A {x | ∃ (a : A) (m: M) (n : N), (a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) = x})


#check Submodule.mkQ

def map_to_quot : M →ₗ[A] N →ₗ[A] ((M⊗[R] N) ⧸ (span_of_smul_tmul R A M N)) where
  toFun m := {
    toFun n := (span_of_smul_tmul R A M N).mkQ (m⊗ₜn)
    map_add' _ _ := by simp [tmul_add]
    map_smul' _ _ := by
      rw [RingHom.id_apply, ←LinearMap.map_smul, ←sub_eq_zero, ← LinearMap.map_sub,smul_tmul']
      refine LinearMap.mem_ker.mp ?_
      simp only [Submodule.ker_mkQ]
      rw [←neg_mem_iff]
      refine Submodule.mem_span_of_mem ?_
      simp}
  map_add' _ _ := by
    ext _
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_tmul,map_add]
  map_smul' a m := by
    ext n
    simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
      LinearMap.smul_apply]
    rw [←LinearMap.map_smul, ←sub_eq_zero, ← LinearMap.map_sub,smul_tmul']
    simp

abbrev tens_to_quot := TensorProduct.lift (map_to_quot R A M N)

-- now I should show that the span is in the kernel of  (mapOfCompatibleSMul' A R M N), and
-- use this to obtain a map quot to tens and then put them together to have an iso between
-- the tensor product an the quotient. This then can be used to prove the lemma below





lemma CompatibleSMul_ker_eq_span : (mapOfCompatibleSMul' A R M N).ker = (span_of_smul_tmul R A M N)
    := by
  refine Eq.symm (Submodule.span_eq_of_le (mapOfCompatibleSMul' A R M N).ker ?_ ?_)
  · sorry
  · sorry
