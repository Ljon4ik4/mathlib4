import Mathlib


variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable (N : Type*) [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]

open TensorProduct


abbrev span_of_smul_tmul :=
  (Submodule.span A {x | ∃ (a : A) (m: M) (n : N), (a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) = x})

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

omit [IsScalarTower R A N] in
@[simp]
lemma map_to_quot_apply (m : M) (n : N) : map_to_quot R A M N m n = ⟦m⊗ₜn⟧ := by rfl



abbrev tens_to_quot := TensorProduct.lift (map_to_quot R A M N)

omit [IsScalarTower R A N] in
@[simp]
lemma tens_to_quot_apply (m : M) (n : N) : tens_to_quot R A M N (m⊗ₜn) = ⟦m⊗ₜn⟧ := by rfl


lemma compose_eq_mkQ :(tens_to_quot R A M N) ∘ₗ (mapOfCompatibleSMul' A R M N)
    = (span_of_smul_tmul R A M N).mkQ := by
  ext m n
  simp [mapOfCompatibleSMul', Submodule.Quotient.mk''_eq_mk]


lemma span_in_ker : (span_of_smul_tmul R A M N) ≤ (mapOfCompatibleSMul' A R M N).ker := by
  rw [LinearMap.le_ker_iff_comp_subtype_eq_zero]
  let S := {x | ∃ (a : A) (m: M) (n : N), (a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) = x}
  have hS : span_of_smul_tmul R A M N = Submodule.span A S := rfl
  rw [Submodule.linearMap_eq_zero_iff_of_eq_span (S:=S) (hV:=hS)]
  simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply, Subtype.forall]
  intro x hx
  rw [Set.mem_setOf] at hx
  obtain ⟨a, m, n, heq⟩ := hx
  rw [← heq]
  simp [mapOfCompatibleSMul', smul_tmul]

abbrev quot_to_tens := Submodule.liftQ  (span_of_smul_tmul R A M N) (mapOfCompatibleSMul' A R M N)
  (span_in_ker R A M N)

@[simp]
lemma quot_to_tens_apply (m : M) (n : N) : quot_to_tens R A M N ⟦m⊗ₜn⟧ = m⊗ₜn := by rfl


def quot_equi_tens : (M ⊗[R] N ⧸ (span_of_smul_tmul R A M N)) ≃ₗ[A] M ⊗[A] N where
  toLinearMap := quot_to_tens R A M N
  invFun := tens_to_quot R A M N
  left_inv := by
    rw [Function.leftInverse_iff_comp]
    ext z
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Function.comp_apply, id_eq]
    obtain ⟨y, hy⟩ := Quotient.exists_rep z
    obtain ⟨S, h⟩ := exists_finset (y)
    simp_rw [← hy, h]
    clear h hy
    simp_rw [Submodule.Quotient.mk''_eq_mk, ← Submodule.mkQ_apply, map_sum, Submodule.mkQ_apply,
      ← Submodule.Quotient.mk''_eq_mk]
    simp only [quot_to_tens_apply, tens_to_quot_apply]
  right_inv := by
    rw [Function.rightInverse_iff_comp]
    ext z
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Function.comp_apply, id_eq]
    obtain ⟨S, h⟩ := exists_finset (z)
    simp_rw [h]
    simp

lemma CompatibleSMul_ker_eq_span : (mapOfCompatibleSMul' A R M N).ker = (span_of_smul_tmul R A M N)
    := by
  rw [← LinearEquiv.ker_comp (quot_equi_tens R A M N).symm (mapOfCompatibleSMul' A R M N)]
  have h : (quot_equi_tens R A M N).symm.toLinearMap = tens_to_quot R A M N := rfl
  rw [h, compose_eq_mkQ]
  simp
