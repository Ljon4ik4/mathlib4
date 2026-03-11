import Mathlib.Algebra.Lie.BaseChange
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.Lie.SemiDirect

section LieDerivationExtendScalars
open TensorProduct
variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {L : Type*} [LieRing L] [LieAlgebra R L]

variable (L) in
def ExtendDerToLieDer (d : Derivation R A A) : LieDerivation R (A ⊗[R] L) (A ⊗[R] L) where
  toFun := TensorProduct.map d.toLinearMap LinearMap.id
  map_add' := by simp
  map_smul' := by simp
  leibniz' x y := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    refine x.induction_on (by simp) ?_ ?_
    · intros _ l
      refine y.induction_on (by simp) ?_ ?_
      · intros _ l'
        rw [←sub_eq_zero]
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, map_tmul, Derivation.coeFn_coe,
          Derivation.leibniz, smul_eq_mul, LinearMap.id_coe, id_eq, add_tmul]
        rw [←(lie_skew l' l), tmul_neg]
        abel_nf
      · intros _ _ h1 h2
        rw [←sub_eq_zero]
        simp [h1, h2]
        abel_nf
    · intros _ _ h1 h2
      rw [←sub_eq_zero]
      simp [h1, h2]
      abel_nf

@[simp]
lemma ExtendDerToLieDer_apply (d : Derivation R A A) (x : A ⊗[R] L) :
    (ExtendDerToLieDer L d) x = (TensorProduct.map d.toLinearMap LinearMap.id) x := rfl

variable (R A L)
def ExtendDerToLieDerHom : (Derivation R A A) →ₗ⁅R⁆ (LieDerivation R (A ⊗[R] L) (A ⊗[R] L)) where
  toFun := ExtendDerToLieDer L
  map_add' _ _ := by ext _; simp [map_add_left]
  map_smul' _ _ := by ext _; simp [map_smul_left]
  map_lie' {_ _} := by
    ext z
    simp only [ExtendDerToLieDer_apply, Derivation.commutator_coe_linear_map,
      LieDerivation.lie_apply]
    refine z.induction_on (by simp) ?_ ?_
    · intros _ _
      simp [sub_tmul]
    · intros _ _ hx hy
      simp [hx, hy]
      abel_nf

@[simp]
lemma ExtendDerToLieDerHom_apply (d : Derivation R A A) (x : A ⊗[R] L) :
    (ExtendDerToLieDerHom R A L d) x = (TensorProduct.map d.toLinearMap LinearMap.id) x := rfl


end LieDerivationExtendScalars



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

