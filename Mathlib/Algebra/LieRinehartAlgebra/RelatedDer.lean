import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.LieRinehartAlgebra.Semidirect_additions
import Mathlib.RingTheory.Derivation.Lie


section CompatibleDerivations

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {A' : Type*} [CommRing A'] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']

variable (R A A') in
def CompatibleDerivations : LieSubalgebra R  ( (Derivation R A' A') ⊕⁅R⁆ (Derivation R A A)) where
  carrier := { x | (x.left).compAlgebraMapL R A A' A'
    = (Algebra.ofId A A').toLinearMap.compDer (x.right) }
  add_mem' {x y} hx hy  := by simp at hx hy; simp [hx,hy]
  zero_mem' := by simp
  smul_mem'  c x h := by simp at h; simp [h]
  lie_mem' {x y} hx hy := by
    have hxx (a : A) := congrArg (fun f => f a) hx
    have hyy (a : A) := congrArg (fun f => f a) hy
    simp at hxx hyy
    ext z
    simp [Derivation.commutator_apply, hxx, hyy]
end CompatibleDerivations


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
