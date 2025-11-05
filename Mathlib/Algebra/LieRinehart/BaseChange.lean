import Mathlib.Algebra.LieRinehart.Defs_implicitanchor
import Mathlib.LinearAlgebra.TensorProduct.Basic

variable {R : Type} [CommRing R]

variable {A : Type} [CommRing A] [Algebra R A]
variable {A' : Type} [CommRing A'] [Algebra R A']
variable (σ : A →ₐ[R] A')

variable {L : Type} [LieRing L] [LieAlgebra R L] [Module A L] [IsScalarTower R A L]


--instance instModule {S : Type*} [Semiring S] [Module S M] [SMulCommClass R S M]
--    [SMulCommClass S A M] : Module S (Derivation R A M) :=
--  Function.Injective.module S coeFnAddMonoidHom coe_injective coe_smul

instance : SMulCommClass R A' σ.inducedAlgMod := by exact Algebra.to_smulCommClass
instance : SMulCommClass A' A σ.inducedAlgMod :=
  {
    smul_comm:= by
      intros m n a
      simp only [smul_eq_mul, Algebra.mul_smul_comm, AlgHom.toRingHom_eq_coe]
  }


/-- Given a derivation d from `A'` to `A'`, obtain a derivation from `A` to `A'` by
precomposing with an algebra homomorphism `σ:A→ A'`. the inducedAlgMod is there to make it possible
to see `A'` as an `A`-algebra via `σ`.
-/
def precompder (d : Derivation R A' A') : Derivation R A σ.inducedAlgMod :=
{
  toLinearMap :=
    (σ.inducedlinearEquiv.symm.toLinearMap.restrictScalars (R:=R)).comp (d.comp σ.toLinearMap)
  map_one_eq_zero' := by simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, Derivation.coeFn_coe, AlgHom.coe_toLinearMap, Function.comp_apply, map_one,
    Derivation.map_one_eq_zero, map_zero]
  leibniz' := by
    intros a b
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      Derivation.coeFn_coe, AlgHom.coe_toLinearMap, Function.comp_apply, map_mul,
      Derivation.leibniz, smul_eq_mul, map_add]
    rfl
  }

def procompdermorph : Derivation R A' A' →ₗ[A'] Derivation R A (σ.inducedAlgMod) :=
{
  toFun := fun d↦precompder (R:=R) (A':=A') (σ:=σ) d
  map_add' := by
    intros x y
    rfl
  map_smul' := by
    intros m x
    simp only [RingHom.id_apply]
    rfl
}






--plan:
--`done`show that σ induces an (A'-linear) map from Der(A'A') to Der(A,A')
--show that there is an (A'-linear?) map A'⨂A L → Der(A,A')
-- take their pullback, and show it is LR over A' most properties should be automatic, the difficult
-- bit should be the Lie bracket. This follows the preprint 'Sheaves of LieRinehart algebras'



--instance pullback (σ L ρ) [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [Module A L]
--[LieAlgebra R L] [IsScalarTower R A L] [CommRing A'] [Algebra R A'] :
--LieRinehartAlgebra R A' (TensorProduct R A L) := {}
-- Module.compHom A' σ.toRingHom
