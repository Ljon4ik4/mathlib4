import Mathlib.Algebra.LieRinehart.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Prod



section relative_derivations
variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {A' : Type*} [CommRing A'] [Algebra R A']
variable {σ : A →ₐ[R] A'}

/-- Given a derivation d from `A'` to `A'`, obtain a derivation from `A` to `A'` by
precomposing with an algebra homomorphism `σ:A→ A'`. the inducedAlgMod is there to make it possible
to see `A'` as an `A`-algebra via `σ`.
-/
def AlgHom.precompose_derivation (σ : A →ₐ[R] A') (d : Derivation R A' A') :
Derivation R A σ.inducedAlgMod :=
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


/-- Given an algebra morphism  `σ:A→ A'`, this yields the induced morphism from derivations of `A'`
to derivations of the `A`-module `A'`, precomposing with an algebra homomorphism `σ:A→ A'`.
the inducedAlgMod is there to make it possible to see `A'` as an `A`-algebra via `σ`.
-/
def AlgHom.derivation_pullback (σ : A →ₐ[R] A') :
 Derivation R A' A' →ₗ[A'] Derivation R A (σ.inducedAlgMod) :=
{
  toFun := fun d↦σ.precompose_derivation d
  map_add' := by
    intros x y
    rfl
  map_smul' := by
    intros m x
    simp only [RingHom.id_apply]
    rfl
}
end relative_derivations

-- Todo: restructure and clean up from here on


variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {A' : Type*} [CommRing A'] [Algebra R A']
variable {σ : A →ₐ[R] A'}


variable {L : Type} [LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L]
[LieRingModule L A] [LieModule R L A] [LeibnizAction L A A] [LeibnizAction L A L]
[LieRinehartAlgebra R A L]


instance : Module A'  (TensorProduct A σ.inducedAlgMod L) := by
  unfold AlgHom.inducedAlgMod
  exact inferInstance



def anchor_eval_pointwise (a : σ.inducedAlgMod) : L →ₗ[A] (Derivation R A σ.inducedAlgMod):=
{
  toFun:= fun l ↦ a• (σ.toFullyLinearMap.compDer (LieRinehartAlgebra.derivOf l))
  map_add' := by
    intros x y
    ext b
    simp only [Derivation.coe_smul, Derivation.coe_comp, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Derivation.coeFn_coe, Pi.smul_apply, Function.comp_apply,
      LieRinehartAlgebra.lem_derivof, add_lie, lem_toFullyLinearMap, map_add, smul_eq_mul,
      Derivation.coe_add, Pi.add_apply]
    exact LeftDistribClass.left_distrib a (σ ⁅x, b⁆) (σ ⁅y, b⁆)
  map_smul' := by
    intros b x
    ext c
    simp only [Derivation.coe_smul, Derivation.coe_comp, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Derivation.coeFn_coe, Pi.smul_apply, Function.comp_apply,
      LieRinehartAlgebra.lem_derivof, lem_toFullyLinearMap, smul_eq_mul, RingHom.id_apply,
      mul_is_just_action]
    rw [LieRinehartAlgebra.left_linearity R]
    unfold AlgHom.inducedlinearEquiv
    simp only [map_mul, LinearEquiv.coe_symm_mk', id_eq]
    ring
}


def anchor_eval : σ.inducedAlgMod →ₗ[A] L →ₗ[A] (Derivation R A σ.inducedAlgMod):=
{
  toFun := anchor_eval_pointwise (σ:=σ)
  map_add' := by
    intros x y
    ext c d
    simp only [LinearMap.add_apply, Derivation.coe_add, Pi.add_apply]
    unfold anchor_eval_pointwise
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Derivation.coe_smul, Derivation.coe_comp,
      LinearMap.coe_comp, LinearMap.coe_restrictScalars, Derivation.coeFn_coe, Pi.smul_apply,
      Function.comp_apply, LieRinehartAlgebra.lem_derivof, lem_toFullyLinearMap, smul_eq_mul]
    exact RightDistribClass.right_distrib x y (σ ⁅c, d⁆)
  map_smul' := by
    intros m x
    ext c d
    unfold anchor_eval_pointwise
    simp only [mul_is_just_action, LinearMap.coe_mk, AddHom.coe_mk, Derivation.coe_smul,
      Derivation.coe_comp, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Derivation.coeFn_coe,
      Pi.smul_apply, Function.comp_apply, LieRinehartAlgebra.lem_derivof, lem_toFullyLinearMap,
      smul_eq_mul, RingHom.id_apply, LinearMap.smul_apply]
    exact mul_assoc (σ.inducedlinearEquiv.symm (σ m)) x (σ ⁅c, d⁆)
}



def otherrelevantmorphforpullback (σ : A →ₐ[R] A') :
(TensorProduct A σ.inducedAlgMod L) →ₗ[A] Derivation R A σ.inducedAlgMod :=
TensorProduct.lift (anchor_eval (σ:=σ))

def improvedotherrelevantmorphforpullback (σ : A →ₐ[R] A') :
(TensorProduct A σ.inducedAlgMod L) →ₗ[A'] Derivation R A σ.inducedAlgMod :=
{
  toFun := otherrelevantmorphforpullback (σ)
  map_add' := by exact fun x y ↦ LinearMap.map_add (otherrelevantmorphforpullback σ) x y
  map_smul' := by
    intros m x
    simp only [RingHom.id_apply]
    induction x using TensorProduct.induction_on with
    | zero =>
      simp only [smul_zero, map_zero]
    | tmul x y =>
      calc (otherrelevantmorphforpullback σ) (m • x ⊗ₜ[A] y)
      = (otherrelevantmorphforpullback σ) ((m • x) ⊗ₜ[A] y) := by exact rfl
      _ = m • (otherrelevantmorphforpullback σ) (x ⊗ₜ[A] y) := by
        ext a
        unfold otherrelevantmorphforpullback
        simp only [smul_eq_mul, TensorProduct.lift.tmul, Derivation.coe_smul, Pi.smul_apply]
        unfold anchor_eval
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        unfold anchor_eval_pointwise
        simp only [LinearMap.coe_mk, AddHom.coe_mk, Derivation.coe_smul, Derivation.coe_comp,
          LinearMap.coe_comp, LinearMap.coe_restrictScalars, Derivation.coeFn_coe, Pi.smul_apply,
          Function.comp_apply, LieRinehartAlgebra.lem_derivof, lem_toFullyLinearMap, smul_eq_mul]
        exact mul_assoc m x (σ ⁅y, a⁆)
    | add y z h1 h2 =>
      simp only [smul_add, map_add]
      rw [h1,h2]
}


#synth Module σ.inducedAlgMod
((Derivation R σ.inducedAlgMod σ.inducedAlgMod) × (TensorProduct A σ.inducedAlgMod L))

--#check improvedotherrelevantmorphforpullback σ

--def K : (Derivation R σ.inducedAlgMod σ.inducedAlgMod)
-- × (TensorProduct A σ.inducedAlgMod L)→ₗ[σ.inducedAlgMod] Derivation R A σ.inducedAlgMod  := LinearMap.coprod (R:=A')
-- (improvedotherrelevantmorphforpullback (L:=L) σ) σ.derivation_pullback


--plan:
--`done`show that σ induces an (A'-linear) map from Der(A'A') to Der(A,A')
--`done`show that there is an (A'-linear) map A'⨂A L → Der(A,A')
-- take their pullback, and show it is LR over A' most properties should be automatic, the difficult
-- bit should be the Lie bracket. This follows the preprint 'Sheaves of LieRinehart algebras'
