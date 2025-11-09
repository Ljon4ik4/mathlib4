import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Tower



section CompTriple
/--
helper so lean recognizes that the composition of semilinear maps over algebras is semilinear
in LieRinehart.Hom.comp
-/
instance instCompTriple {R A A' A'' : Type*} [CommRing R] [CommRing A] [Algebra R A]
[CommRing A'] [Algebra R A'] [CommRing A''] [Algebra R A'']
(σ : A →ₐ[R] A') (σ' : A' →ₐ[R] A'') :
RingHomCompTriple σ.toRingHom σ'.toRingHom (σ'.comp σ).toRingHom := ⟨rfl⟩
end CompTriple




section inducedAlgMod
variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {A' : Type*} [CommRing A'] [Algebra R A']


/-- Given an algebra morphism`A →ₐ[R] A'` this creates an alias for `A'` seen as an `A`-module.
The realization of this alias as an A-module is realized by the below instances
-/
def AlgHom.inducedAlgMod (_ : A →ₐ[R] A') : Type _ := A'

section inducedAlgMod
variable {σ : A →ₐ[R] A'}
instance : CommRing (σ.inducedAlgMod) := by
  unfold AlgHom.inducedAlgMod
  exact inferInstance

instance : Algebra R σ.inducedAlgMod := by
  unfold AlgHom.inducedAlgMod
  exact inferInstance

instance : Module A (σ.inducedAlgMod) :=
by simpa [AlgHom.inducedAlgMod] using σ.toAlgebra.toModule

instance : Module A' σ.inducedAlgMod := by exact Semiring.toModule

instance : IsScalarTower R A' σ.inducedAlgMod :=
by exact IsScalarTower.of_commMonoid R A'

instance : SMulCommClass R A' σ.inducedAlgMod := by exact Algebra.to_smulCommClass
instance : SMulCommClass A' A σ.inducedAlgMod :=
  {
    smul_comm:= by
      intros m n a
      simp only [smul_eq_mul, Algebra.mul_smul_comm, AlgHom.toRingHom_eq_coe]
  }


def AlgHom.inducedlinearEquiv (σ : A →ₐ[R] A') :  σ.inducedAlgMod ≃ₗ[A'] A' :=
  {
  toFun    := id,
  invFun   := id,
  map_add' := fun _ _ => rfl,
  map_smul' := fun _ _ => rfl,
  }

variable {σ : A →ₐ[R] A'}

@[simp]
lemma induced_linear_equiv_is_id (x : σ.inducedAlgMod) : σ.inducedlinearEquiv (x)=x := rfl

@[simp]
lemma mul_is_just_action (a : A) (x : σ.inducedAlgMod) :
a • x = σ.inducedlinearEquiv.symm (σ (a)) * x := rfl

def AlgHom.toFullyLinearMap (σ : A →ₐ[R] A') : A →ₗ[A] σ.inducedAlgMod:=
{
  toFun := σ
  map_add' := by exact fun x y ↦ map_add σ x y
  map_smul' := by
    unfold AlgHom.inducedAlgMod
    intros m x
    simp only [smul_eq_mul, map_mul, RingHom.id_apply]
    exact rfl
}

@[simp]
lemma lem_toFullyLinearMap (a : A) : σ.toFullyLinearMap (a) = σ (a) := by rfl



end inducedAlgMod

section RestrictScalarsAlgtoRing
variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {A' : Type*} [CommRing A'] [Algebra R A']
variable {L : Type*} [AddCommMonoid L] [Module R L] [Module A L] [IsScalarTower R A L]
variable {L' : Type*} [AddCommMonoid L'] [Module R L'] [Module A' L'] [IsScalarTower R A' L']
variable {σ : A →ₐ[R] A'}

/-- Interpreting a `σ:A→ₐ[R]A'` semilinear map as an `R`-linear map.
-/
def LinearMap.RestrictScalarsAlgtoRing (f : L →ₛₗ[σ.toRingHom] L') :
( L →ₗ[R] L') :=
  {
    f.toAddMonoidHom with
    map_smul' := by
      intros r x
      simp
      simp only [←(IsScalarTower.algebraMap_smul (R:=R) (A:=A) (M:=L) r x)]
      calc f ((algebraMap R A) r • x)
        = σ.toRingHom ((algebraMap R A) r) • f (x) :=
          by rw [f.map_smulₛₗ (R:= A) (c := (algebraMap R A) r) (M:=L) (x:=x)]
        _ = r • f (x) := by simp
  }

@[simp]
lemma lem_RestrictedScalarhom (f : L →ₛₗ[σ.toRingHom] L') (x : L) :
f  x= (f.RestrictScalarsAlgtoRing) x
:= by rfl

end RestrictScalarsAlgtoRing
