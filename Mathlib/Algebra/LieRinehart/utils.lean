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
