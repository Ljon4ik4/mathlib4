import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.LieRinehart.utils


class LeibnizAction (L A M : Type*) [Bracket L M] [Bracket L A] [AddCommGroup M] [SMul A M]
where leibniz : ∀ (x : L) (a : A) (m : M),  ⁅x, a•m⁆ = a•⁅x, m⁆ + ⁅x, a⁆•m

namespace LeibnizAction
variable {L A M : Type*} [Bracket L M] [Bracket L A] [AddCommGroup M] [SMul A M]
[LeibnizAction L A M]

@[simp]
lemma lem_leibniz (x : L) (a : A) (m : M) : ⁅x, a•m⁆ = a•⁅x, m⁆ + ⁅x, a⁆•m := by apply leibniz x a m
end LeibnizAction

class LeftLinBracket (L A M : Type*) [Bracket L M] [Bracket L A] [SMul A M] [SMul A L]
where linearity : ∀ (a : A) (x : L) (m : M),  ⁅a•x, m⁆ = a•⁅x, m⁆

namespace LeftLinBracket
variable {L A M : Type*} [Bracket L M] [Bracket L A] [SMul A M] [SMul A L] [LeftLinBracket L A M]

@[simp]
lemma lem_linearity (a : A) (x : L) (m : M) :  ⁅a•x, m⁆ = a•⁅x, m⁆ := by apply linearity a x m

end LeftLinBracket





/-- A Lie-Rinehart algebra over a commutative Ring `R` is a commutative `R`-algebra `A` together
with an `A`-module `L` equipped with a Lie bracket and a Lie algebra and module homomorphism
`ρ:L→ Der_R(A,A)` to the derivations of `A`, such that the Leibniz rule `⁅x,a•y⁆=a•⁅x,y⁆+ρ(x)(a)•y`
is satisfied.
In this version of the definition we are encoding the anchor implictly by a Lie action of L on A.
The anchor is later derived as a consequence of the definition.
-/
class LieRinehartAlgebra (R A L : Type*) [CommRing R] [CommRing A] [Algebra R A]
[LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L] [LieRingModule L A]
[LieModule R L A] [LeibnizAction L A A] [LeibnizAction L A L] [LeftLinBracket L A A]



section instDerivationLieRinehartAlgebra

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]

instance instDerLieRingModule : LieRingModule (Derivation R A A) A where
bracket:= fun X a ↦X (a)
add_lie:= by simp
lie_add:= by simp
leibniz_lie:=by exact fun x y m ↦ Eq.symm (add_eq_of_eq_sub rfl)

instance : LieModule R (Derivation R A A) A where
smul_lie := by exact fun t x m ↦ rfl
lie_smul := by
  intros r X a
  exact X.map_smul_of_tower r a

@[simp]
lemma bracketmul (X : Derivation R A A) (a : A) : ⁅ X ,a ⁆ = X (a) := by rfl

instance : LeibnizAction (Derivation R A A) A A where
leibniz:=by
  intros X a m
  simp
  exact CommMonoid.mul_comm m (X a)

instance : LeibnizAction (Derivation R A A) A (Derivation R A A) where
leibniz:= by
  intros X a Y
  ext b
  simp
  repeat rw [Derivation.commutator_apply]
  simp
  ring

instance : LeftLinBracket (Derivation R A A) A A where
linearity := by simp

/-- The derivations of an Algebra form a LieRinehartAlgebra themselves
-/
instance : (LieRinehartAlgebra R A (Derivation R A A)) :={}

end instDerivationLieRinehartAlgebra


namespace LieRinehartAlgebra

/-- A homomorphism of Lie-Rinehart algebras `(A,L)`, `(A',L')` consists of an algebra map `σ:A→ A'`
and an `A`-linear map `F: L→L'` which is also a Lie algebra homomorphism and is compatible
with the anchors.
-/
structure Hom {R A A' : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing A'] [Algebra R A']
(σ : A →ₐ[R] A') (L L' : Type*) [LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L]
[LieRingModule L A] [LieModule R L A] [LeibnizAction L A A] [LeibnizAction L A L]
[LeftLinBracket L A A] [LieRinehartAlgebra R A L] [LieRing L'] [Module A' L'] [LieAlgebra R L']
[IsScalarTower R A' L'] [LieRingModule L' A'] [LieModule R L' A']
[LeibnizAction L' A' A'] [LeibnizAction L' A' L'] [LeftLinBracket L' A' A']
[LieRinehartAlgebra R A' L']
extends LinearMap (R := A) (S := A') σ.toRingHom L L' where
map_lie' : ∀ (x y : L), toLinearMap ⁅x,y⁆ = ⁅ toLinearMap x, toLinearMap y ⁆
anchorcomp: ∀ (a : A) (l : L), σ (⁅l, a⁆)  =  ⁅(toLinearMap l), (σ a)⁆

@[inherit_doc]
notation:25 L " →ₗ⁅" σ:25 "⁆ " L':0 => LieRinehartAlgebra.Hom σ L L'


variable {R A L : Type*} [CommRing R] [CommRing A] [Algebra R A]
[LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L] [LieRingModule L A]
[LieModule R L A] [LeibnizAction L A A] [LeibnizAction L A L] [LeftLinBracket L A A]
[LieRinehartAlgebra R A L]

variable {A' L' : Type*} [CommRing A'] [Algebra R A']
[LieRing L'] [Module A' L'] [LieAlgebra R L'] [IsScalarTower R A' L'] [LieRingModule L' A']
[LieModule R L' A'] [LeibnizAction L' A' A'] [LeibnizAction L' A' L']
[LeftLinBracket L' A' A']
[LieRinehartAlgebra R A' L']

variable {A'' L'' : Type*} [CommRing A''] [Algebra R A'']
[LieRing L''] [Module A'' L''] [LieAlgebra R L''] [IsScalarTower R A'' L''] [LieRingModule L'' A'']
[LieModule R L'' A''] [LeibnizAction L'' A'' A''] [LeibnizAction L'' A'' L'']
[LeftLinBracket L'' A'' A'']
[LieRinehartAlgebra R A'' L'']

variable (σ : A →ₐ[R] A')
variable (σ' : A' →ₐ[R] A'')

--TODO: IS This something we want?
instance : CoeFun (L →ₗ⁅σ⁆ L') (fun _ => L → L') := ⟨fun f => f.toLinearMap⟩

@[simp]
lemma lem_map_lie (f : L →ₗ⁅σ⁆ L') (x y : L) : f (⁅x,y⁆) = ⁅ f (x), f (y) ⁆ :=
by exact f.map_lie' x y

@[simp]
lemma lem_anchorcomp (f : L →ₗ⁅σ⁆ L') (l : L) (a : A ): σ (⁅l, a⁆)  =  ⁅f (l), σ (a)⁆ :=
by exact f.anchorcomp a l


/-- Recovers the Lie algebra morphism underlying a Lie-Rinehart algbera homomorophism
-/
def Hom.toLieHom (f : L →ₗ⁅σ⁆ L') : L →ₗ⁅R⁆ L' := {
  toLinearMap := f.RestrictScalarsAlgtoRing,
  map_lie' := by
    apply f.map_lie'
  }

/-- The module homomorphism and the Lie algebra homomorphism undelying a Lie Rinehart homomorphism
are the same function
-/
@[simp]
theorem ModHomeqLieHom (f : L →ₗ⁅σ⁆ L') (x : L) : f.toLinearMap  x= (f.toLieHom) x
:= by rfl


/-- The composition of Lie Rinehart algebra homomorphisms is again a homomorphism
-/
def comp (f : L →ₗ⁅σ⁆ L') (g : L' →ₗ⁅σ'⁆ L'') : L →ₗ⁅(AlgHom.comp σ' σ)⁆ L'' :=
  { g.toLinearMap.comp f.toLinearMap with
    map_lie' := by
      intros x y
      simp
      repeat rw [ModHomeqLieHom]
      simp
    anchorcomp := by
      intros l a
      dsimp
      repeat rw [←lem_anchorcomp]
  }


/-- The way to see an element of `L` as a derivation of `A`.
Later this will become simply `ρ(a)`
-/
def derivOf (x : L) : Derivation R A A :=
Derivation.mk'
  ((LieModule.toEnd R L A) x)
  (by
    intros a b
    dsimp
    repeat rw [←smul_eq_mul]
    rw [LeibnizAction.lem_leibniz x a b]
    simp
    exact CommMonoid.mul_comm ⁅x, a⁆ b)


@[simp]
lemma lem_derivof {R A L : Type*} [CommRing R] [CommRing A] [Algebra R A]
[LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L] [LieRingModule L A]
[LieModule R L A] [LeibnizAction L A A] [LeibnizAction L A L] [LeftLinBracket L A A]
[LieRinehartAlgebra R A L]
(x : L) (a : A) : (derivOf (R:=R) x) a = ⁅ x, a ⁆ := by rfl

/-- The anchor of a given LieRinehart algebra `L` over `A` interpreted as a LieRinehart morphism to
the module of derivations of `A`.
-/
def ρ (L : Type*) [LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L]
[LieRingModule L A] [LieModule R L A] [LeibnizAction L A A] [LeibnizAction L A L]
[LeftLinBracket L A A] [LieRinehartAlgebra R A L] : L →ₗ⁅AlgHom.id R A⁆ (Derivation R A A) := {
  toFun := derivOf
  map_add' := by
    intros x y
    ext a
    simp_all
  map_smul' := by
    intros a X
    ext b
    simp_all
  map_lie' := by
    intros x y
    ext a
    simp_all
    rw [Derivation.commutator_apply]
    simp_all
  anchorcomp := by simp
}


end LieRinehartAlgebra
