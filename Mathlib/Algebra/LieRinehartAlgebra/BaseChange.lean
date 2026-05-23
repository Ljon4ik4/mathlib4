import Mathlib.Algebra.LieRinehartAlgebra.Defs
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.Lie.Derivation.BaseChange
import Mathlib.Algebra.Lie.SemiDirect


section

/-
# Todos:
- `TensorProduct.AlgebraTensorModule.ker_mapOfCompatibleSMul` is a bad namespace it should be just
int the `TensorProduct` namespace, as indicated in the doc of the surjectivity of the map
-/

section
variable {R : Type*} {A : Type*} {M : Type*}
variable [CommSemiring R] [CommSemiring A] [AddCommMonoid M]
variable [Algebra R A]
variable [Module R M] [Module A M]


theorem Derivation.coe_sum_linear_maps {ι : Type*} (t : Finset ι) (f : ι → (Derivation R A M)) :
    ↑(∑ i ∈ t, f i) = ∑ i ∈ t, (f i : A →ₗ[R] M) :=
  _root_.map_sum
    (show AddMonoidHom (Derivation R A M) (A →ₗ[R] M)
      from { toFun := toLinearMap,
             map_zero' := rfl
             map_add' := fun _ _ => rfl }) _ _

theorem Derivation.sum_apply {ι : Type*} (t : Finset ι) (f : ι → (Derivation R A M)) (a : A) :
    (∑ i ∈ t, f i) a = ∑ i ∈ t, (f i a) := by
  rw [← Derivation.coeFn_coe, Derivation.coe_sum_linear_maps, LinearMap.sum_apply]
  simp

variable {B : Type*} [CommSemiring B] [Algebra R B] [Algebra A B] [Module B M]
[IsScalarTower R A B] [IsScalarTower A B M] [IsScalarTower R B M]
theorem Derivation.leibniz_smul (d : Derivation R B M) (a : A) (b : B) : d (a • b) =
    a • (d b) + b • (d.compAlgebraMapL R A B M a) := by
  simp [Algebra.smul_def]
end

namespace Equiv

section

variable {R α β : Type*} [CommRing R] (e : α ≃ β)

/-- Transfer `LieRing` across an `Equiv` -/
protected abbrev lieRing [LieRing β] : LieRing α where
  __ := e.addCommGroup
  bracket x y := e.symm ⁅e x, e y⁆
  add_lie _ _ _ := by simp [add_def]
  lie_add _ _ _ := by simp [add_def]
  lie_self _ := by simp [zero_def]
  leibniz_lie _ _ _ := by simp [add_def]

lemma bracket_def [LieRing β] (x y : α) :
    letI := Equiv.lieRing e
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

/-- Transfer `LieAlgebra` across an `Equiv` -/
protected abbrev lieAlgebra (e : α ≃ β) [LieRing β] [LieAlgebra R β] :
    letI := Equiv.lieRing e
    letI := Equiv.module (R := R) e
    LieAlgebra R α :=
  letI := Equiv.lieRing e
  letI := Equiv.module (R:= R) e
  { lie_smul _ _ _ := by simp [Equiv.smul_def, Equiv.bracket_def] }

end

section
variable {α β : Type*} [AddCommGroup α] [LieRing β]

/-- Transfer `LieRing` across an `AddEquiv` -/
protected abbrev lieRing' (e : α ≃+ β) : LieRing α where
  bracket x y := e.symm ⁅e x, e y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp

lemma bracket_def' (e : α ≃+ β) (x y : α) :
    letI := Equiv.lieRing' e
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

variable {R : Type*} [CommRing R] [Module R α] [LieAlgebra R β]

/-- Transfer `LieAlgebra` across a `LinearEquiv` -/
protected abbrev lieAlgebra' (e : α ≃ₗ[R] β) :
    letI := Equiv.lieRing' e.toAddEquiv
    LieAlgebra R α :=
  letI := Equiv.lieRing' e.toAddEquiv
  { lie_smul _ _ _ := by simp [bracket_def'] }


end



end Equiv





namespace LieRinehartAlgebra

section

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {A' : Type*} [CommRing A'] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']

variable {L : Type*} [LieRing L] [Module A L] [LieRingModule L A] [LieRinehartRing A L]
    [LieAlgebra R L] [LieRinehartAlgebra R A L]

open TensorProduct

def relative_anchor : A'⊗[A] L →ₗ[A'] Derivation R A A' :=
  LinearMap.liftBaseChange (A := A') (((Algebra.ofId A A').toLinearMap.compDer)
  ∘ₗ (LieRinehartAlgebra.anchor R A L).toLinearMap')

lemma relative_anchor_apply (a : A') (l : L) (z : A) : relative_anchor (R := R) (a⊗ₜl) (z) =
    ⁅l, z⁆ • a := by
  simp [Algebra.smul_def, mul_comm]
  rfl

variable (R A A' L) in
def Basechange : Submodule A'  ((A' ⊗[A] L) × (Derivation R A' A')) where
  carrier := {x | relative_anchor x.1 = Derivation.compAlgebraMapL R A A' A' x.2}
  zero_mem' := by simp
  add_mem' {_ _} _ _ := by simp_all
  smul_mem' _ _ _ := by simp_all

lemma finset_mem (S : Finset (A' × L)) (v : Derivation R A' A') :
    (∑ i ∈ S, i.1 ⊗ₜ i.2 , v) ∈ (Basechange R A A' L)
    ↔ ∀ (z : A), ∑ i ∈ S, ⁅i.2, z⁆ • i.1 = v.compAlgebraMap A z := by
  constructor
  · intro h z
    replace h := DFunLike.congr_fun h z
    simp_rw [map_sum, Derivation.sum_apply, relative_anchor_apply] at h
    exact h
  · intro h
    ext z
    simp_rw [map_sum, Derivation.sum_apply, relative_anchor_apply, h]
    rfl

-- this is an $A'$-module, this is helpful in a proof later
variable (R A A' L) in
private abbrev preBasechange :
    LieSubalgebra R  ((A' ⊗[R] L) ⋊⁅(Lie.Derivation.ofDerivation L)⁆ (Derivation R A' A')) where
  carrier := {x |
    (Prod.map (TensorProduct.mapOfCompatibleSMul A R A A' L) id)
    (LieAlgebra.SemiDirectSum.toProd x) ∈ Basechange R A A' L}
  zero_mem' := by rfl
  add_mem' {_ _} hx hy := by
    convert_to _ = _
    replace hx : _ = _ := hx
    replace hy : _ = _ := hy
    simp_all
  smul_mem' _ _ h:= by
    convert_to _ = _
    replace h : _ = _ := h
    simp_all
  lie_mem' {x y} hx hy := by
    replace hx : _ ∈ (Basechange R A A' L) := hx
    obtain ⟨Sx, h_x_as_sum⟩ := exists_finset (x.left)
    simp_rw [LieAlgebra.SemiDirectSum.toProd_apply, Prod.map_apply, id_eq, h_x_as_sum, map_sum,
      mapOfCompatibleSMul_tmul, finset_mem, Derivation.compAlgebraMap_apply] at hx
    replace hy : _ ∈ (Basechange R A A' L) := hy
    obtain ⟨Sy, h_y_as_sum⟩ := exists_finset (y.left)
    simp_rw [LieAlgebra.SemiDirectSum.toProd_apply, Prod.map_apply, id_eq, h_y_as_sum, map_sum,
      mapOfCompatibleSMul_tmul, finset_mem, Derivation.compAlgebraMap_apply] at hy
    ext z
    rw [← sub_eq_zero]
    simp [h_x_as_sum, h_y_as_sum]
    simp [Derivation.commutator_apply, sum_lie_sum, Derivation.sum_apply, relative_anchor_apply]
    simp [← hx, ← hy, Derivation.leibniz_smul, sub_smul, Finset.sum_add_distrib]
    ring_nf
    simp_rw [Finset.mul_sum, (Finset.sum_comm (s:=Sy) (t := Sx)), ← Finset.sum_sub_distrib,
      Algebra.mul_smul_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero ?_
    intro _ _
    refine Finset.sum_eq_zero ?_
    intro _ _
    ring_nf

private instance : Module A' ((A' ⊗[R] L) ⋊⁅(Lie.Derivation.ofDerivation L)⁆ (Derivation R A' A'))
  := (LieAlgebra.SemiDirectSum.toProd).module (R:= A')

private instance : IsScalarTower R A'
    ((A' ⊗[R] L) ⋊⁅(Lie.Derivation.ofDerivation L)⁆ (Derivation R A' A'))
  := (LieAlgebra.SemiDirectSum.toProd).isScalarTower (M := R) (N := A')

--this should have a better name, and it should be improved to be A' linear, but for that A'-module
--  of prebasechange is needed
variable (R A A' L) in
private abbrev pr : (preBasechange R A A' L) →ₗ[R] (Basechange R A A' L) where
  toFun x := ⟨ (Prod.map (TensorProduct.mapOfCompatibleSMul A R A A' L) id)
    (LieAlgebra.SemiDirectSum.toProd x), by have hx : (_ = _) := x.property; simpa using hx⟩
  map_add'  := by simp
  map_smul' := by simp

private lemma pr_surjective : Function.Surjective (pr R A A' L) := by
  intro y
  let x1 := Function.surjInv (mapOfCompatibleSMul_surjective A R A A' L) y.val.1
  have hx : ((mapOfCompatibleSMul A R A A' L) x1) = y.val.1 := by simp [x1, Function.surjInv_eq]
  use ⟨⟨x1, y.val.2⟩, by simp [hx]⟩
  simp [pr, hx]

variable (R A A' L) in
private abbrev basechange_ker : LieIdeal R (preBasechange R A A' L) where
  __ := LinearMap.ker (pr R A A' L)
  lie_mem := by
    rintro ⟨x, hx : _ = _⟩ ⟨m, _⟩ hm
    -- first we simplify and apply the condition on `m`
    have ⟨hmleft, hmright⟩: (m.left ∈ (mapOfCompatibleSMul A R A A' L).ker) ∧ m.right = 0 :=
      by simp_all
    rw [TensorProduct.AlgebraTensorModule.ker_mapOfCompatibleSMul] at hmleft
    convert_to (mapOfCompatibleSMul A R A A' L) ⁅x.left, m.left⁆ +
      (mapOfCompatibleSMul A R A A' L) ((LinearMap.rTensor L ↑x.right) m.left) = 0
    · simp [hmright, Lie.Derivation.ofDerivation_apply]
    refine Submodule.closure_induction (by simp) (by grind only [= map_add, lie_add]) ?_ hmleft
    -- since the set generating the span is multiplicatively closed we may assume `a = 1`
    intro a
    wlog ha : a = 1 generalizing a with H
    · rintro q ⟨b,b',l,hq⟩
      simp only [forall_eq, one_smul] at H
      refine H (a • q) ⟨b, a • b', l, ?_⟩
      simp_rw [hq.symm,  smul_sub, smul_tmul']
      rw [← sub_eq_zero, smul_comm]
      abel_nf
    rintro y ⟨b, a', l, hy⟩
    rw [ha, one_smul, hy.symm]
    -- now we rewrite the target s.th. we can replace x.right
    simp only [lie_sub, map_sub, LinearMap.rTensor_tmul, Derivation.coeFn_coe,
      mapOfCompatibleSMul_tmul, tmul_smul]
    simp at hx
    simp_rw [Derivation.leibniz_smul, hx.symm, add_tmul, smul_tmul', add_sub_cancel_left]
    refine x.left.induction_on (by simp) ?_ ?_
    · intros c z
      rw [mapOfCompatibleSMul_tmul, relative_anchor_apply]
      simp [tmul_add, smul_tmul']
      ring_nf
      abel_nf
    · rintro p q hp hq
      simp_rw [add_lie, map_add, Derivation.add_apply, smul_add, add_tmul]
      grind

-- better name?
private noncomputable abbrev iso : ((preBasechange R A A' L) ⧸ (basechange_ker R A A' L))
    ≃ₗ[R] (Basechange R A A' L)
  := LinearMap.quotKerEquivOfSurjective (pr R A A' L) (pr_surjective)

-- this might be replaceable by something standard, no need for extra lemma
private lemma iso_comp (x : preBasechange R A A' L) : (pr R A A' L x) =
    iso (LieSubmodule.Quotient.mk x) := by rfl

noncomputable instance : LieRing (Basechange R A A' L) where
  bracket x y := iso ⁅ iso.symm x, iso.symm y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _  := by simp
  leibniz_lie _ _ _ := by simp

private lemma bracket_unfold (x y : (Basechange R A A' L)) : ⁅x, y⁆ = iso ⁅ iso.symm x, iso.symm y⁆
  := rfl

-- there could also be a new def of a better pr, moreover, it is A'linear
private lemma pr_lie (x y : preBasechange R A A' L) :
    ⁅(pr R A A' L) x, (pr R A A' L) y⁆ = (pr R A A' L) (⁅x, y⁆) := by
  simp_rw [bracket_unfold, iso_comp, LinearEquiv.symm_apply_apply, LieSubmodule.Quotient.mk_bracket]

-- I don't know what the useful framing is, possibly everything would work better with Multisets
-- rather than finite sets, then at least gettin the description of $ay$ from the one of $y$ would
-- be easier
lemma bracket_formula (x y : Basechange R A A' L) (Sx Sy : Finset (A' × L))
    (hx : ∑ i ∈ Sx, i.1 ⊗ₜ i.2 = x.val.1) (hy : ∑ i ∈ Sy, i.1 ⊗ₜ i.2 = y.val.1) :
    ⁅x, y⁆.val = ((∑ i ∈  Sx, ∑ j ∈ Sy, (i.1*j.1) ⊗ₜ ⁅i.2, j.2⁆) + (∑ j ∈ Sy, x.val.2 (j.1)⊗ₜj.2)
      - (∑ i ∈ Sx, y.val.2 (i.1)⊗ₜi.2), ⁅x.val.2, y.val.2⁆) := by
  let ix : preBasechange R A A' L := ⟨⟨∑ i ∈ Sx, i.1 ⊗ₜ i.2, x.val.2⟩, by simp_all⟩
  have hix : x = (pr R A A' L) ix := by simp [ix, hx]
  let iy : preBasechange R A A' L := ⟨⟨∑ i ∈ Sy, i.1 ⊗ₜ i.2, y.val.2⟩, by simp_all⟩
  have hiy : y = (pr R A A' L) iy := by simp [iy, hy]
  have ih : ⁅ix, iy⁆.val = ⟨(∑ i ∈  Sx, ∑ j ∈ Sy, (i.1*j.1) ⊗ₜ ⁅i.2, j.2⁆)
      + (∑ j ∈ Sy, x.val.2 (j.1)⊗ₜj.2) - (∑ i ∈ Sx, y.val.2 (i.1)⊗ₜi.2), ⁅x.val.2, y.val.2⁆⟩ := by
    simp [ix, iy, LieAlgebra.SemiDirectSum.lie_eq_mk, sum_lie_sum]
  conv_lhs =>
    rw [hix, hiy, iso_comp, iso_comp, bracket_unfold, LinearEquiv.symm_apply_apply]
    rw [LinearEquiv.symm_apply_apply, ← LieSubmodule.Quotient.mk_bracket, ← iso_comp]
  simp [ih]

noncomputable instance : LieAlgebra R (Basechange R A A' L) where
  lie_smul _ _ _ := by simp [bracket_unfold]

-- this is not really used, it might be related/ replace pr_lie
private noncomputable def iso' : ((preBasechange R A A' L) ⧸ (basechange_ker R A A' L))
    ≃ₗ⁅R⁆ (Basechange R A A' L) where
  __ := iso
  map_lie' {_ _} := by simp [bracket_unfold]

def snd' : (Basechange R A A' L) →ₗ⁅R⁆ Derivation R A' A' where
  __ := (LinearMap.snd R (A' ⊗[A] L) (Derivation R A' A')) ∘ₗ ((Basechange R A A' L).subtype)
  map_lie' {x y} := by
    have h_iso (x y : (preBasechange R A A' L) ⧸ (basechange_ker R A A' L)) :
      (iso ⁅x, y⁆).val.2 = ⁅(iso x).val.2, (iso y).val.2⁆ := by
      induction x using Quotient.inductionOn
      induction y using Quotient.inductionOn
      rfl
    simp [bracket_unfold, h_iso]

lemma snd'_apply (x : Basechange R A A' L) : snd' x = x.val.2 := rfl

lemma snd'_smul_apply (a : A') (x : Basechange R A A' L) : snd' (a • x) = a • snd' x := rfl

noncomputable instance : LieRingModule  (Basechange R A A' L) A' where
  bracket x a := (snd' x) a
  add_lie _ _ := by simp
  lie_add _ _ := by simp
  leibniz_lie _ _ _ := by
    rw [LieHom.map_lie, Derivation.commutator_apply]
    simp

lemma lbracket_apply (x : (Basechange R A A' L)) (a : A') : ⁅x, a⁆ = (snd' x) a := rfl

noncomputable instance : LieRinehartRing A' (Basechange R A A' L) where
  lie_smul_eq_mul' _ _ x := by
    obtain ⟨_, _⟩ := x
    simp
    rfl
  leibniz_mul_right' x a b := by simp [lbracket_apply, mul_comm]
  leibniz_smul_right' x y a := by
    refine Subtype.ext_iff.mpr ?_
    refine Prod.ext ?_ ?_
    · simp only [Submodule.coe_add, SetLike.val_smul, Prod.fst_add, Prod.smul_fst]
      obtain ⟨x', hx⟩ := pr_surjective x
      obtain ⟨y', hy⟩ := pr_surjective y
      simp_rw [←hx, ←hy]
      simp_rw [pr_lie]
      -- this is a place where A'-linearity of pr would be useful
      sorry
    · simp [← snd'_apply, snd'_smul_apply]
      rfl


end
end LieRinehartAlgebra
end
