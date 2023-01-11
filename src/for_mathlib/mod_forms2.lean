/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

import algebra.direct_sum.ring
import number_theory.modular
import analysis.complex.upper_half_plane.functions_bounded_at_infty
import number_theory.modular_forms.basic

open_locale complex_conjugate upper_half_plane

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

local notation `GL(` n `, ` R `)`⁺ := matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)` := matrix.special_linear_group (fin n) R

open modular_form
open cusp_form
open slash_invariant_form
open complex

noncomputable theory

/--The upper half space as a subset of `ℂ` which is convenient sometimes.-/
def upper_half_plane.upper_half_space := {z : ℂ | 0 <  z.im}

lemma upper_half_plane_is_open: is_open upper_half_plane.upper_half_space  :=
is_open.preimage complex.continuous_im is_open_Ioi

local notation `ℍ'`:= (⟨upper_half_plane.upper_half_space , upper_half_plane_is_open⟩: topological_space.opens ℂ)

section graded_ring

namespace modular_form

open modular_form

variables (F : Type*) (Γ : subgroup SL(2, ℤ)) (k : ℤ)

/-cast for modular forms, which is useful for removing `heq`'s. -/
def mcast {a b : ℤ} {Γ : subgroup SL(2, ℤ)} (h : a = b) (f : modular_form Γ a) :
  (modular_form Γ b) :=
{ to_fun := (f : ℍ → ℂ),
  slash_action_eq' := by {intro A, have := f.slash_action_eq' A, convert this, exact h.symm,},
  holo' := f.holo',
  bdd_at_infty' := by {intro A, convert f.bdd_at_infty' A, exact h.symm }}

lemma type_eq {a b : ℤ} (Γ : subgroup SL(2, ℤ)) (h : a = b) :
  (modular_form Γ a) = (modular_form Γ b) :=
begin
  induction h,
  refl,
end

lemma cast_eq_mcast {a b : ℤ} {Γ : subgroup SL(2, ℤ)} (h : a = b) (f : modular_form Γ a) :
  cast (type_eq Γ h) f = mcast h f :=
begin
  induction h,
  ext1,
  refl,
end

lemma heq_one_mul (k : ℤ) {Γ : subgroup SL(2, ℤ)} (f : modular_form Γ k) :
  (1 : modular_form Γ 0).mul f == f :=
begin
   apply heq_of_cast_eq (type_eq Γ (zero_add k).symm).symm,
    funext,
    rw [cast_eq_mcast, mcast, mul],
    simp only [one_coe_eq_one, one_mul],
    ext1,
    refl,
    simp only [zero_add]
end

lemma heq_mul_one (k : ℤ) {Γ : subgroup SL(2, ℤ)} (f : modular_form Γ k) :
  f.mul (1 : modular_form Γ 0) == f :=
begin
      apply heq_of_cast_eq (type_eq Γ (add_zero k).symm).symm,
      funext,
      rw [cast_eq_mcast, mcast, mul],
      simp only [one_coe_eq_one, mul_one],
      ext1,
      refl,
      simp only [add_zero]
end

lemma heq_mul_assoc {a b c : ℤ} (f : modular_form Γ a) (g : modular_form Γ b)
  (h : modular_form Γ c) : (f.mul g).mul h ==  f.mul (g.mul h) :=
begin
  apply heq_of_cast_eq (type_eq Γ (add_assoc a b c)),
  rw [cast_eq_mcast, mcast],
  ext1,
  simp only [mul_coe, pi.mul_apply, ←mul_assoc],
  refl,
end

lemma heq_mul_comm (a b : ℤ) (f : modular_form Γ a) (g : modular_form Γ b) : f.mul g == g.mul f :=
begin
  apply heq_of_cast_eq (type_eq Γ (add_comm a b)),
  rw [cast_eq_mcast, mcast],
  ext1,
  simp only [mul_coe, pi.mul_apply, mul_comm],
  refl,
end

instance graded_mod_ring (Γ : subgroup SL(2, ℤ)) : direct_sum.gcomm_ring (λ k, modular_form Γ k) :=
{ mul := λ k_1, λ k_2, λ f g, f.mul g,
  one := 1,
  one_mul := by {intro f,
    rw [graded_monoid.ghas_one.to_has_one, graded_monoid.ghas_mul.to_has_mul],
    apply sigma.ext,
    { simp only [zero_add] },
    { simp only [submodule.coe_mk, one_mul, heq_one_mul] }},
  mul_one := by {intro f,
    rw [graded_monoid.ghas_one.to_has_one, graded_monoid.ghas_mul.to_has_mul],
    apply sigma.ext,
    { simp only [add_zero] },
    { simp only [submodule.coe_mk, mul_one, heq_mul_one]}},
  mul_assoc := by {intros f g h,
    rw graded_monoid.ghas_mul.to_has_mul,
    apply sigma.ext,
    { apply add_assoc },
    { simp only [submodule.coe_mk, heq_mul_assoc] }},
  mul_zero := by {intros i j f, ext1, simp,},
  zero_mul := by {intros i j f, ext1, simp,},
  mul_add := by {intros i j f g h,
    ext1,
    simp only [pi.mul_apply, mul_add, mul_coe, add_apply],},
  add_mul := by {intros i j f g h,
    ext1,
    simp only [add_mul, mul_coe, pi.mul_apply, add_apply],},
  mul_comm := by {intros f g,
    rw graded_monoid.ghas_mul.to_has_mul,
    apply sigma.ext,
    { apply add_comm },
    { apply heq_mul_comm }},
  gnpow_zero' := by {intro f,
    apply sigma.ext,
    repeat {refl}},
  gnpow_succ' := by {intros n f,
    rw graded_monoid.ghas_mul.to_has_mul,
    apply sigma.ext,
    repeat {refl}},
  nat_cast := λ n, n • (1 : (modular_form Γ 0)),
  nat_cast_zero := by {simp},
  nat_cast_succ := by {intro n, simp only [add_smul, one_nsmul, add_right_inj], refl,},
  int_cast := λ n, n • (1 : (modular_form Γ 0)),
  int_cast_of_nat := by {simp},
  int_cast_neg_succ_of_nat := by {intro , apply _root_.neg_smul }}

end modular_form

end graded_ring

section petersson_product

def pet (f g : ℍ → ℂ) (k : ℤ) : ℍ → ℂ :=
  λ z, conj (f z) * (g z) * (upper_half_plane.im z) ^ k

def pet_self (f : ℍ → ℂ) (k : ℤ) : ℍ → ℝ := λ z, complex.abs(f z) ^ 2 * (upper_half_plane.im z) ^ k

lemma pet_is_invariant  {k : ℤ} {Γ : subgroup SL(2, ℤ)}
  (f : slash_invariant_form Γ k) ( g : slash_invariant_form Γ k) {γ : SL(2, ℤ)}
  (hγ : γ ∈ Γ) (z : ℍ) : pet f g k (γ • z) = pet f g k z :=
begin
  dsimp only [pet],
  let D := upper_half_plane.denom γ z, have hD : (D ≠ 0) := by apply upper_half_plane.denom_ne_zero,
  have mod_g : g (γ • z) = D ^ k * g z,
  { have tt := (slash_action_eqn' k Γ g) ⟨γ, hγ⟩ z,
    dsimp only [upper_half_plane.denom] at *, exact tt, },
  have mod_f : conj (f (γ • z)) = (conj D) ^ k * conj (f z),
  { have tt : f (γ • z) = D ^ k * f z := by apply (slash_action_eqn' k Γ f) ⟨γ, hγ⟩ z,
    rw [tt, star_ring_end_apply, star_ring_end_apply, star_mul',  ←star_zpow₀], refl, },
  rw [mod_f, mod_g], ring_nf,
  suffices : ↑((γ • z).im) = ↑(upper_half_plane.im z) / D / (conj D),
  { rw this, simp only [upper_half_plane.coe_im, div_zpow],
    have : ↑(z.im) ^ k / D ^ k / conj D ^ k * g z * D ^ k * conj (f z) * conj D ^ k =
    ↑(z.im) ^ k / D ^ k / conj D ^ k  * D ^ k * conj D ^ k * g z * conj (f z) := by ring,
    rw this, congr' 2,
    have h1 : D ^ k ≠ 0 := zpow_ne_zero _ hD,
    have h2 : conj D ^ k ≠ 0,
    { apply zpow_ne_zero, rw [star_ring_end_apply, star_ne_zero], exact hD },
    field_simp [h1, h2], ring },
  have : (((γ • z) : ℍ) : ℂ).im = (upper_half_plane.im z) / complex.norm_sq D,
  { rw [upper_half_plane.coe_im],
    convert upper_half_plane.im_smul_eq_div_norm_sq γ z,
    simp only [upper_half_plane.coe_im, coe_coe,
      matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
      matrix.special_linear_group.coe_matrix_coe, int.coe_cast_ring_hom],
    suffices : ((↑ₘγ).map coe).det = (1:ℝ), { rw this, simp only [one_mul], },
    have : (↑ₘγ).map (coe : ℤ → ℝ) = ↑ₘ(γ : SL(2, ℝ)),
    { simp only [matrix.special_linear_group.coe_matrix_coe, int.coe_cast_ring_hom], },
    rw this, apply matrix.special_linear_group.det_coe },
  apply_fun (coe : ℝ → ℂ) at this,
  convert this,
  simp only [upper_half_plane.coe_im, complex.of_real_div],
  rw [div_div, mul_conj],
end

lemma pet_self_eq (f : ℍ → ℂ) (k : ℤ) (z : ℍ): pet_self f k z = re (pet f f k z) :=
begin
  dsimp only [pet, pet_self],
  simp_rw [star_ring_end_apply],
  have : (star (f z) * f z * ↑((z).im) ^ k).re = (star (f z) * f z).re * (↑z.im) ^ k,
  { conv begin to_lhs,congr,  rw mul_comm, end,
    rw [←of_real_zpow, of_real_mul_re, mul_comm],
    simp only [upper_half_plane.coe_im, is_R_or_C.coe_real_eq_id, id.def], },
  rw this, congr,
  rw [mul_comm, ←norm_sq_eq_abs, norm_sq],
  simp only [monoid_with_zero_hom.coe_mk, is_R_or_C.star_def, mul_re, conj_re, conj_im,
    mul_neg, sub_neg_eq_add],
end

lemma pet_self_is_invariant {k : ℤ} {Γ : subgroup SL(2, ℤ)}
  ( f : slash_invariant_form Γ k) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (z : ℍ) :
  pet_self f k (γ • z) = pet_self f k z :=
begin
  rw [pet_self_eq, pet_self_eq], congr' 1, exact pet_is_invariant f f hγ z,
end

end petersson_product
