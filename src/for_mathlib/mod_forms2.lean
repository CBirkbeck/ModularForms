/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import algebra.module.submodule
import mod_forms.upper_half_plane
import linear_algebra.general_linear_group
import linear_algebra.special_linear_group
--import algebra.direct_sum.ring
import mod_forms.modular
import mod_forms.mfderiv
import geometry.manifold.mfderiv


/-!
# Modular forms

This file defines modular forms and proves some basic properties about them.

We begin by defining the `slash_k` operator on the space of functions `ℍ → ℂ` and from this
define the notion of weakly modular form.

We then define `bounded_at_infinity` and `zero_at_infinity`. Finally we construct the vector
space of modular forms and prove that the product of two modular forms is a modular form
(of higher weight).
-/

open complex

open_locale topological_space manifold upper_half_plane

noncomputable theory

local notation `ℍ'`:=(⟨upper_half_plane.upper_half_space ,
 upper_half_plane.upper_half_plane_is_open⟩: topological_space.opens ℂ)

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

local notation `GL(` n `, ` R `)`⁺:= matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)`:= matrix.special_linear_group (fin n) R

variable (M : GL(2, ℝ)⁺)

def slash_k : ℤ → GL(2, ℝ)⁺ → (ℍ → ℂ) → (ℍ → ℂ) := λ k γ f,
  (λ (x : ℍ), f (γ • x) * (((↑ₘ γ).det ) : ℝ)^(k-1) * (((↑ₘ γ 1 0 : ℝ) * x +(↑ₘ γ 1 1 : ℝ))^k)⁻¹)

namespace modular_forms

variables (Γ : subgroup SL(2,ℤ)) (C : GL(2, ℝ)⁺) (k: ℤ) (f : (ℍ → ℂ))

localized "notation  f  ` ∣[`:100 k `]`:0 γ :100 := slash_k k γ f" in modular_form

lemma slash_k_right_action (k : ℤ) (A B : GL(2, ℝ)⁺) (f : ℍ → ℂ ) :
  (f ∣[k] A) ∣[k] B = f ∣[k] (A * B) :=
begin
  simp_rw slash_k,
  ext1,
  have e1 := upper_half_plane.denom_cocycle A B x,
  have e3 : (A * B) • x = A • B • x := (upper_half_plane.mul_smul' A B x),
  simp only [upper_half_plane.num, upper_half_plane.denom, of_real_mul, subgroup.coe_mul, coe_coe,
    upper_half_plane.coe_smul, units.coe_mul, matrix.mul_eq_mul, matrix.det_mul,
    upper_half_plane.smul_aux, upper_half_plane.smul_aux', subtype.coe_mk] at *,
  rw [e1, e3],
  ring_nf,
  have aux1 : ∀ (a b c d e : ℂ), (e ^ k)⁻¹ * a ^ (k - 1) * (b ^ k)⁻¹ * c ^ (k - 1) * d =
    ((b * e) ^ k)⁻¹ * (c * a) ^ (k - 1) * d := by { intros, simp_rw [mul_zpow₀, mul_inv₀], ring, },
  simp_rw aux1,
end

lemma slash_k_add (k : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
  (f + g) ∣[k] A = (f ∣[k] A) + (g ∣[k] A) :=
begin
  simp only [slash_k, pi.add_apply, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe,
    coe_coe],
  ext1,
  simp only [pi.add_apply],
  ring,
end

lemma slash_k_mul_one (k : ℤ) (f : ℍ → ℂ) : (f ∣[k] 1) = f :=
begin
 simp_rw slash_k,
 ext1,
 simp,
end

/- FIXME FIXME -- this is hideous, I cannot find a way of deducing this from the above;
lean refuses to identify the two 1's. -/
lemma slash_k_mul_one_SL2 (k : ℤ) (f : ℍ → ℂ) : (f ∣[k] (1 : SL(2, ℤ))) = f :=
begin
  simp_rw slash_k,
  simp only [coe_coe, matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
    matrix.special_linear_group.coe_matrix_coe, matrix.special_linear_group.coe_one,
    int.coe_cast_ring_hom, matrix.map_one, int.cast_eq_zero, int.cast_one,
    matrix.det_one, of_real_one, one_zpow₀, mul_one, matrix.one_apply_ne, ne.def,
    fin.one_eq_zero_iff, nat.one_ne_zero, not_false_iff, of_real_zero, zero_mul,
    matrix.one_apply_eq, zero_add, inv_one],
  ext1, congr' 1, ext1,
  rw [upper_half_plane.coe_smul], simp,
end

lemma smul_slash_k (k : ℤ) (A : GL(2, ℝ)⁺) (f : ℍ → ℂ) (c : ℂ) : (c • f) ∣[k] A = c • (f ∣[k] A):=
begin
  ext1,
  simp_rw slash_k,
  simp only [algebra.id.smul_eq_mul, matrix.general_linear_group.coe_det_apply, pi.smul_apply,
    subtype.val_eq_coe, coe_coe],
  ring,
end

lemma slash_k_mul (k1 k2 : ℤ) (A : GL(2, ℝ)⁺) (f g : ℍ → ℂ) :
  (f * g) ∣[k1+k2] A = (((↑ₘ A).det) : ℝ) • (f ∣[k1] A) * (g ∣[k2] A) :=
begin
  ext1,
  simp [slash_k, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe, coe_coe,
  ←mul_assoc],
  rw  pi.mul_apply,
  have h1 : ((((↑ₘ A).det) : ℝ) ^ (k1 + k2 - 1) : ℂ) =
  (((↑ₘ A).det) : ℝ) * (((↑ₘ A).det) : ℝ) ^ (k1 - 1) * (((↑ₘ A).det) : ℝ) ^ (k2 - 1),
  { simp only [mul_assoc, matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe, coe_coe],
    rw [←zpow_add₀, ←zpow_one_add₀],
    ring_exp,
    all_goals
    { have hd := (matrix.mem_GL_pos _).1 A.2,
      simp only [subtype.val_eq_coe, matrix.general_linear_group.coe_det_apply] at hd,
      norm_cast,
     apply ne_of_gt hd,}, },
  simp only [matrix.general_linear_group.coe_det_apply, subtype.val_eq_coe, coe_coe] at h1,
  rw h1,
  have h2 : ((((↑ₘA 1 0 : ℝ) : ℂ) * (x : ℂ) + ((↑ₘA 1 1 : ℝ)))^(k1 + k2))⁻¹ =
  ((((↑ₘA 1 0 : ℝ) : ℂ) * (x : ℂ) + ((↑ₘA 1 1 : ℝ)))^k1)⁻¹ *
  ((((↑ₘA 1 0 : ℝ) : ℂ) * (x : ℂ) + ((↑ₘA 1 1 : ℝ)))^k2)⁻¹,
  { simp_rw ← mul_inv₀,
    simp only [coe_coe, inv_inj],
    apply zpow_add₀ (upper_half_plane.denom_ne_zero A x), },
  simp only [coe_coe] at h2,
  rw h2,
  ring,
end

lemma slash_k_mul_SL2 (k1 k2 : ℤ) (A : SL(2, ℤ)) (f g : ℍ → ℂ) :
  (f * g) ∣[k1 + k2] A = (f ∣[k1] A) * (g ∣[k2] A) :=
begin
  have : (((↑ₘ(A : GL(2,ℝ)⁺)).det): ℝ) = 1,
  { simp only [coe_coe,matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
  matrix.special_linear_group.det_coe], },
  simp_rw [slash_k_mul, this, one_smul],
end

/-- The space of weakly modular functions of weight `k` and level `Γ` -/
def weakly_modular_submodule (k : ℤ) (Γ : subgroup SL(2, ℤ)): submodule ℂ (ℍ → ℂ) :=
{ carrier := {f : ℍ → ℂ | ∀ (γ : Γ), f ∣[k] γ = f },
  zero_mem' := by
  { simp only [set.mem_set_of_eq, coe_coe],
    simp_rw slash_k,
    simp only [forall_const, zero_mul, pi.zero_apply],
    refl, },
  add_mem' := by
  { intros f g hf hg γ,
    rw [slash_k_add k γ f g, hf γ, hg γ], },
  smul_mem' := by
  { intros c f hf γ,
    have : (c • f) ∣[k] γ = c • (f ∣[k] γ ) := by apply smul_slash_k,
    rw (hf γ) at this,
    apply this, } }

/-- A function `f : ℍ → ℂ` is weakly modular, of level `Γ` and weight `k ∈ ℤ`, iff for every matrix
 `γ ∈ Γ` we have `f(γ • z)= (c * z + d)^k f(z)` where `γ= ![![a, b], ![c, d]]`, acting on `ℍ` via
 Moebius trainsformations. -/
@[simp]
lemma wmodular_mem' (k : ℤ) (Γ : subgroup SL(2, ℤ)) (f : ℍ → ℂ) :
  f ∈ (weakly_modular_submodule k Γ) ↔
  ∀ γ : Γ, ∀ z : ℍ, f (γ • z) = ((↑ₘγ 1 0 : ℝ) * z + (↑ₘγ 1 1 : ℝ)) ^ k * f z :=
begin
  dsimp only [weakly_modular_submodule], split,
  { intros h1 γ z,
    rw [←(by simp_rw h1 γ : (f ∣[k] γ) z = f z), slash_k, mul_comm],
    have h55 := inv_mul_cancel (zpow_ne_zero k (upper_half_plane.denom_ne_zero γ z)),
    simp only [upper_half_plane.denom, upper_half_plane.subgroup_to_sl_moeb,
      upper_half_plane.sl_moeb, coe_coe, matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
      matrix.special_linear_group.coe_matrix_coe, int.coe_cast_ring_hom, matrix.map_apply,
      of_real_int_cast] at *,
    rw [mul_assoc, h55, ←int.coe_cast_ring_hom, ←matrix.special_linear_group.coe_matrix_coe,
      matrix.special_linear_group.det_coe ((γ : SL(2, ℤ) ) : SL(2, ℝ))],
    simp only [of_real_one, one_zpow₀, mul_one] },
  { intros hf γ,
    simp_rw slash_k,
    ext1,
    rw [←upper_half_plane.subgroup_moeb, (hf γ x), mul_comm],
    have h55 := inv_mul_cancel (zpow_ne_zero k (upper_half_plane.denom_ne_zero γ x)),
    simp_rw upper_half_plane.denom at *,
    simp only [matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix, coe_coe,
      matrix.special_linear_group.coe_matrix_coe, int.coe_cast_ring_hom, matrix.map_apply,
      of_real_int_cast] at h55,
    simp only [coe_coe, matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
      matrix.map_apply, of_real_int_cast],
    rw (matrix.special_linear_group.det_coe ((γ : SL(2, ℤ) ) : SL(2, ℝ))),
    simp only [matrix.special_linear_group.coe_matrix_coe, int.coe_cast_ring_hom, matrix.map_apply,
      of_real_int_cast, of_real_one, one_zpow₀, mul_one],
    simp_rw [←mul_assoc, h55],
    simp },
end

lemma mul_modular {k_1 k_2 : ℤ} {Γ : subgroup SL(2, ℤ)} {f g : ℍ → ℂ}
  (hf : f ∈ weakly_modular_submodule k_1 Γ) (hg : g ∈ weakly_modular_submodule k_2 Γ) :
  f * g ∈ weakly_modular_submodule (k_1 + k_2) Γ :=
begin
  simp only [wmodular_mem', pi.mul_apply, coe_coe] at *,
  intros γ z,
  rw [(hf γ z), (hg γ z)],
  have pown := zpow_add₀ (upper_half_plane.denom_ne_zero (γ : GL(2, ℝ)⁺) z) k_1 k_2,
  simp only [upper_half_plane.denom, coe_fn_coe_base, ne.def,
    matrix.general_linear_group.coe_fn_eq_coe, coe_coe] at pown,
  rw pown,
  ring,
end

/-! Conditions at cusps, defined using filters -/

def at_I_inf := filter.at_top.comap upper_half_plane.im

lemma at_I_inf_mem (S : set ℍ) : S ∈ at_I_inf ↔ (∃ A : ℝ, ∀ z : ℍ, A ≤ im z → z ∈ S) :=
begin
  simp only [at_I_inf, filter.mem_comap', filter.mem_at_top_sets, ge_iff_le, set.mem_set_of_eq,
    upper_half_plane.coe_im],
  split,
  { intro h, cases h with a h,
    exact ⟨a, (λ z hz, by { apply h (im z) hz, refl })⟩ },
  { intro h, cases h with A h,
    refine ⟨A, (λ b hb x hx, by { apply (h x), rw hx, exact hb })⟩ }
end

def is_bound_at_inf (f : ℍ → ℂ) : Prop := asymptotics.is_O f (1 : ℍ → ℂ) at_I_inf

def is_zero_at_inf (f : ℍ → ℂ) : Prop := filter.tendsto f at_I_inf (𝓝 0)

lemma zero_form_is_zero_at_inf : is_zero_at_inf 0 := tendsto_const_nhds

lemma is_zero_at_inf_is_bound (f : ℍ → ℂ) (hf : is_zero_at_inf f) : is_bound_at_inf f :=
begin
  apply asymptotics.is_O_of_div_tendsto_nhds, { simp, }, { convert hf, ext1, simp, }
end

lemma zero_form_is_bound : is_bound_at_inf 0 := is_zero_at_inf_is_bound _ zero_form_is_zero_at_inf

def zero_at_infty_submodule : submodule ℂ (ℍ → ℂ) :=
{ carrier := is_zero_at_inf,
  zero_mem' := zero_form_is_zero_at_inf,
  add_mem' := by { intros a b ha hb, simpa using ha.add hb },
  smul_mem' := by { intros c f hf, simpa using hf.const_mul c }, }

def bounded_at_infty_submodule : submodule ℂ (ℍ → ℂ) :=
{ carrier := is_bound_at_inf,
  zero_mem' := zero_form_is_bound,
  add_mem' := by { intros f g hf hg, simpa using hf.add hg, },
  smul_mem' := by { intros c f hf, simpa using hf.const_mul_left c }, }

lemma prod_of_bound_is_bound {f g : ℍ → ℂ} (hf : is_bound_at_inf f) (hg : is_bound_at_inf g) :
  is_bound_at_inf (f * g) := by simpa using hf.mul hg

@[simp]lemma bound_mem (f : ℍ → ℂ) :
  is_bound_at_inf f ↔ ∃ (M A : ℝ), ∀ z : ℍ, A ≤ im z → abs (f z) ≤ M :=
begin
  simp_rw [is_bound_at_inf, asymptotics.is_O_iff, filter.eventually, at_I_inf_mem],
  simp,
end

/--The extension of a function from `ℍ` to `ℍ'`-/
def hol_extn (f : ℍ → ℂ) : ℍ' → ℂ := λ (z : ℍ'), (f (z : ℍ))

instance : has_coe (ℍ → ℂ) (ℍ' → ℂ) := ⟨λ f, hol_extn f ⟩

/-- A function `f : ℍ → ℂ` is a modular form of level `Γ` and weight `k ∈ ℤ` if it is holomorphic,
 weakly modular and bounded at infinity -/
structure is_modular_form_of_lvl_and_weight (Γ : subgroup SL(2,ℤ)) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  (hol      : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑f : ℍ' → ℂ))
  (transf   : f ∈ weakly_modular_submodule k Γ)
  (infinity : ∀ (A : SL(2, ℤ)), is_bound_at_inf (f ∣[k] A))

/-- A function `f : ℍ → ℂ` is a cusp form of level one and weight `k ∈ ℤ` if it is holomorphic,
 weakly modular, and zero at infinity -/
structure is_cusp_form_of_lvl_and_weight (Γ : subgroup SL(2,ℤ)) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  (hol      : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (λ (z : ℍ'), (f (z : ℍ))))
  (transf   : f ∈ weakly_modular_submodule k Γ)
  (infinity : ∀ (A : SL(2, ℤ)), is_zero_at_inf (f ∣[k] A) )

/-- The zero modular form is a cusp form-/
lemma zero_cusp_form : is_cusp_form_of_lvl_and_weight Γ k 0 :=
{ hol := mdifferentiable_zero,
  transf := (weakly_modular_submodule k Γ).zero_mem',
  infinity := by
  { intro A,
    convert zero_form_is_zero_at_inf,
    rw slash_k, simp only [pi.zero_apply, zero_mul], refl, } }

lemma is_modular_form_of_lvl_and_weight_of_is_cusp_form_of_lvl_and_weight {Γ k f}
  (h : is_cusp_form_of_lvl_and_weight Γ k f) : is_modular_form_of_lvl_and_weight Γ k f :=
{ hol      := h.1,
  transf   := h.2,
  infinity := λ A, is_zero_at_inf_is_bound _ (h.3 A) }

 /-- The zero modular form is a modular form-/
lemma zero_mod_form : is_modular_form_of_lvl_and_weight Γ k 0 :=
begin
  apply_rules [is_modular_form_of_lvl_and_weight_of_is_cusp_form_of_lvl_and_weight, zero_cusp_form],
end

/-- This is the space of modular forms of level `Γ` and weight `k`-/
def space_of_mod_forms_of_weight_and_level (Γ : subgroup SL(2, ℤ)) (k : ℤ) : submodule ℂ (ℍ → ℂ) :=
{ carrier  := is_modular_form_of_lvl_and_weight Γ k,
  zero_mem':= zero_mod_form _ _,
  add_mem' := by
  { intros a b ha hb, split,
    exact mdifferentiable_add _ _ ha.hol hb.hol,
    exact (weakly_modular_submodule k Γ).add_mem' ha.transf hb.transf,
    intro, rw slash_k_add,
    exact bounded_at_infty_submodule.add_mem' (ha.infinity A) (hb.infinity A) },
  smul_mem' := by
  { intros c f hf,
    split,
    exact mdifferentiable_smul _ _ hf.hol,
    exact (weakly_modular_submodule k Γ).smul_mem' _ hf.transf,
    intro A, rw smul_slash_k, exact bounded_at_infty_submodule.smul_mem' _ (hf.infinity _), }, }

localized "notation `M(`k`, `Γ`)`:= space_of_mod_forms_of_weight_and_level Γ k" in modular_forms

/-- This is the space of cuspforms of level `Γ` and weigth `k`-/
def space_of_cusp_forms_of_weight_and_level (Γ : subgroup SL(2,ℤ)) (k : ℤ): submodule ℂ (ℍ → ℂ) :=
{ carrier   := is_cusp_form_of_lvl_and_weight Γ k,
  zero_mem' := zero_cusp_form _ _,
  add_mem'  := by
  { intros a b ha hb, split,
    exact mdifferentiable_add _ _ ha.hol hb.hol,
    exact (weakly_modular_submodule k Γ).add_mem' ha.transf hb.transf,
    intro A, rw slash_k_add,
    apply (zero_at_infty_submodule.add_mem' (ha.infinity A) (hb.infinity A)) },
  smul_mem' := by
  { intros c f hf, split,
    exact mdifferentiable_smul _ _ hf.hol,
    exact (weakly_modular_submodule k Γ).smul_mem' _ hf.transf,
    intro A, rw smul_slash_k, exact zero_at_infty_submodule.smul_mem' _ (hf.infinity _), }, }

localized "notation `S(`k`, `Γ`)`:= space_of_cusp_forms_of_weight_and_level Γ k" in modular_forms

lemma mul_modform {k_1 k_2 : ℤ} {Γ : subgroup SL(2, ℤ)} {f g : ℍ → ℂ}
  (hf : f ∈ M(k_1, Γ)) (hg : g ∈ M(k_2, Γ)) : f * g ∈ M(k_1 + k_2, Γ) :=
begin
  refine ⟨mdifferentiable_mul _ _ hf.1 hg.1, mul_modular hf.2 hg.2, _⟩,
  intro A, rw slash_k_mul_SL2 k_1 k_2 A f g,
  exact prod_of_bound_is_bound (hf.infinity A) (hg.infinity A),
end

/-! Constant functions are modular forms of weight 0 -/
section const_mod_form

def const_one_form : ℍ → ℂ := 1

/-- The constant function is bounded at infinity -/
lemma const_one_form_is_bound : is_bound_at_inf const_one_form :=
  @asymptotics.is_O_const_const _ _ ℂ _ _ 1 _ one_ne_zero _

/-- The constant function 1 is invariant under any subgroup of SL2Z -/
lemma const_one_form_is_invar (A : SL(2,ℤ)) : const_one_form ∣[0] A = const_one_form :=
begin
  rw [slash_k, const_one_form], dsimp only,
  have : (((↑ₘ(A : GL(2,ℝ)⁺)).det): ℝ) = 1,
  { simp only [coe_coe,
      matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
      matrix.special_linear_group.det_coe],},
  rw [zero_sub, this], simp, refl,
end

/-- The constant function 1 is modular of weight 0 -/
lemma const_mod_form : const_one_form ∈ M(0, Γ) :=
{ hol      := by { simp_rw const_one_form, apply mdifferentiable_one, },
  transf   := by { intro γ, apply const_one_form_is_invar, },
  infinity := by { intro A, rw const_one_form_is_invar A, exact const_one_form_is_bound,} }

end const_mod_form

end modular_forms
