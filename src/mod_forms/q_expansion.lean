import for_mathlib.mod_forms2
import analysis.complex.removable_singularity

/-!
# q-expansions of periodic functions

We show that if `f : ℂ → ℂ` satisfies `f(z + h) = f(z)`, for some nonzero real `h`, then
there is a well-defined `F` such that `f(z) = F(exp(2 * π * I * z / h))` for all `z`;
and if `f` is holomorphic at some `z`, then `F` is holomorphic at `exp(2 * π * I * z / h)`.

There is some code for functions on `ℍ`, currently commented out because of conflicts.

-/

open modular_forms
open complex
open_locale real topological_space manifold filter

noncomputable theory

section periodic_on_C

variables (h : ℝ) (hh : 0 < h) (f : ℂ → ℂ) (hf : ∀ (w : ℂ), f(w + h) = f(w))

def Q (z : ℂ) : ℂ := exp ( 2 * π * I * z / h )

def Z (q : ℂ) : ℂ := h / (2 * π * I) * log q

def cusp_fcn_0 : ℂ → ℂ := λ q, f (Z h q)

def cusp_fcn : ℂ → ℂ :=
  function.update (cusp_fcn_0 h f) 0 (lim (𝓝[≠] (0:ℂ)) (cusp_fcn_0 h f))

lemma log_exp' (z : ℂ) : ∃ (n : ℤ), log (exp z) = z + n * (2 * π * I) :=
begin
  rw [←exp_eq_exp_iff_exists_int, exp_log], exact exp_ne_zero z,
end

include hh hf

private lemma is_periodic_aux (z : ℂ) (m : ℕ) : f (z + m * h) = f z :=
begin
  induction m with m hm generalizing z, simp,
  rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one, add_mul, ←add_assoc, one_mul],
  rw hf (z + m * h), exact hm z,
end

lemma is_periodic (z : ℂ) (m : ℤ) : f (z + m * h) = f z :=
begin
  cases m, { exact is_periodic_aux h hh f hf z m },
  simp only [neg_add_rev, int.cast_neg_succ_of_nat],
  convert (is_periodic_aux h hh f hf (z - (m+1) * h) (m+1)).symm,
  { ring }, { simp },
end

lemma eq_cusp_fcn (z : ℂ) : f z = (cusp_fcn h f) (Q h z) :=
begin
  have : (cusp_fcn h f) (Q h z) = (cusp_fcn_0 h f) (Q h z),
  { rw cusp_fcn, rw function.update, split_ifs,
    { exfalso, have : Q h z ≠ 0 := by apply exp_ne_zero, exact this h_1, },
    { refl } },
  rw this,
  dsimp only [cusp_fcn_0, Q, Z, subtype.coe_mk],
  have t := log_exp' ( 2 * ↑π * I * z / ↑h ),
  cases t with n t, conv begin to_rhs, congr, rw t, end,
  have : ↑h / (2 * ↑π * I) * (2 * π * I * z / h + n * (2 * π * I)) = z + n * h,
  { field_simp [two_pi_I_ne_zero, of_real_ne_zero.mpr hh.ne'], ring, },
  conv begin to_rhs, congr, rw this, end,
  symmetry, exact (is_periodic h hh f hf z n),
end

end periodic_on_C

section holo_on_C

variables (h : ℝ) (hh : 0 < h) (f : ℂ → ℂ) (hf : ∀ (w : ℂ), f(w + h) = f(w))
include hh hf

lemma cusp_fcn_diff_at (z : ℂ) (hol_z : differentiable_at ℂ f z) :
  differentiable_at ℂ (cusp_fcn h f) (Q h z) :=
begin
  let QQ := (λ w, Q h w : ℂ → ℂ),
  let q := QQ z,
  let F := cusp_fcn h f,
  have qdiff : has_strict_deriv_at QQ (q * (2 * π * I / h)) z,
  { apply has_strict_deriv_at.cexp,
    apply has_strict_deriv_at.div_const,
    have : 2 * ↑π * I = (2 * ↑π * I) * 1 := by ring,
    conv begin congr, skip, rw this, end,
    refine has_strict_deriv_at.const_mul _ (has_strict_deriv_at_id _) },
  -- Now show that the q-map has a differentiable local inverse at z,
  -- say L : ℂ → ℂ, with L(q) = z.
  have diff_ne : (q * (2 * π * I / h)) ≠ 0,
  { apply mul_ne_zero, apply exp_ne_zero, apply div_ne_zero,
    exact two_pi_I_ne_zero, simpa using hh.ne', },
  let L := (qdiff.local_inverse QQ _ z) diff_ne,
  have diff_L : differentiable_at ℂ L q :=
    (qdiff.to_local_inverse diff_ne).differentiable_at,
  have hL : (QQ ∘ L) =ᶠ[𝓝 q] (id : ℂ → ℂ),
  { exact (qdiff.has_strict_fderiv_at_equiv diff_ne).eventually_right_inverse },
  --Thus, if F = cusp_expansion f, we have F(q') = f(L(q')) for q' near q.
  --Since L is differentiable at q, and f is diffble at L(q) [ = z], we conclude
  --that F is differentiable at q.
  have hF := filter.eventually_eq.fun_comp hL F, dsimp at hF,
  have : F ∘ QQ ∘ L = f ∘ L,
  { ext1 z, dsimp [F],
    --rw restrict_extend_eq_self',
    exact (eq_cusp_fcn h hh f hf (L z)).symm, },
  rw this at hF,
  have : z = L(q),
  { have hL2 : (L ∘ QQ) =ᶠ[𝓝 z] (id : ℂ → ℂ),
    { exact (qdiff.has_strict_fderiv_at_equiv diff_ne).eventually_left_inverse },
    replace hL2 := filter.eventually_eq.eq_of_nhds hL2, dsimp at hL2,
    rw hL2, },
  rw this at hol_z,
  exact (differentiable_at.comp q hol_z diff_L).congr_of_eventually_eq hF.symm,
end

end holo_on_C



section bounded_inf_on_C

variables (h : ℝ) (hh : 0 < h) (f : ℂ → ℂ) (hf : ∀ (w : ℂ), f(w + h) = f(w))
include hh hf



end bounded_inf_on_C


--section periodic_on_H

-- local notation `ℍ` := (⟨upper_half_space, upper_half_plane_is_open⟩ : open_subs)

-- def unit_disc_sset := {z : ℂ | z.abs <  1}

-- lemma unit_disc_is_open : is_open unit_disc_sset :=
-- begin
--   exact is_open.preimage complex.continuous_abs is_open_Iio,
-- end

-- def punc_disc_sset := {z : ℂ | z.abs <  1 ∧ z ≠ 0}

-- lemma punc_disc_is_open : is_open punc_disc_sset :=
-- begin
--   have : punc_disc_sset = complex.abs⁻¹' (set.Ioo 0 1),
--   { ext, simp only [set.mem_preimage, set.mem_Iio],
--     split,
--     { intro hx, split, rw complex.abs_pos, exact hx.2, exact hx.1 },
--     { intro hx, split, exact hx.2, rw ←complex.abs_pos, exact hx.1 }, },
--   rw this, exact is_open.preimage complex.continuous_abs is_open_Ioo,
-- end

-- local notation `𝔻` := ( ⟨ unit_disc_sset, unit_disc_is_open ⟩ : open_subs)
-- local notation `𝔻⋆`:= ( ⟨ punc_disc_sset, punc_disc_is_open ⟩ : open_subs)

-- instance : has_vadd ℝ ℍ :=
-- begin
--   split, intros h z, refine ⟨z.1 + h, _⟩, dsimp at *,
--   suffices : 0 < im (z.1 + h), { exact this },
--   rw [add_im, of_real_im, add_zero], exact z.2,
-- end

-- variables (h : ℝ) (hh : 0 < h) (f : ℍ → ℂ) (hf : ∀ (w : ℍ), f(h +ᵥ w) = f(w))

-- include hh

-- -- lemma q_in_Dstar (z : ℍ) :
-- --   abs (exp (2 * π * I * z / h)) < 1 ∧ exp (2 * π * I * z / h) ≠ 0:=
-- -- begin
-- --   split,
-- --   rw [abs_exp,real.exp_lt_one_iff, mul_assoc],
-- --   have : 2 * (π : ℂ) = ((2 * π : ℝ) : ℂ) := by simp, rw this,
-- --   rw [div_eq_inv_mul, ←of_real_inv, of_real_mul_re],
-- --   apply mul_neg_of_pos_of_neg (inv_pos.mpr hh),
-- --   rw [of_real_mul_re, mul_neg_iff], left, split,
-- --   { exact real.two_pi_pos },
-- --   simp only [I_re, one_mul, I_im, zero_sub, right.neg_neg_iff, zero_mul,
-- --     upper_half_plane.coe_im, mul_re],
-- --   exact upper_half_plane.im_pos z,
-- --   apply exp_ne_zero,
-- -- end

-- lemma z_in_H (q : 𝔻⋆) : 0 < im (h / (2 * π * I) * log q) :=
-- begin
--   rw mul_im,
--   have : (↑h / (2 * ↑π * I)).re = 0 := by { rw [div_re], simp, },
--   rw [this, zero_mul, zero_add],
--   apply mul_pos_of_neg_of_neg,
--   { rw div_eq_mul_inv, rw of_real_mul_im,
--     apply mul_neg_of_pos_of_neg hh,
--     rw inv_im, apply div_neg_of_neg_of_pos,
--     swap, { rw norm_sq_pos, exact two_pi_I_ne_zero },
--     apply neg_neg_of_pos,
--     have : 2 * (π : ℂ) = ((2 * π : ℝ) : ℂ) := by simp, rw this,
--     rw of_real_mul_im, rw I_im,
--     simp only [mul_one, zero_lt_bit0, zero_lt_mul_left, zero_lt_one],
--     exact real.pi_pos, },
--   rw log_re,
--   cases q, dsimp,
--   apply real.log_neg, rw complex.abs_pos,
--   exact q_property.2,
--   exact q_property.1,
-- end

-- include hf

-- lemma extend_periodic (w : ℂ) : (extend_by_zero f)(w + h) = (extend_by_zero f)(w) :=
-- begin
--   by_cases hw : 0 < im w,
--   { rw (restrict_extend_eq_self' f w hw),
--     have : 0 < im (w + ↑h), {rw [add_im, of_real_im, add_zero], exact hw },
--     rw (restrict_extend_eq_self' f _ this), exact hf ⟨ w, hw ⟩, },
--   { have : extend_by_zero f w = 0,
--     { rw extend_by_zero, simp, intro bad, exfalso, exact hw bad },
--     rw this,
--     have : extend_by_zero f (w + ↑h) = 0,
--     { rw extend_by_zero, simp, intro bad, exfalso,
--       have : 0 < im (w + h) := by tauto, rw [add_im, of_real_im, add_zero] at this,
--       exact hw this, },
--     exact this }
-- end

-- def cusp_fcn_H : ℂ → ℂ := cusp_fcn h (extend_by_zero f)

-- lemma eq_cusp_fcn_H (z : ℍ) : f z = (cusp_fcn_H h hh f hf) (Q h z) :=
-- begin
--   have t := eq_cusp_fcn h hh (extend_by_zero f) (extend_periodic h hh f hf) z,
--   rw cusp_fcn_H, dsimp only, convert t,
--   rw restrict_extend_eq_self' f _ _, { simp }, { cases z, tauto, },
-- end

-- lemma cusp_fcn_diff_at_H (hf_hol : is_holomorphic_on f) (q : 𝔻⋆) :
--   differentiable_at ℂ (cusp_fcn_H h hh f hf) q :=
-- begin
--   let z := Z h q,
--   have hz := z_in_H h hh q,
--   have : (Q h z : ℂ) = q,
--   { rw Q, dsimp,
--     have : z = ↑h / (2 * ↑π * I) * log ↑q := by refl, rw this,
--     have : 2 * ↑π * I * (↑h / (2 * ↑π * I) * log ↑q) / ↑h = log q,
--     { field_simp [two_pi_I_ne_zero, of_real_ne_zero.mpr hh.ne'], ring, }, rw this,
--     exact exp_log q.2.right, },
--   rw ←is_holomorphic_on_iff_differentiable_on at hf_hol,
--   replace hf_hol := hf_hol z hz,
--   dsimp at hf_hol,
--   replace hf_hol := hf_hol.differentiable_at
--     ((is_open_iff_mem_nhds.mp upper_half_plane_is_open) z hz),
--   have t := (cusp_fcn_diff_at h hh (extend_by_zero f) (extend_periodic h hh f hf)) z hf_hol,
--   rw this at t,
--   rw cusp_fcn_H, dsimp,
--   exact t,
-- end

-- lemma cusp_fcn_bound_near_zero (hf_hol : is_holomorphic_on f) (hf_bd : is_bound_at_infinity f) :
--   differentiable_at ℂ (cusp_fcn_H h hh f hf) 0 :=
-- begin
--   obtain ⟨M, A, hMA⟩ := hf_bd,
--   let F := cusp_fcn_H h hh f hf,
--   let a := real.exp (- 2 * π * A ),
--   let s := { q : ℂ | (abs q < a) ∧ (abs q < 1) },
--   have s_nhd : s ∈ 𝓝 (0:ℂ),
--   { apply is_open.mem_nhds,
--     sorry, simp only [set.mem_set_of_eq, complex.abs_zero, zero_lt_one, and_true],
--     apply real.exp_pos },
--   have F_bd_1 : ∀ (q : ℂ), (q ∈ s) → abs( F(q) ) ≤ M,
--   {
--     sorry,
--   },
--   have F_diff : differentiable_on ℂ F (s \ {0}),
--   {
--     sorry,
--   },
--   have F_bd_2 : bdd_above (norm ∘ F '' (s \ {0})),
--   {
--     sorry,
--   },
--   have := differentiable_on_update_lim_of_bdd_above s_nhd F_diff F_bd_2,
--   convert this.differentiable_at s_nhd,
--   ext1 q, rw function.update, split_ifs,
--   rw cusp_fcn_H,
-- end

-- end periodic_on_H
