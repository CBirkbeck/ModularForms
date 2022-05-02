import for_mathlib.mod_forms2
import mod_forms.holomorphic_functions
import analysis.complex.removable_singularity
import mod_forms.upper_half_plane_manifold
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

abbreviation ℝ_pos := {u : ℝ // 0 < u}

section Q_and_Z

variables (h : ℝ_pos)

def Q (z : ℂ) : ℂ := exp ( 2 * π * I * z / h )

def Z (q : ℂ) : ℂ := h / (2 * π * I) * log q

lemma log_exp' (z : ℂ) : ∃ (n : ℤ), log (exp z) = z + n * (2 * π * I) :=
begin
  rw [←exp_eq_exp_iff_exists_int, exp_log], exact exp_ne_zero z,
end

lemma QZ_eq_id (q : ℂ) (hq : q ≠ 0) : Q h (Z h q) = q :=
begin
  dsimp only [Q, Z],
  suffices : 2 * ↑π * I * (↑h / (2 * ↑π * I) * log q) / ↑h = log q,
  { rw this, exact exp_log hq },
  have : (h : ℂ) ≠ 0 := of_real_ne_zero.mpr h.2.ne',
  field_simp [two_pi_I_ne_zero, this], ring,
end

lemma abs_Q_eq (z : ℂ) : abs (Q h z) = real.exp(-2 * π * im z / h) :=
begin
  dsimp only [Q], rw abs_exp, congr,
  rw [div_eq_mul_inv, mul_comm],
  have : (↑h)⁻¹ = (↑((h : ℝ)⁻¹) : ℂ) := by simp, rw this,
  rw of_real_mul_re,
  have : 2 * ↑π * I * z = (↑(2 * π) * z) * I := by { simp, ring, },
  rw [this, mul_I_re, of_real_mul_im], field_simp [h.2.ne'],
end

lemma im_Z_eq (q : ℂ) (hq : q ≠ 0) : im (Z h q) = -h / (2 * π) * real.log (abs q) :=
begin
  dsimp only [Z],
  have : ↑h / (2 * ↑π * I) * log q = -↑h / (2 * ↑π) * log q * I,
  { field_simp [of_real_ne_zero.mpr real.pi_pos.ne', two_pi_I_ne_zero], ring_nf, simp, },
  rw [this, mul_I_im],
  have : -↑h / (2 * ↑π) * log q = ↑(-↑h / (2 * π)) * log q := by simp,
  rw [this, of_real_mul_re, log_re],
end

lemma ZQ_eq_mod_period (z : ℂ) : ∃ (m : ℤ), Z h (Q h z) = z + m * h :=
begin
  dsimp only [Q, Z],
  have t := log_exp' ( 2 * ↑π * I * z / ↑h ),
  cases t with m t, use m, rw t,
  have : (h:ℂ) ≠ 0 := of_real_ne_zero.mpr h.2.ne',
  field_simp [two_pi_I_ne_zero], ring,
end

end Q_and_Z

section periodic_on_C

variables (h : ℝ_pos) (f : ℂ → ℂ) (hf : ∀ (w : ℂ), f(w + h) = f(w))

def cusp_fcn_0 : ℂ → ℂ := λ q, f (Z h q)

def cusp_fcn : ℂ → ℂ :=
  function.update (cusp_fcn_0 h f) 0 (lim (𝓝[≠] (0:ℂ)) (cusp_fcn_0 h f))

include hf

private lemma is_periodic_aux (z : ℂ) (m : ℕ) : f (z + m * h) = f z :=
begin
  induction m with m hm generalizing z, simp,
  rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one, add_mul, ←add_assoc, one_mul],
  rw hf (z + m * h), exact hm z,
end

lemma is_periodic (z : ℂ) (m : ℤ) : f (z + m * h) = f z :=
begin
  cases m, { exact is_periodic_aux h f hf z m },
  simp only [neg_add_rev, int.cast_neg_succ_of_nat],
  convert (is_periodic_aux h f hf (z - (m+1) * h) (m+1)).symm,
  { ring }, { simp },
end

lemma eq_cusp_fcn (z : ℂ) : f z = (cusp_fcn h f) (Q h z) :=
begin
  have : (cusp_fcn h f) (Q h z) = (cusp_fcn_0 h f) (Q h z),
  { rw cusp_fcn, rw function.update, split_ifs,
    { exfalso, have : Q h z ≠ 0 := by apply exp_ne_zero, exact this h_1, },
    { refl } },
  rw this,
  dsimp only [cusp_fcn_0],
  obtain ⟨m, hm⟩ := ZQ_eq_mod_period h z,
  rw hm, exact (is_periodic h f hf z m).symm,
end

end periodic_on_C

section holo_on_C

variables (h : ℝ_pos) (f : ℂ → ℂ) (hf : ∀ (w : ℂ), f(w + h) = f(w))
include hf

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
    exact two_pi_I_ne_zero, simpa using h.2.ne', },
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
    exact (eq_cusp_fcn h f hf (L z)).symm, },
  rw this at hF,
  have : z = L(q),
  { have hL2 : (L ∘ QQ) =ᶠ[𝓝 z] (id : ℂ → ℂ),
    { exact (qdiff.has_strict_fderiv_at_equiv diff_ne).eventually_left_inverse },
    replace hL2 := filter.eventually_eq.eq_of_nhds hL2, dsimp at hL2,
    rw hL2, },
  rw this at hol_z,
  exact (differentiable_at.comp q hol_z diff_L).congr_of_eventually_eq hF.symm,
end

lemma diff_on_region (A : ℝ) (hol_f : differentiable_on ℂ f { z:ℂ | A < im z }) :
  differentiable_on ℂ (cusp_fcn h f) {q:ℂ | q ≠ 0 ∧ abs q < real.exp (-2 * π * A / h)} :=
begin
  intros q hq,
  apply differentiable_at.differentiable_within_at,
  let z := Z h q, have : Q h z = q := by apply QZ_eq_id _ _ hq.1, rw ←this,
  have hz : A < im z,
  { have hq_abs := hq.2,
    have hh : (0:ℝ) < h := h.2,
    rw [←this, abs_Q_eq, real.exp_lt_exp, div_lt_div_iff hh hh,
      mul_lt_mul_right hh, mul_lt_mul_left_of_neg] at hq_abs,
    exact hq_abs, simp [real.pi_pos], },
  apply cusp_fcn_diff_at _ _ hf,
  apply differentiable_within_at.differentiable_at (hol_f z hz),
  exact is_open.mem_nhds (continuous.is_open_preimage continuous_im _ is_open_Ioi) hz,
end

end holo_on_C

section holo_at_inf_C

def at_I_inf : filter ℂ := filter.at_top.comap im

variables (h : ℝ_pos) (f : ℂ → ℂ) (hf : ∀ (w : ℂ), f(w + h) = f(w)) (A : ℝ) (C : ℝ)
include hf

-- lemma F_bound' (h_bd : asymptotics.is_O f (1 : ℂ → ℂ) at_I_inf) : ∃ (R : ℝ_pos),
--   bdd_above (norm ∘ (cusp_fcn h f) '' ( { q : ℂ |  abs q < real.exp (-2 * π * R / h) } \ {0} )) :=
-- begin
--   rw bdd_above_def,
--   use C, intros y hy, cases hy with q hq,
--   simp only [set.mem_diff, set.mem_set_of_eq, set.mem_singleton_iff,
--     function.comp_app, norm_eq_abs] at hq,
--   rw ←hq.2, replace hq := hq.1,
--   let z := Z h q,
--   have hz : Q h z = q := by { apply QZ_eq_id , exact hq.2 },
--   have hz2 : A < im z,
--   { rw [←hz, abs_Q_eq, real.exp_lt_exp, div_lt_div_right] at hq,
--     swap, exact h.2,
--     rw mul_lt_mul_left_of_neg at hq, exact hq.1, simp [real.pi_pos], },
--   convert h_bd z hz2.le,
--   rw [←hz, eq_cusp_fcn h f hf z],
-- end


lemma F_bound (h_bd : ∀ z:ℂ, A ≤ im z → abs (f z) ≤ C) :
  bdd_above (norm ∘ (cusp_fcn h f) '' ( { q : ℂ |  abs q < real.exp (-2 * π * A / h) } \ {0} )) :=
begin
  rw bdd_above_def,
  use C, intros y hy, cases hy with q hq,
  simp only [set.mem_diff, set.mem_set_of_eq, set.mem_singleton_iff,
    function.comp_app, norm_eq_abs] at hq,
  rw ←hq.2, replace hq := hq.1,
  let z := Z h q,
  have hz : Q h z = q := by { apply QZ_eq_id , exact hq.2 },
  have hz2 : A < im z,
  { rw [←hz, abs_Q_eq, real.exp_lt_exp, div_lt_div_right] at hq,
    swap, exact h.2,
    rw mul_lt_mul_left_of_neg at hq, exact hq.1, simp [real.pi_pos], },
  convert h_bd z hz2.le,
  rw [←hz, eq_cusp_fcn h f hf z],
end

lemma F_hol_at_zero (h_bd : ∀ z:ℂ, A ≤ im z → abs (f z) ≤ C)
(h_hol : differentiable_on ℂ f { z:ℂ | A < im z }) :
  differentiable_on ℂ (cusp_fcn h f) {q:ℂ | abs q < real.exp (-2 * π * A / h)} :=
begin
  let S := {q:ℂ | abs q < real.exp (-2 * π * A / h)},
  have h_nhd : S ∈ 𝓝 (0:ℂ),
  { apply is_open.mem_nhds,
    have : S = abs⁻¹' (set.Iio (real.exp (-2 * π * A / h))) := by {ext, simp},
    rw this,
    exact continuous.is_open_preimage complex.continuous_abs _ is_open_Iio,
    rw [set.mem_set_of_eq, complex.abs_zero], apply real.exp_pos, },
  have hF_bd := F_bound h f hf _ _ h_bd,
  have hF_diff := diff_on_region h f hf _ h_hol,
  have hF_diff' : differentiable_on ℂ (cusp_fcn h f) (S \ {(0:ℂ)}),
  { convert hF_diff, ext q,
    simp only [set.mem_diff, set.mem_set_of_eq, neg_mul, set.mem_singleton_iff, ne.def], tauto, },
  have t := differentiable_on_update_lim_of_bdd_above h_nhd hF_diff' hF_bd,
  convert t,
  -- The rest is just checking that "function.update" doesn't break anything
  ext1 q, rw function.update, split_ifs,
  { rw [cusp_fcn, function.update], split_ifs,
    congr' 1,
    rw [lim,lim],
    congr' 1,
    apply filter.map_congr, apply eventually_eq_nhds_within_of_eq_on,
    intros r hr, simp at hr,
    rw function.update, split_ifs, refl,},
  { refl, },
end

lemma cusp_fcn_zero_of_zero_at_inf (h_hol : differentiable_on ℂ f { z:ℂ | A < im z })
  (h_zero : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ z : ℂ, B ≤ im z → abs (f z) ≤ ε) : cusp_fcn h f 0 = 0 :=
begin
  rw [cusp_fcn, function.update], split_ifs, swap, tauto,
  suffices : filter.tendsto (cusp_fcn_0 h f) (𝓝[{0}ᶜ] 0) (𝓝 (0:ℂ)),
  { exact filter.tendsto.lim_eq this },
  rw metric.tendsto_nhds_within_nhds,
  simp_rw [dist_eq_norm, sub_zero],
  intros ε hε,
  specialize h_zero (ε/2) (by linarith),
  cases h_zero with B h_zero,
  use real.exp(-2 * π * B / h), split, apply real.exp_pos,
  intros q hq hq2,
  let z := Z h q,
  have : B ≤ im z,
  { rw [im_Z_eq h q hq, neg_div,neg_mul, le_neg,
      div_mul_eq_mul_div, div_le_iff real.two_pi_pos],
    ring_nf,
    rw [norm_eq_abs] at hq2,
    replace hq2 := (real.log_lt_log (complex.abs_pos.mpr hq) hq2).le,
    rw real.log_exp at hq2,
    rw le_div_iff' _ at hq2, swap, exact h.2, ring_nf at hq2,
    have: 2 * π * B = 2 * B * π := by ring, rw this, exact hq2 },
  replace h_zero := h_zero z this,
  have : cusp_fcn_0 h f q = f z,
  { rw eq_cusp_fcn h f hf,
    rw QZ_eq_id h q hq,
    rw [cusp_fcn, function.update], split_ifs,
    { exfalso, exact hq h_2,},
    { refl, } },
  rw this,
  refine lt_of_le_of_lt h_zero _,
  linarith,
end

lemma bound_holo_fcn (g : ℂ → ℂ) (hg : differentiable_at ℂ g 0) (hg' : g 0 = 0):
  asymptotics.is_O g id (𝓝 0) :=
begin
  replace hg := hg.has_deriv_at.is_O_sub,
  simp_rw [hg', sub_zero, coe_coe] at *, exact hg,
end

-- lemma exp_decay_of_zero_at_inf (h_hol : differentiable_on ℂ f { z:ℂ | A < im z })
--   (h_zero : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ z : ℂ, B ≤ im z  → abs (f z) ≤ ε) :
--   ∃ D E : ℝ, (0 < E) ∧ (∀ z : ℂ, D ≤ im z → abs (f z) ≤ E * real.exp (-2 * π * im z / h) ) :=
-- begin
--   --First show boundedness at inf
--   obtain ⟨A2, h_bd⟩ := h_zero (1 : ℝ) zero_lt_one,
--   let A' := max A A2,
--   have h_hol' : differentiable_on ℂ f { z:ℂ | A' < im z },
--   { apply differentiable_on.mono h_hol,
--     simp only [max_lt_iff, set.set_of_subset_set_of, and_imp], intro a, tauto },
--   have h_bd' : ∀ (z : ℂ), A' ≤ z.im → abs (f z) ≤ 1,
--   { intros z hz, apply h_bd, exact le_trans (le_max_right A A2) hz, },
--   have hF_hol := F_hol_at_zero h f hf _ _ h_bd' h_hol',
--   use (A' + 1),
--   sorry
-- end

end holo_at_inf_C


/-! Now we prove corresponding results about functions `ℍ → ℂ`. There is some tedious
book-keeping involved here. -/
section periodic_on_H

local notation `ℍ` := (⟨upper_half_plane.upper_half_space,
  upper_half_plane.upper_half_plane_is_open⟩ : open_subs)

def punc_disc_sset := {z : ℂ | z.abs <  1 ∧ z ≠ 0}

lemma punc_disc_is_open : is_open punc_disc_sset :=
begin
  have : punc_disc_sset = complex.abs⁻¹' (set.Ioo 0 1),
  { ext, simp only [set.mem_preimage, set.mem_Iio],
    split,
    { intro hx, split, rw complex.abs_pos, exact hx.2, exact hx.1 },
    { intro hx, split, exact hx.2, rw ←complex.abs_pos, exact hx.1 }, },
  rw this, exact is_open.preimage complex.continuous_abs is_open_Ioo,
end

--local notation `𝔻` := ( ⟨ unit_disc_sset, unit_disc_is_open ⟩ : open_subs)
local notation `𝔻⋆`:= ( ⟨ punc_disc_sset, punc_disc_is_open ⟩ : open_subs)

instance : has_vadd ℝ ℍ :=
begin
  split, intros h z, refine ⟨z.1 + h, _⟩, dsimp at *,
  suffices : 0 < im (z.1 + h), { exact this },
  rw [add_im, of_real_im, add_zero], exact z.2,
end

variables (h : ℝ_pos) (f : ℍ → ℂ) (hf : ∀ (w : ℍ), f(h.1 +ᵥ w) = f(w))

lemma z_in_H (q : 𝔻⋆) : Z h ↑q ∈ ℍ.1 :=
begin
  dsimp only [upper_half_plane.upper_half_space],
  simp only [set.mem_set_of_eq],
  rw im_Z_eq h q q.2.2,
  apply mul_pos_of_neg_of_neg,
  { exact div_neg_of_neg_of_pos (neg_lt_zero.mpr h.2) real.two_pi_pos, },
  rw real.log_neg_iff, exact q.2.1,
  rw complex.abs_pos, exact q.2.2,
end

include hf

lemma extend_periodic (w : ℂ) : (extend_by_zero f)(w + h) = (extend_by_zero f)(w) :=
begin
  by_cases hw : 0 < im w,
  { rw (extend_by_zero_eq_of_mem f w hw),
    have : 0 < im (w + ↑h), {rw [add_im, coe_coe, of_real_im, add_zero], exact hw },
    rw (extend_by_zero_eq_of_mem f _ this), exact hf ⟨ w, hw ⟩, },
  { have : extend_by_zero f w = 0,
    { rw extend_by_zero, simp, intro bad, exfalso, exact hw bad },
    rw this,
    have : extend_by_zero f (w + ↑h) = 0,
    { rw extend_by_zero, simp, intro bad, exfalso,
      have : 0 < im (w + h) := by tauto,
      rw [add_im, coe_coe, of_real_im, add_zero] at this,
      exact hw this, },
    exact this }
end

def cusp_fcn_H : ℂ → ℂ := cusp_fcn h (extend_by_zero f)

lemma eq_cusp_fcn_H (z : ℍ) : f z = (cusp_fcn_H h f hf) (Q h z) :=
begin
  have t := eq_cusp_fcn h (extend_by_zero f) (extend_periodic h f hf) z,
  rw cusp_fcn_H, dsimp only, convert t,
  rw extend_by_zero_eq_of_mem f _ _, { simp }, { cases z, tauto, },
end

lemma cusp_fcn_diff_at_H (hf_hol : is_holomorphic_on f) (q : 𝔻⋆) :
  differentiable_at ℂ (cusp_fcn_H h f hf) q :=
begin
  let z := Z h q,
  have hz := z_in_H h q,
  have : (Q h z : ℂ) = q := QZ_eq_id h q q.2.2,
  rw ←is_holomorphic_on_iff_differentiable_on at hf_hol,
  replace hf_hol := hf_hol z hz,
  dsimp at hf_hol,
  replace hf_hol := hf_hol.differentiable_at
    ((is_open_iff_mem_nhds.mp ℍ.2) z hz),
  have t := (cusp_fcn_diff_at h (extend_by_zero f) (extend_periodic h f hf)) z hf_hol,
  rw this at t,
  rw cusp_fcn_H, dsimp,
  exact t,
end

-- lemma cusp_fcn_bound_near_zero (hf_hol : is_holomorphic_on f) (hf_bd : is_bound_at_infinity f) :
--   differentiable_at ℂ (cusp_fcn_H h f hf) 0 :=
-- begin
--   obtain ⟨M, A, hMA⟩ := hf_bd,
--   let F := cusp_fcn_H h f hf,
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

end periodic_on_H
