import for_mathlib.mod_forms2
import mod_forms.holomorphic_functions
import analysis.complex.removable_singularity
import mod_forms.upper_half_plane_manifold
/-!
# q-expansions of periodic functions

We show that if `f : ℂ → ℂ` satisfies `f(z + h) = f(z)`, for some nonzero real `h`, then
there is a well-defined `F` such that `f(z) = F(exp(2 * π * I * z / h))` for all `z`;
and if `f` is holomorphic at some `z`, then `F` is holomorphic at `q = exp (2 * π * I * z / h)`.

We also show (using Riemann's removable singularity theorem) that if `f` is holomorphic and bounded
for all sufficiently large `im z`, then `F` extends to a holomorphic function on a neighbourhood of
`0`. As a consequence, if `f` tends to zero as `im z → ∞`, then in fact it decays *exponentially*
to zero.
-/

open modular_forms complex filter asymptotics
open_locale real topological_space manifold filter

noncomputable theory

abbreviation ℝ_pos := {u : ℝ // 0 < u}

/-- Function-theoretic lemma, maybe move this elsewhere? -/
lemma bound_holo_fcn (g : ℂ → ℂ) (hg : differentiable_at ℂ g 0) (hg' : g 0 = 0):
  is_O g id (𝓝 0) :=
begin
  replace hg := hg.has_deriv_at.is_O_sub, simp_rw [hg', sub_zero] at hg, exact hg,
end


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

lemma abs_q_lt_iff (A : ℝ) (z : ℂ) : abs (Q h z) < real.exp(-2 * π * A / h) ↔ A < im z :=
begin
  rw [abs_Q_eq, real.exp_lt_exp],
  split,
  { intro hz, rw div_lt_div_right at hz, swap, exact h.2,
    have : (-2) * π < 0 := by simpa using real.pi_pos,
    rwa mul_lt_mul_left_of_neg this at hz, },
  { intro hz, rw div_lt_div_right, swap, exact h.2,
    have : (-2) * π < 0 := by simpa using real.pi_pos,
    rwa mul_lt_mul_left_of_neg this, },
end

-- Filter stuff

def at_I_inf' : filter ℂ := at_top.comap im

lemma at_I_inf'_mem (S : set ℂ) : S ∈ at_I_inf' ↔ (∃ A : ℝ, ∀ z : ℂ, A < im z → z ∈ S) :=
begin
  rw [at_I_inf', mem_comap', mem_at_top_sets],
  simp, split,
  { intro h, cases h with a h, use a,
    intros z hz, specialize h (im z) hz.le, apply h, refl },
  { intro h, cases h with A h, use A + 1,
    intros b hb x hx, apply (h x), rw hx, linarith, }
end

lemma Z_tendsto : tendsto (Z h) (𝓝[{0}ᶜ] 0) at_I_inf' :=
begin
  rw [tendsto, map_le_iff_le_comap, comap],
  intros S h, simp_rw at_I_inf'_mem at h, obtain ⟨T, ⟨A, hA⟩, hT⟩ := h,
  simp_rw [metric.mem_nhds_within_iff, metric.ball, dist_eq, sub_zero],
  use real.exp(-2 * π * A / h), split, apply real.exp_pos,
  intro q, dsimp, rintro ⟨u1, u2⟩,
  rw [←(QZ_eq_id h _ u2), abs_q_lt_iff] at u1, specialize hA (Z h q) u1,
  apply hT, exact hA,
end

lemma Q_tendsto : tendsto (Q h) at_I_inf' (𝓝 0) :=
begin
  rw [tendsto_zero_iff_norm_tendsto_zero],
  simp_rw [norm_eq_abs,abs_Q_eq],
  have : set.range im ∈ at_top,
  { suffices : set.range im = ⊤, { rw this, apply univ_mem, },
    ext1, simp only [set.mem_range, set.top_eq_univ, set.mem_univ, iff_true],
    use I * x, simp, },
  have := (@tendsto_comap'_iff ℝ ℝ ℂ (λ y, real.exp ((-2) * π * y / ↑h)) at_top (𝓝 0) im this).mpr,
  apply this, refine real.tendsto_exp_at_bot.comp _,
  apply tendsto.at_bot_div_const h.2,
  apply tendsto.neg_const_mul_at_top, { simpa using real.pi_pos }, exact tendsto_id,
end

end Q_and_Z

section periodic_on_C

variables (h : ℝ_pos) (f : ℂ → ℂ) (hf : ∀ (w : ℂ), f(w + h) = f(w))

def cusp_fcn_0 : ℂ → ℂ := λ q, f (Z h q)

def cusp_fcn : ℂ → ℂ := function.update (cusp_fcn_0 h f) 0 (lim (𝓝[≠] (0:ℂ)) (cusp_fcn_0 h f))

lemma cusp_fcn_eq_of_nonzero (q : ℂ) (hq : q ≠ 0) :
  (cusp_fcn h f) q = (cusp_fcn_0 h f) q :=
begin
  rw [cusp_fcn, function.update], split_ifs,
  { exfalso, exact hq h_1 },
  { refl },
end

lemma update_twice :
  cusp_fcn h f = function.update (cusp_fcn h f) 0 (lim (𝓝[≠] (0:ℂ)) (cusp_fcn h f)) :=
begin
  ext1 q, rw function.update, split_ifs,
  { rw [cusp_fcn, function.update], split_ifs,
    congr' 1, rw [lim, lim], congr' 1,
    apply map_congr, apply eventually_eq_nhds_within_of_eq_on,
    intros r hr, simp at hr,
    rw function.update, split_ifs, refl,},
  { refl, },
end

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
  let q := Q h z,
  have qdiff : has_strict_deriv_at (Q h) (q * (2 * π * I / h)) z,
  { apply has_strict_deriv_at.cexp,
    apply has_strict_deriv_at.div_const,
    have : 2 * ↑π * I = (2 * ↑π * I) * 1 := by ring,
    conv begin congr, skip, rw this, end,
    exact has_strict_deriv_at.const_mul _ (has_strict_deriv_at_id _) },
  -- Now show that the q-map has a differentiable local inverse at z, say L : ℂ → ℂ, with L(q) = z.
  have diff_ne : (q * (2 * π * I / h)) ≠ 0,
  { apply mul_ne_zero, apply exp_ne_zero, apply div_ne_zero,
    exact two_pi_I_ne_zero, simpa using h.2.ne', },
  let L := (qdiff.local_inverse (Q h) _ z) diff_ne,
  have diff_L : differentiable_at ℂ L q := (qdiff.to_local_inverse diff_ne).differentiable_at,
  have hL : (Q h) ∘ L =ᶠ[𝓝 q] (id : ℂ → ℂ),
  { exact (qdiff.has_strict_fderiv_at_equiv diff_ne).eventually_right_inverse },
  --Thus, if F = cusp_expansion f, we have F(q') = f(L(q')) for q' near q.
  --Since L is differentiable at q, and f is diffble at L(q) [ = z], we conclude
  --that F is differentiable at q.
  have hF := eventually_eq.fun_comp hL (cusp_fcn h f), dsimp at hF,
  have : (cusp_fcn h f) ∘ (Q h) ∘ L = f ∘ L := by { ext1 z, exact (eq_cusp_fcn h f hf (L z)).symm },
  rw this at hF,
  have : z = L(q),
  { have hL2 : (L ∘ (Q h)) =ᶠ[𝓝 z] (id : ℂ → ℂ),
    { exact (qdiff.has_strict_fderiv_at_equiv diff_ne).eventually_left_inverse },
    replace hL2 := eventually_eq.eq_of_nhds hL2, dsimp at hL2, rw hL2, },
  rw this at hol_z,
  exact (differentiable_at.comp q hol_z diff_L).congr_of_eventually_eq hF.symm,
end

lemma F_diff_near_zero (h_hol : ∀ᶠ (z : ℂ) in at_I_inf', differentiable_at ℂ f z) :
  ∀ᶠ (q : ℂ) in 𝓝[≠] 0, differentiable_at ℂ (cusp_fcn h f) q :=
begin
  refine ((Z_tendsto h).eventually h_hol).mp _,
  apply eventually_nhds_within_of_forall, intros q hq h_diff,
  rw ←(QZ_eq_id _ _ hq), exact cusp_fcn_diff_at _ _ hf _ h_diff,
end

end holo_on_C

section holo_at_inf_C

variables (h : ℝ_pos) (f : ℂ → ℂ) (hf : ∀ (w : ℂ), f(w + h) = f(w))
include hf

lemma F_bound (h_bd : is_O f (1 : ℂ → ℂ) at_I_inf') : is_O (cusp_fcn h f) (1 : ℂ → ℂ) (𝓝[≠] 0) :=
begin
  refine is_O.congr' _ (by refl) (h_bd.comp_tendsto $ Z_tendsto h),
  apply eventually_nhds_within_of_forall, intros q hq,
  rw cusp_fcn_eq_of_nonzero _ _ _ hq, refl,
end

lemma F_diff_at_zero (h_bd : is_O f (1 : ℂ → ℂ) at_I_inf')
  (h_hol : ∀ᶠ (z : ℂ) in at_I_inf', differentiable_at ℂ f z) :
  differentiable_at ℂ (cusp_fcn h f) 0 :=
begin
  obtain ⟨c, t⟩ := (F_bound _ _ hf h_bd).bound,
  replace t := (F_diff_near_zero h f hf h_hol).and t,
  simp only [norm_eq_abs, pi.one_apply, complex.abs_one, mul_one] at t,
  obtain ⟨S, hS1, hS2, hS3⟩ := eventually_nhds_iff.mp (eventually_nhds_within_iff.mp t),
  have h_diff : differentiable_on ℂ (cusp_fcn h f) (S \ {0}),
  { intros x hx, apply differentiable_at.differentiable_within_at,
    exact (hS1 x ((set.mem_diff _).mp hx).1  ((set.mem_diff _).mp hx).2).1, },
  have hF_bd : bdd_above (norm ∘ (cusp_fcn h f) '' (S \ {0})),
  { use c, rw mem_upper_bounds, simp, intros y q hq hq2 hy, rw ←hy, exact (hS1 q hq hq2).2 },
  have := differentiable_on_update_lim_of_bdd_above (is_open.mem_nhds hS2 hS3) h_diff hF_bd,
  rw ←update_twice at this,
  exact this.differentiable_at (is_open.mem_nhds hS2 hS3),
end

/-- If `f` is periodic, and holomorphic and bounded near `I∞`, then it tends to a limit at `I∞`,
and this limit is the value of its cusp function at 0. -/
theorem tendsto_at_I_inf (h_bd : is_O f (1 : ℂ → ℂ) at_I_inf')
  (h_hol : ∀ᶠ (z : ℂ) in at_I_inf', differentiable_at ℂ f z) :
  tendsto f at_I_inf' (𝓝 $ cusp_fcn h f 0) :=
begin
  suffices : tendsto (cusp_fcn h f) (𝓝[≠] 0) (𝓝 $ cusp_fcn h f 0),
  { have t2 : f = (cusp_fcn h f) ∘ (Q h) := by { ext1, apply eq_cusp_fcn h f hf },
    conv begin congr, rw t2, end,
    apply tendsto.comp, exact this,
    apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
    exact Q_tendsto h, apply eventually_of_forall, intro q, apply exp_ne_zero, },
  exact tendsto_nhds_within_of_tendsto_nhds (F_diff_at_zero _ _ hf h_bd h_hol).continuous_at.tendsto
end

lemma cusp_fcn_zero_of_zero_at_inf (h_bd : is_o f (1 : ℂ → ℂ) at_I_inf')
  (h_hol : ∀ᶠ (z : ℂ) in at_I_inf', differentiable_at ℂ f z) : cusp_fcn h f 0 = 0 :=
begin
  rw [cusp_fcn, function.update], split_ifs, swap, tauto,
  suffices : tendsto (cusp_fcn_0 h f) (𝓝[{0}ᶜ] 0) (𝓝 (0:ℂ)),
  { exact tendsto.lim_eq this },
  have : is_o (cusp_fcn h f) 1 (𝓝[≠] 0),
  { refine is_o.congr' _ (by refl) (h_bd.comp_tendsto $ Z_tendsto h),
    apply eventually_nhds_within_of_forall, intros q hq, rw cusp_fcn_eq_of_nonzero _ _ _ hq, refl },
  have : is_o (cusp_fcn_0 h f) 1 (𝓝[≠] 0),
  { refine is_o.congr' _ (by refl) this, apply eventually_nhds_within_of_forall,
    apply cusp_fcn_eq_of_nonzero, },
  simpa using this.tendsto_div_nhds_zero,
end

/-- Main theorem of this file: if `f` is periodic, holomorphic near `I∞`, and tends to zero
at `I∞`, then in fact it tends to zero exponentially fast. -/
theorem exp_decay_of_zero_at_inf (h_bd : is_o f (1 : ℂ → ℂ) at_I_inf')
  (h_hol : ∀ᶠ (z : ℂ) in at_I_inf', differentiable_at ℂ f z) :
  is_O f (λ z:ℂ, real.exp (-2 * π * im z / h)) at_I_inf' :=
begin
  have F0 := cusp_fcn_zero_of_zero_at_inf _ _ hf h_bd h_hol,
  have : f = λ z:ℂ, (cusp_fcn h f) (Q h z) := by { ext1 z, apply eq_cusp_fcn _ _ hf,},
  conv begin congr, rw this, skip, funext, rw [←(abs_Q_eq h), ←norm_eq_abs], end,
  apply is_O.norm_right,
  exact (bound_holo_fcn _ (F_diff_at_zero _ _ hf h_bd.is_O h_hol) F0).comp_tendsto (Q_tendsto h),
end

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
