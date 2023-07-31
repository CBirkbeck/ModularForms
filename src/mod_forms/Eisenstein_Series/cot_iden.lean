import data.complex.exponential
import mod_forms.Eisenstein_Series.Eisen_is_holo
import mod_forms.Eisenstein_Series.exp_summable_lemmas
import analysis.special_functions.trigonometric.euler_sine_prod
import analysis.complex.locally_uniform_limit
import analysis.special_functions.trigonometric.bounds

noncomputable theory

open modular_form Eisenstein_series upper_half_plane topological_space set measure_theory
interval_integral metric filter function complex
open_locale interval real nnreal ennreal topology big_operators nat classical

local notation `ℍ'`:=(⟨upper_half_plane.upper_half_space, upper_half_plane_is_open⟩: open_subs)

local notation `ℍ` := upper_half_plane

def cot (z : ℂ) := (complex.cos z)/(complex.sin z)

lemma cot_exp (z : ℍ) : cot (↑π* z) =
  (complex.exp ( 2 *↑π * I * z) + 1)/(I* (1- complex.exp ( 2 *↑π * I * z))) :=
begin
rw [cot,sin,cos],
field_simp,
have h1 : (exp (↑π * ↑z * I) + exp (-(↑π * ↑z * I))) =  exp (-(↑π * ↑z * I)) * (exp (2* ↑π * ↑z * I) + 1),
by{rw mul_add,
rw ←exp_add,
simp,
apply congr_arg,
ring,},
have h2 : ((exp (-(↑π * ↑z * I)) - exp (↑π * ↑z * I)) * I) = I * exp (-(↑π * ↑z * I)) * (1 -exp (2* ↑π * ↑z * I)),
by {rw mul_sub,
simp_rw mul_assoc,
rw ←exp_add,
ring_nf,},
rw [h1,h2],
have h22: I * exp (-(↑π * ↑z * I)) * (1 -exp (2* ↑π * ↑z * I)) =
exp (-(↑π * ↑z * I)) * (I * (1 -exp (2* ↑π * ↑z * I))), by {ring},
rw h22,
rw mul_div_mul_left,
have h3 : complex.exp ( 2 *↑π * I * z) = complex.exp ( 2 *↑π * z * I), by {apply congr_arg,
ring,},
simp_rw h3,
apply exp_ne_zero,
end

lemma div_one_sub_exp (z : ℍ) : 1/ (1- complex.exp ( 2 *↑π * I * z)) =
  ∑'(n : ℕ), complex.exp ( 2 *↑π * I * z * n) :=
begin
simp,
apply symm,
have h :  ∑'(n : ℕ), complex.exp ( 2 *↑π * I * z * n) =  ∑'(n : ℕ), complex.exp ( 2 *↑π * I * z )^n,
by {apply tsum_congr,
intro b,
rw  ←exp_nat_mul,
ring_nf,},
rw h,
apply tsum_geometric_of_norm_lt_1,
apply exp_upper_half_plane_lt_one,
end


variables {R : Type*} [normed_ring R] [complete_space R]

lemma geo_succ (x : R) (h : ‖x‖ < 1) : ∑' i:ℕ, x^(i+1)=  (∑' i:ℕ, x^i) -1 :=
begin
  apply symm,
  rw sub_eq_iff_eq_add,
  rw tsum_eq_zero_add,
  simp only [pow_zero],
  apply add_comm,
  apply normed_ring.summable_geometric_of_norm_lt_1 x h,
end

lemma geom_series_mul_add (x : R) (h : ‖x‖ < 1) :
 x * (∑' i:ℕ, x ^ i)  = ∑' i:ℕ, x^(i+1)  :=
begin
have := ((normed_ring.summable_geometric_of_norm_lt_1 x h).has_sum.mul_left (x)),
  refine tendsto_nhds_unique this.tendsto_sum_nat _,
  have : tendsto (λ (n : ℕ), (∑ i in finset.range (n+1), x ^ i)-1) at_top (𝓝 ∑' i:ℕ, x^(i+1)),
  by {have hu :=(normed_ring.summable_geometric_of_norm_lt_1 x h).has_sum,
     have hj := geo_succ x h,
     rw hj,
     apply tendsto.sub_const,
     simp_rw finset.sum_range_succ,
     have hp : (tsum (pow x)) = (tsum (pow x)) + 0, by {simp},
     rw hp,
     apply tendsto.add,
     apply  has_sum.tendsto_sum_nat,
     apply summable.has_sum,
     apply normed_ring.summable_geometric_of_norm_lt_1 x h,
     apply (tendsto_pow_at_top_nhds_0_of_norm_lt_1 h),},
  convert ←this,
  ext n,
  have hh:= @geom_sum_succ _ _ x n,
  rw hh,
  simp only [add_sub_cancel],
  exact finset.mul_sum,
end




lemma geom_series_mul_one_add (x : R) (h : ‖x‖ < 1) :
(1+ x) * (∑' i:ℕ, x ^ i) = 2* (∑' i:ℕ, x ^ i) - 1 :=
begin
rw add_mul,
simp only [one_mul],
rw geom_series_mul_add x h,
rw geo_succ x h,
rw two_mul,
abel,
end

lemma pi_cot_q_exp (z : ℍ) : ↑π * cot (↑π* z) =
  ↑π * I- (2 *  ↑π * I)* ∑' (n : ℕ), complex.exp ( 2 *↑π * I * z * n) :=
begin
rw cot_exp,
have h1: ↑π * ((exp (2 * ↑π * I * ↑z) + 1) / (I * (1 - exp (2 * ↑π * I * ↑z)))) =
-↑π * I * ((exp (2 * ↑π * I * ↑z) + 1)* (1 /  ((1 - exp (2 * ↑π * I * ↑z))))),
by {rw div_mul_eq_div_mul_one_div,
simp,
ring,},
rw h1,
rw div_one_sub_exp z,
rw add_comm,
have :=geom_series_mul_one_add (exp (2 * ↑π * I * ↑z)) (exp_upper_half_plane_lt_one _),
have hh : ∑' (n : ℕ), complex.exp ( 2 *↑π * I * z * n) =
∑' (n : ℕ), complex.exp ( 2 *↑π * I * z)^n, by {
  apply tsum_congr,
  intro b,
  rw ←exp_nat_mul,
  ring_nf,
},
rw hh,
rw this,
ring,
end


lemma sin_piz_ne_zero (z : ℍ) : complex.sin (π * z) ≠ 0 :=
begin
sorry,

end


def log_deriv (f : ℂ  → ℂ) := deriv f / f

lemma cot_log_derv_sin (z : ℍ) : cot (π *z) = ((deriv sin) (π * z))/ sin (π * z) :=
begin
rw cot,
simp,
end

lemma log_derv_eq_derv_log (f : ℂ  → ℂ) (x : ℂ) (hf : f x ≠ 0): (log_deriv f) x =
(deriv ((complex.log) ∘ f) x) :=
begin
sorry,
end



lemma log_deriv_one : log_deriv 1 = 0 :=
begin
sorry,
end

lemma log_derv_mul (f g: ℂ → ℂ) (x : ℂ) (hfg : f x * g x ≠ 0) (hdf : differentiable_at ℂ f x)
 (hdg : differentiable_at ℂ g x) :
log_deriv (λz, f z * g z) x = log_deriv(f) x + log_deriv (g) x:=
begin
simp_rw log_deriv,
simp,
rw deriv_mul hdf hdg,
have h1 := (mul_ne_zero_iff.1 hfg).1,
have h2 := (mul_ne_zero_iff.1 hfg).2,
field_simp,
apply mul_comm,
end

lemma log_derv_prod {α : Type*} (s : finset  α) (f : α → ℂ → ℂ) (t : ℂ) (hf : ∀ x ∈ s, f x t ≠ 0)
   (hd : ∀ x ∈ s, differentiable_at ℂ (f x) t) :
  log_deriv (∏ i in s, f i) t = ∑ i in s, log_deriv (f i) t :=
begin
  induction s using finset.cons_induction_on with a s ha ih,
  { simp [log_deriv_one] },
  { rw [finset.forall_mem_cons] at hf,
    simp [ih hf.2], rw finset.prod_insert, rw finset.sum_insert, sorry, sorry, sorry,
   -- apply log_derv_mul,
   }
end

lemma log_derv_diff (f : ℂ → ℂ) (s : set ℂ) (hs : is_open s) (hf : differentiable_on ℂ f s) (x : s)
 (hf2 : ∀ x ∈ s, f x ≠ 0) : differentiable_on ℂ (log_deriv f) s :=
begin
rw log_deriv,
apply differentiable_on.div,
all_goals{sorry},


end

lemma log_deriv_congr (f g : ℂ → ℂ)  (hfg : f = g) : log_deriv f = log_deriv g :=
begin
apply congr,
refl,
exact hfg,
end

lemma log_deriv_comp (f g : ℂ → ℂ) (x : ℂ) (hf : differentiable_at ℂ f (g x) )
(hg : differentiable_at ℂ g x) : log_deriv (f ∘ g) x = ((log_deriv f) (g x)) * deriv g x :=
begin
simp_rw log_deriv,
simp,
rw (deriv.comp _ hf hg),
simp_rw mul_comm,
apply mul_assoc,
end


lemma log_deriv_of_sin_pi_mul (z : ℍ) (n : ℕ): log_deriv (complex.sin ∘  (λt, π * t)) =
log_deriv (λ x,  π * x * (∏ j in finset.range n, (1 - x ^ 2 / (j + 1) ^ 2)) *
(∫ y in 0..π/2, complex.cos (2 * x * y) * real.cos y ^ (2 * n)) / ↑∫ y in 0..π/2, real.cos y ^ (2 * n))  :=
begin
apply log_deriv_congr,
ext1,
apply euler_sine.sin_pi_mul_eq x n,
end

lemma log_deriv_sine (z : ℍ): log_deriv (complex.sin ∘  (λt, π * t)) z = π * cot(π * z) :=
begin
rw log_deriv_comp,
simp,
rw log_deriv,
simp,
rw cot,
apply mul_comm,
simp,
simp,
end

--lemma log_of_prod  (z : ℍ) (n : ℕ) :
 --log_deriv (λ x,  π * x * (∏ j in finset.range n, (1 - x ^ 2 / (j + 1) ^ 2))) =

lemma log_der_tendsto (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (x : ℍ') (hF : tendsto_locally_uniformly_on f g at_top ℍ')
  (hf : ∀ᶠ (n : ℕ) in at_top, differentiable_on ℂ (f n) ℍ') (hg : g x ≠0 ):
tendsto (λ n : ℕ, (log_deriv (f n) x)) at_top (𝓝 ((log_deriv g) x)) :=
begin
--have := continuous_at.tendsto,
--rw tendsto_at_top_nhds,
simp_rw log_deriv,
apply tendsto.div,
swap,
apply hF.tendsto_at,
apply x.2,
have := (hF.deriv) _ _,
have hf2 := this.tendsto_at,
apply hf2,
apply x.2,
apply hf,
apply upper_half_plane_is_open,
apply hg,
end


/-! ## Integration against `cos x ^ n`
The next few lemmas can be interpreted as stating that the distribution on `[0, π/2]` given by
integrating against `cos x ^ n` converges, after a suitable normalisation, to a Dirac distribution
at 0. -/

/-- If `f` has continuous derivative `f'` on `[a, b]`, then it satisfies a Lipschitz continuity
condition at `a`. (This is a simple special case of
`convex.lipschitz_on_with_of_nnnorm_has_deriv_within_le`.) -/
lemma norm_sub_le_mul_of_cont_diff {f f' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
  (hfd : ∀ (x:ℝ), x ∈ Icc a b → has_deriv_within_at f (f' x) (Icc a b) x)
  (hfc : continuous_on f' (Icc a b)) :
  ∃ (M : ℝ), ∀ (x : ℝ), x ∈ Icc a b → ‖f x - f a‖ ≤ M * (x - a) :=
begin
  obtain ⟨M, hM⟩ := is_compact.exists_bound_of_continuous_on is_compact_Icc hfc,
  have hM' : 0 ≤ M := le_trans (norm_nonneg _) (hM a (left_mem_Icc.mpr hab)),
  refine ⟨M, _⟩,
  have := convex.lipschitz_on_with_of_nnnorm_has_deriv_within_le (convex_Icc a b) hfd _,
  show nnreal, exact ‖M‖₊,
  { intros x hx,
    specialize this hx (left_mem_Icc.mpr hab),
    simp_rw edist_eq_coe_nnnorm_sub at this,
    rw [←ennreal.coe_mul, ennreal.coe_le_coe, ←nnreal.coe_le_coe, coe_nnnorm] at this,
    convert this,
    { rw [coe_nnnorm, real.norm_of_nonneg hM'] },
    { rw [coe_nnnorm, real.norm_of_nonneg (by linarith [hx.1] : 0 ≤ x - a)] } },
  { intros x hx,
    rw ←nnreal.coe_le_coe,
    simp_rw coe_nnnorm,
    convert hM x hx,
    exact real.norm_of_nonneg hM' }
end

/-- Bound for the integral of `x / (x ^ 2 + 1) ^ t`, for `t < 2`. -/
lemma integral_div_rpow_sq_add_one_le {t : ℝ} (y : ℝ) (ht : 2 < t) :
  ∫ (u : ℝ) in 0..y, u / (u ^ 2 + 1) ^ (t / 2) ≤ 1 / (t - 2) :=
begin
  calc ∫ u in 0..y, u / (u ^ 2 + 1) ^ (t / 2) = ∫ u in 0..y, u * (u ^ 2 + 1) ^ (-t / 2) :
    begin
      refine integral_congr (λ u hu, _),
      dsimp only,
      rw [div_eq_mul_inv, ←real.rpow_neg (add_nonneg (sq_nonneg u) zero_le_one), neg_div],
    end
  ... = ((1 + y ^ 2) ^ (-t / 2 + 1) / (2 * (-t / 2 + 1)) - 1 / (2 * (-t / 2 + 1))) :
    begin
      conv in (_ ^ 2 + _) { rw add_comm },
      rw [integral_mul_rpow_one_add_sq (by linarith : -t / 2 ≠ -1), zero_pow zero_lt_two,
        add_zero, real.one_rpow],
    end
  ... = (1 / (t - 2) - (1 + y ^ 2) ^ (-t / 2 + 1) / (t - 2)) :
    begin
      have : ∀ u:ℝ, u / (2 * (-t / 2 + 1)) = -u / (t - 2),
      { intro u,
        rw [mul_add, mul_one, ←mul_div_assoc, mul_div_cancel_left, neg_div, ←div_neg],
        congr' 1, ring,
        exact two_ne_zero },
      simp_rw this,
      rw [sub_eq_add_neg _ ((-1 : ℝ) / _), ←neg_div, neg_neg, add_comm _ (1 / (t - 2)),
        neg_div, ←sub_eq_add_neg],
    end
  ... ≤ 1 / (t - 2) :
    begin
      apply sub_le_self,
      refine div_nonneg (real.rpow_nonneg_of_nonneg _ _) _,
      linarith [sq_nonneg y],
      linarith,
    end
end

/-- If `f` is integrable on `[0, π/2]`, and `f x` satisfies a Lipschitz-continuity condition at `0`,
then the integral `∫ x in 0..π/2, f x * cos x ^ n` differs from `f 0 * ∫ x in 0..π/2, cos x ^ n` by
an `O(1 / n)` error. -/
lemma abs_integral_mul_cos_pow_sub_le
  {f : ℝ → ℂ} (hfi : interval_integrable f volume 0 (π/2))
  {M : ℝ} (hm : ∀ (x : ℝ), x ∈ Icc (0:ℝ) (π/2) → ‖f x - f 0‖ ≤ M * x) {n : ℕ} (hn : 2 < n) :
  ‖(∫ (x:ℝ) in 0..π/2, f x * real.cos x ^ n) - f 0 * (∫ (x:ℝ) in 0..π/2, real.cos x ^ n)‖
  ≤ M / (n - 2) :=
begin
  have m_nn : 0 ≤ M,
  { replace hm := (norm_nonneg _).trans (hm (π/2) (right_mem_Icc.mpr real.pi_div_two_pos.le)),
    rwa mul_nonneg_iff_left_nonneg_of_pos real.pi_div_two_pos at hm, },
  rw [sub_eq_add_neg, ←neg_mul, ←integral_const_mul, ←interval_integral.integral_add],
  swap, { apply hfi.mul_continuous_on (continuous.continuous_on _),
    sorry,},
  swap, { apply continuous.interval_integrable, sorry,
    --exact continuous_const.mul ((complex.continuous_of_real.comp continuous_cos).pow n)
    },
  refine (norm_integral_le_integral_norm real.pi_div_two_pos.le).trans _,
  -- Bound the LHS above by the integral of (M * x) / (x ^ 2 + 1) ^ (n / 2).
  -- (This creates several integrability side-goals.)
  refine (integral_mono_on real.pi_div_two_pos.le _ _ _).trans _,
  { exact λ x:ℝ, M * x / (x ^ 2 + 1) ^ (n / 2 : ℝ) },
  { refine (interval_integrable.add _ _).norm,
    { apply hfi.mul_continuous_on (continuous.continuous_on _), sorry,
     -- exact (complex.continuous_of_real.comp continuous_cos).pow n
     },
    { apply continuous.interval_integrable, sorry,
      --exact continuous_const.mul ((complex.continuous_of_real.comp continuous_cos).pow n)
      } },
  { apply continuous_on.interval_integrable,
    refine continuous_at.continuous_on (λ x hx, _),
    have : 0 < x ^ 2 + 1 := by { linarith [sq_nonneg x], },
    apply continuous_at.div,
    { exact continuous_at_id.const_mul _ },
    { apply continuous_at.rpow_const,
      { apply continuous.continuous_at,
        exact (continuous_pow 2).add continuous_const },
      { left, exact this.ne' } },
    { exact (real.rpow_pos_of_pos this _).ne', } },
  { intros x hx,
    have a1 : 0 ≤ real.cos x,
    { refine real.cos_nonneg_of_mem_Icc ⟨_, _⟩; linarith [real.pi_div_two_pos, hx.1, hx.2] },
    have a2 : 0 < x ^ 2 + 1 := by linarith [sq_nonneg x],
    have a3 : real.cos x ≤ 1 / real.sqrt (x ^ 2 + 1),
    { refine real.cos_le_one_div_sqrt_sq_add_one _ _; linarith [real.pi_div_two_pos, hx.1, hx.2] },
    rw [neg_mul, ←sub_eq_add_neg, ←sub_mul, norm_mul],
    refine le_trans (mul_le_mul_of_nonneg_right (hm x hx) (norm_nonneg _)) _,
    refine mul_le_mul_of_nonneg_left _ (mul_nonneg m_nn hx.1),
    rw [norm_pow, complex.norm_eq_abs, complex.abs_of_nonneg a1],
    convert pow_le_pow_of_le_left a1 a3 n,
    rw [←real.inv_rpow a2.le, ←real.rpow_nat_cast _ n],
    nth_rewrite 1 (by { field_simp, ring } : (n:ℝ) = 2 * (n / 2 : ℝ)),
    rw [real.rpow_mul (one_div_nonneg.mpr $ real.sqrt_nonneg _), one_div, real.inv_rpow (real.sqrt_nonneg _) 2],
    nth_rewrite 3 ←nat.cast_two,
    rw [real.rpow_nat_cast _ 2, real.sq_sqrt a2.le] },
  simp_rw [←mul_div, integral_const_mul],
  refine mul_le_mul_of_nonneg_left _ m_nn,
  rw ←one_div,
  refine integral_div_rpow_sq_add_one_le _ (_ : 2 < (n:ℝ)),
  rwa [←nat.cast_two, nat.cast_lt],
end

lemma le_integral_cos_pow (n : ℕ) :
  real.sqrt (π / 2 / (n + 1)) ≤ ∫ (x:ℝ) in 0..π/2, real.cos x ^ n :=
begin
  /-

  have nn : 0 < (n : ℝ) + 1 := by linarith [(nat.cast_nonneg _ : 0 ≤ (n:ℝ))],
  rw [euler_sine.integral_cos_pow_eq, ←div_le_iff' (by simp : 0 < (1 / 2 : ℝ)), ←div_mul, div_one],
  convert euler_sine.le_integral_sin_pow n,
  rw [←sq_eq_sq (mul_nonneg (sqrt_nonneg _) zero_le_two) (sqrt_nonneg _), mul_pow,
    sq_sqrt (div_pos pi_div_two_pos nn).le, sq_sqrt (div_pos two_pi_pos nn).le],
  field_simp [nn.ne'],
  ring,
  -/
  sorry,
end

lemma abs_integral_mul_cos_pow_div_sub_le
  {f : ℝ → ℂ} (hfi : interval_integrable f volume 0 (π/2))
  {M : ℝ} (hm : ∀ (x : ℝ), x ∈ Icc (0:ℝ) (π/2) → ‖f x - f 0‖ ≤ M * x) {n : ℕ} (hn : 2 < n) :
  ‖(∫ (x:ℝ) in 0..π/2, f x * real.cos x ^ n) / (∫ (x:ℝ) in 0..π/2, real.cos x ^ n) - f 0‖
  ≤ M / (n - 2) * real.sqrt (2 * (n + 1) / π) :=
begin
  have : ‖(∫ (x:ℝ) in 0..π/2, f x * real.cos x ^ n) / (∫ (x:ℝ) in 0..π/2, real.cos x ^ n) - f 0‖
    ≤ M / (n - 2) / (∫ (x:ℝ) in 0..π/2, real.cos x ^ n),
  { rw [le_div_iff (euler_sine.integral_cos_pow_pos n), ←real.norm_of_nonneg (euler_sine.integral_cos_pow_pos n).le,
    real.norm_eq_abs, ←complex.abs_of_real, ←complex.norm_eq_abs, ←norm_mul,
    ←interval_integral.integral_of_real],
    have : ∫ (x : ℝ) in 0..π/2, ((real.cos x ^ n : ℝ) : ℂ) = ∫ (x : ℝ) in 0..π/2, ((real.cos x : ℝ) : ℂ) ^ n,
    { simp_rw complex.of_real_pow },
    rw [this, sub_mul],
    convert abs_integral_mul_cos_pow_sub_le hfi hm hn,
    apply div_mul_cancel,
    rw [←this, interval_integral.integral_of_real, complex.of_real_ne_zero],
    exact (euler_sine.integral_cos_pow_pos n).ne' },
  refine this.trans _,
  have m_nn : 0 ≤ M,
  { replace hm := (norm_nonneg _).trans (hm (π/2) (right_mem_Icc.mpr real.pi_div_two_pos.le)),
    rwa mul_nonneg_iff_left_nonneg_of_pos real.pi_div_two_pos at hm, },
  conv_lhs { rw div_eq_mul_inv },
  refine mul_le_mul_of_nonneg_left _ (div_nonneg m_nn _),
  swap, { rw [sub_nonneg, ←nat.cast_two, nat.cast_le], exact hn.le },
  rw inv_le,
  { convert le_integral_cos_pow n,
    { rw ←real.sqrt_inv,
      congr' 1,
      rw [inv_div, div_div] } },
  { apply euler_sine.integral_cos_pow_pos },
  { apply real.sqrt_pos_of_pos,
    refine div_pos (mul_pos (zero_lt_two' ℝ) _) real.pi_pos,
    rw [←nat.cast_add_one, nat.cast_pos],
    linarith }
end

lemma auc (a b  : ℂ) : a*b-a = a*(b-1) :=
begin
exact (mul_sub_one a b).symm,

end

lemma auss  : tendsto_uniformly (λ n: ℕ, λ z : ℂ,  (∫ x in 0..π/2,
  complex.cos (2 * z * x) * real.cos x ^ (2 * n)) / ↑∫ x in 0..π/2, real.cos x ^ (2 * n)) 1 at_top :=
begin
rw tendsto_uniformly_iff,
simp_rw pi.one_apply,
simp,
simp_rw dist_eq_norm,
sorry,
end

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section has_prod
variables [comm_monoid α] [topological_space α]

def has_prod (f : ℕ → β  → α) (a : β → α) : Prop := tendsto (λ n : ℕ, ∏ b in finset.range n, f b) at_top (𝓝 a)

def prodable (f : ℕ → β → α) : Prop := ∃a, has_prod f a

@[irreducible] def tprod {β} (f : ℕ → β → α) := if h : prodable f then classical.some h else 1

notation `∏'` binders `, ` r:(scoped:67 f, tprod f) := r

noncomputable theory

lemma prodable.has_prod {f : ℕ → β → α} (ha : prodable f) : has_prod f (∏'b, f b) :=
by simp [ha, tprod]; exact classical.some_spec ha

lemma prod_be_exp (f : ℕ → ℂ) (s : finset ℕ) : (∏ i in s,  (1 + complex.abs (f i))) ≤
real.exp ( ∑ i in s, complex.abs (f i) ) :=
begin
rw real.exp_sum,
apply finset.prod_le_prod,
intros i hi,
apply add_nonneg,
linarith,
apply complex.abs.nonneg,
intros i hi,
rw add_comm,
apply real.add_one_le_exp_of_nonneg (complex.abs.nonneg _),
end



lemma prod_le_prod_abs (f : ℕ → ℂ) (n : ℕ)  : complex.abs ((∏ i in finset.range (n), ((f i) + 1)) - 1) ≤
  (∏ i in finset.range (n), (complex.abs (f i) + 1)) - 1 :=
begin
induction n with h,
simp only [finset.range_zero, finset.prod_empty, sub_self, absolute_value.map_zero],
have HH : ((∏ i in finset.range (h + 1), ((f i) + 1)) - 1) =
  ((∏ i in finset.range (h), ((f i) + 1)) - 1) * (f (h) + 1)+ f (h), by {
    simp_rw finset.prod_range_succ,
    ring},
rw HH,
have  H3: complex.abs (((∏ i in finset.range (h), ((f i) + 1)) - 1) * (f (h ) + 1) + f (h )) ≤
complex.abs(((∏ i in finset.range (h), ((f i) + 1)) - 1) * (f (h) + 1))+ complex.abs (f (h)),
by {
  apply le_trans (complex.abs.add_le _ _),
  simp only},
apply le_trans H3,
have H4: complex.abs(((∏ i in finset.range (h), ((f i) + 1)) - 1) * (f (h) + 1))+
  complex.abs (f (h)) ≤  ((∏ i in finset.range (h), (complex.abs (f i) + 1)) - 1) *
  (complex.abs ((f (h))) + 1) +  complex.abs (f (h)), by {
    simp only [absolute_value.map_mul, add_le_add_iff_right],
    have h1: complex.abs(((∏ i in finset.range (h), ((f i) + 1)) - 1)) ≤
    ((∏ i in finset.range (h), (complex.abs (f i) + 1)) - 1), by {
      apply n_ih},
    have h2 : complex.abs (f (h) + 1) ≤  (complex.abs ((f (h))) + 1), by {
        apply le_trans (complex.abs.add_le _ _),
        simp only [absolute_value.map_one],
       },
    apply mul_le_mul h1 h2,
    apply complex.abs.nonneg,
    apply le_trans _ n_ih,
    apply complex.abs.nonneg,},
apply le_trans H4,
ring_nf,
rw finset.prod_range_succ,
rw mul_comm,
end

--rw ←finset.prod_range_mul_prod_Ico

lemma prod_le_prod_abs_Ico (f : ℕ → ℂ) (n m: ℕ) : complex.abs ((∏ i in finset.Ico m n, ((f i) + 1)) - 1) ≤
  (∏ i in finset.Ico m n, (complex.abs (f i) + 1)) - 1 :=
begin
simp_rw finset.prod_Ico_eq_prod_range,
apply prod_le_prod_abs,
end

lemma prod_le_prod_abs_Ico_ond_add (f : ℕ → ℂ) (n m: ℕ) : complex.abs ((∏ i in finset.Ico m n, (1+ (f i))) - 1) ≤
  (∏ i in finset.Ico m n, (1 + complex.abs ((f i)))) - 1 :=
begin
convert prod_le_prod_abs_Ico f n m,
repeat {apply add_comm},
end


lemma unif_prod_bound (F : ℕ → ℂ → ℂ) (K : set ℂ)
  (hb : ∃ (T : ℝ), ∀ (x : ℂ), x ∈ K →   ∑' (n : ℕ), complex.abs (F n x) ≤ T)
   (hs : ∀ x : ℂ, summable (λ n : ℕ, ( (complex.abs (F n x))) )):
  ∃ (C : ℝ), 0 < C  ∧  ∀ (s : finset ℕ) (x : ℂ), x ∈ K →
  (∏ i in s,  (1 + complex.abs (F i x))) ≤ C :=
begin
obtain ⟨T, ht⟩:= hb,
have HB : ∀ (s : finset ℕ) (a : ℂ), ∑ i in s, complex.abs (F i a) ≤  ( ∑' (n : ℕ), complex.abs (F n a)),
by {intros n a,
    apply sum_le_tsum,
    intros b hb,
    apply complex.abs.nonneg,
    apply hs a},
have hexp : 0 < real.exp(T), by {have := (real.exp_pos T), apply this,},
refine ⟨real.exp (T),  _, ⟩ ,
simp [hexp],
intros n x hx,
apply le_trans (prod_be_exp _ _),
simp,
apply le_trans (HB n x),
exact ht x hx,
end

lemma fin_prod_le_exp_sum (F : ℕ → ℂ → ℂ)
  (hs : ∀ x : ℂ, summable (λ n : ℕ, ( (complex.abs (F n x))) )):
  ∀ (s : finset ℕ) (x : ℂ),
  (∏ i in s,  (1 + complex.abs (F i x))) ≤ real.exp ( ∑' i : ℕ, complex.abs (F i x) ) :=
begin
have HB : ∀ (s : finset ℕ) (a : ℂ), ∑ i in s, complex.abs (F i a) ≤  ( ∑' (n : ℕ), complex.abs (F n a)),
by {intros n a,
    apply sum_le_tsum,
    intros b hb,
    apply complex.abs.nonneg,
    apply hs a},
intros s x,
apply le_trans (prod_be_exp _ _),
simp,
apply HB s x,
end



lemma tsum_unif  (F : ℕ → ℂ → ℂ) (K : set ℂ)  (hf :  tendsto_uniformly_on
  (λ (n : ℕ), (λ (a : ℂ), ∑ i in (finset.range n), complex.abs (F i a)))
  ( (λ (a : ℂ), ∑' (n : ℕ), complex.abs (F n a))) filter.at_top K)
  (hs : ∀ x : ℂ, summable (λ n : ℕ, ( (complex.abs (F n x))) )):
  ∀ ε : ℝ , 0 < ε → ∃ (N : ℕ), ∀ (n : ℕ) (x : ℂ), x ∈ K → N ≤ n →
  complex.abs (∑' i : ℕ, complex.abs (F (i + N) x)) < ε  :=
begin
rw tendsto_uniformly_on_iff at hf,
simp at hf,
intros ε hε,
have HF := hf ε hε,
obtain ⟨N, hN⟩:= HF,
refine ⟨N,_⟩,
intros n x hx hn,
have hnn : N ≤ N, by {linarith},
have HN2 := hN N hnn x hx,
simp_rw dist_eq_norm at *,
convert HN2,
rw tsum_coe,
rw ← norm_eq_abs,
rw complex.norm_real,
congr,
have hy := sum_add_tsum_nat_add N (hs x),
simp at hy,
rw ←hy,
ring,
end


lemma abs_tsum_of_poss (F : ℕ → ℂ → ℝ ) (h : ∀ (n : ℕ) (c : ℂ), 0 ≤ F n c) : ∀ x : ℂ,
 |(∑'(i : ℕ), F i x) | = ∑' (i : ℕ), F i x :=
begin
intro x,
simp only [abs_eq_self],
apply tsum_nonneg,
intro b,
apply h b x,
end


lemma abs_tsum_of_pos (F: ℕ → ℂ → ℂ) : ∀ (x : ℂ) (N : ℕ),
  complex.abs ((∑' (i : ℕ), complex.abs (F (i + N) x)) : ℂ) = ∑' (i : ℕ), complex.abs (F (i + N) x) :=
begin
intros x N,
have := abs_tsum_of_poss (λ n : ℕ, λ x : ℂ, complex.abs (F (n + N) x)) _ x,
rw ←this,
simp,
rw ←abs_of_real _,
congr,
rw tsum_coe,
intros n c,
apply complex.abs.nonneg,
end

example (a b : ℝ) (hab : a ≤ b): a-1 ≤ b ↔ a ≤ 1 + b :=
begin
exact tsub_le_iff_left
end


lemma add_eq_sub_add (a b c d : ℝ) : b = c - a +d  ↔  a + b = c + d :=
begin
split,
repeat {intro h,
linarith [h]},
end


lemma sum_subtype_le_tsum (f: ℕ → ℝ) (m n N : ℕ) (hmn : m ≤ n ∧ N ≤ m)
 (hg: ∀ b , 0 ≤ f b) (hf : summable f) :
∑(i : ℕ) in finset.Ico m n, f i ≤ ∑' (i : ℕ), f (i + N) :=
begin
have h1 : ∑(i : ℕ) in finset.Ico m n, f i  ≤ ∑(i : ℕ) in finset.Ico N n, f i, by {
  have := finset.Ico_union_Ico_eq_Ico hmn.2 hmn.1,
  rw ←this,
  rw finset.sum_union,
  simp,
  apply finset.sum_nonneg,
  intros i hi,
  apply hg i,
  exact finset.Ico_disjoint_Ico_consecutive N m n,
},
apply le_trans h1,
have h2 :  ∑' (i : ℕ), f (i + N) = ∑(i : ℕ) in finset.Ico N n, f i + ∑' (i : ℕ), f (i + n),
by {
  have hh1 := sum_add_tsum_nat_add N hf,
  have hh2 := sum_add_tsum_nat_add n hf,
  rw ←hh2 at hh1,
  rw ←add_eq_sub_add at hh1,
  rw hh1,
  simp,
  have hNn : N ≤ n, by {exact le_trans hmn.2 hmn.1, },
  have :=  finset.sum_range_add_sum_Ico f hNn,
  rw ← this,
  simp,},
rw h2,
simp,
apply tsum_nonneg,
intro b,
apply hg (b+n),
end


lemma tsum_unifo  (F : ℕ → ℂ → ℂ) (K : set ℂ)  (hf :  tendsto_uniformly_on
  (λ (n : ℕ), (λ (a : ℂ), ∑ i in (finset.range n), complex.abs (F i a)))
  ( (λ (a : ℂ), ∑' (n : ℕ), complex.abs (F n a))) filter.at_top K)
  (hs : ∀ x : ℂ, summable (λ n : ℕ, ( (complex.abs (F n x))) )):
  ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ), ∀ (n m: ℕ) (x : ℂ), x ∈ K →  N ≤ n ∧ N ≤ m ∧ m ≤ n →
  (∏ i in finset.Ico (m) (n),  (1 + complex.abs (F i x))) - 1 ≤ ε  :=
begin
intros ε hε,
have hl : 0 < real.log(1 + ε), by {apply real.log_pos, linarith,},
have H2:= tsum_unif  F K hf hs (real.log( 1+ ε)) hl,
obtain ⟨N, hN⟩:= H2,
use N,
intros n m x hK h,
have HN2:= hN n x hK h.1,
apply le_trans (sub_le_sub_right (prod_be_exp _ _) 1),
rw ←real.exp_lt_exp at HN2,
have hll : 0 < 1 + ε, by {linarith},
rw (real.exp_log hll) at HN2,
rw tsub_le_iff_left,
apply le_trans _ (HN2.le),
simp,
have hss : summable (λ n : ℕ, ( (complex.abs (F (n + N) x))) ), by {have := hs x,
  rw  ← (summable_nat_add_iff N) at this,
  apply this,
  exact topological_add_group.mk,},
have := (abs_tsum _ (hss)),
rw (abs_tsum_of_pos F x N),
have := sum_add_tsum_nat_add N (hs x),
apply sum_subtype_le_tsum,
split,
apply h.2.2,
apply h.2.1,
intro b,
apply complex.abs.nonneg,
exact hs x,
end

lemma reggs (c e: ℝ) (ha : 0 ≤ c) (he : 0 < e): c * (e/c - 1) < e :=
begin
by_cases hc : c ≠ 0,
rw mul_sub,
rw mul_div_cancel' ,
simp,
exact (ne.symm hc).lt_of_le ha,
exact hc,
simp at hc,
rw hc,
simp,
exact he,
end

lemma auxreal (e : ℂ) : complex.abs (1- e) = complex.abs(e -1):=
begin
exact map_sub_rev abs 1 e,
end



lemma sum_prod_unif_conv (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (K : set ℂ) (hf :  tendsto_uniformly_on
  (λ (n : ℕ), (λ (a : ℂ), ∑ i in (finset.range n), complex.abs (F i a)))
  ( (λ (a : ℂ), ∑' (n : ℕ), complex.abs (F n a))) filter.at_top K)
  (hb : ∃ (T : ℝ), ∀ (x : ℂ), x ∈ K →   ∑' (n : ℕ), complex.abs (F n x) ≤ T)
  (hs : ∀ x : ℂ, summable (λ n : ℕ, ( (complex.abs (F n x))) ))
  (hp : ∀ x : ℂ, x ∈ K → tendsto (λ (n : ℕ), ( ∏ i in (finset.range n),  (1 + F i x) )) at_top (𝓝 (g x))):
  tendsto_uniformly_on  (λ (n : ℕ), (λ (a : ℂ), ∏ i in (finset.range n),  (1 + F i a) ))
   ( g ) filter.at_top K:=
begin
apply uniform_cauchy_seq_on.tendsto_uniformly_on_of_tendsto,
rw uniform_cauchy_seq_on_iff,
intros ε hε,
have H := tsum_unifo F K hf hs,
have H2 := unif_prod_bound F K hb hs,
obtain ⟨C, hCp, hC⟩:= H2,
have hdelta:= exists_pos_mul_lt hε C,
obtain ⟨δ, hδ⟩ := hdelta,
have HH := H (δ) hδ.1,
obtain ⟨N, HN⟩:= HH,
refine  ⟨N,_⟩,
intros n hn m hm x hx,
have hCm := hC (finset.range (m)) x,
have hCn := hC (finset.range (n)) x,
rw dist_eq_norm,
simp only [norm_eq_abs],
by_cases hmn:  m ≤ n,
rw ←finset.prod_range_mul_prod_Ico _ hmn,
rw ←mul_sub_one,
simp only [absolute_value.map_mul, abs_prod],
have A : ∏ (i : ℕ) in finset.range m, complex.abs(1 + F i x) ≤ C, by {
  apply le_trans _ (hCm hx),
  apply finset.prod_le_prod,
  intros i hi,
  apply complex.abs.nonneg,
  intros i hi,
  apply le_trans (complex.abs.add_le _ _),
  simp only [absolute_value.map_one],},
have B: complex.abs((∏ (i : ℕ) in  (finset.Ico m n), (1 + (F i x))) -1) ≤ δ, by {
  have HI := HN n m x hx,
  simp only [ and_imp] at HI,
  have HI2:= HI hn hm hmn,
  have:= (prod_le_prod_abs_Ico_ond_add (λ (i : ℕ), F i x) n m),
  simp at this,
  apply le_trans this,
  exact HI2,},
have AB := mul_le_mul A B _ hCp.le,
apply lt_of_le_of_lt AB,
apply hδ.2,

apply complex.abs.nonneg,
simp at hmn,
rw ←finset.prod_range_mul_prod_Ico _ hmn.le,
rw ←mul_one_sub,
simp only [absolute_value.map_mul, abs_prod],
have A : ∏ (i : ℕ) in finset.range n, complex.abs(1 + F i x) ≤ C, by {
  apply le_trans _ (hCn hx),
  apply finset.prod_le_prod,
  intros i hi,
  apply complex.abs.nonneg,
  intros i hi,
  apply le_trans (complex.abs.add_le _ _),
  simp only [absolute_value.map_one],},
have B: complex.abs((∏ (i : ℕ) in  (finset.Ico n m), (1 + (F i x))) -1) ≤ δ, by {
  have HI := HN m n x hx,
  simp only [ and_imp] at HI,
  have HI2:= HI hm hn hmn.le,
  have:= (prod_le_prod_abs_Ico_ond_add (λ (i : ℕ), F i x) m n),
  simp at this,
  apply le_trans this,
  exact HI2,},
have AB := mul_le_mul A B _ hCp.le,
rw auxreal _,
apply lt_of_le_of_lt AB,
apply hδ.2,

apply complex.abs.nonneg,


exact hp,
end

lemma tendsto_unif_on_restrict (f: ℕ → ℂ → ℝ ) (g : ℂ → ℝ) (K : set ℂ) :
 tendsto_uniformly_on f g at_top K ↔ tendsto_uniformly (λ n : ℕ,  λ k : K,  f n k)
 (λ k : K, g k) at_top :=
begin
rw tendsto_uniformly_iff,
rw tendsto_uniformly_on_iff,
simp,
end

lemma tendst_unif_coe (K : set ℂ) (f: ℕ → K → ℝ ) (g : K → ℝ)  :
tendsto_uniformly (λ n : ℕ,  λ k : K,  ((f n k) : ℂ)) (λ n : K, ((g n) : ℂ)) at_top
  ↔ tendsto_uniformly (λ n : ℕ,  λ k : K,  f n k) (λ k : K, g k) at_top :=
begin
simp_rw tendsto_uniformly_iff,
simp,
sorry,
end

lemma assa (r : ℝ) (z :  ℂ) (x : ball z r) : complex.abs(x) ≤ complex.abs(z) +r :=
begin
have hx : (x : ℂ) = (x - z) + z, by {ring},
rw hx,
apply le_trans (complex.abs.add_le (x - z) z),
rw add_comm,
simp,
have hxx := x.2,
simp at hxx,
rw dist_eq_norm at hxx,
simpa using hxx.le,
end

lemma summable_rie_twist (x : ℂ):  summable (λ (n : ℕ), complex.abs (x ^ 2 / (↑n + 1) ^ 2)) :=
begin
simp,
simp_rw div_eq_mul_inv,
apply summable.mul_left,
have hs : summable (λ (n : ℕ), ((n : ℝ) + 1) ^ 2)⁻¹, by {
  norm_cast,
  simp,
  have h2 : (1 : ℤ)  < 2, by {linarith},
  have := int_Riemann_zeta_is_summmable 2 h2,
  rw rie at this,
  rw  ←(summable_nat_add_iff 1) at this,
  norm_cast at this,
  simpa using this,
  exact topological_add_group.mk,
  },
apply summable.congr hs,
intros b,
simp,
rw ←complex.abs_pow,
norm_cast,
end

lemma rie_twist_bounded_on_ball (z : ℂ) (r: ℝ) (hr : 0 < r):
 ∃ (T : ℝ), ∀ (x : ℂ), x ∈ ball z r → ∑' (n : ℕ), complex.abs (-x ^ 2 / (↑n + 1) ^ 2) ≤ T :=
begin
refine ⟨ (∑' (n : ℕ), (complex.abs(z) +r)^2 /complex.abs ((n+1)^2)), _  ⟩,
intros x hx,
simp only [map_div₀, absolute_value.map_neg, complex.abs_pow],
have := summable_rie_twist x,
apply tsum_le_tsum,
intro b,
simp only,
apply div_le_div_of_le,
apply pow_two_nonneg,
apply pow_le_pow_of_le_left,
apply complex.abs.nonneg,
apply assa r z ⟨x, hx⟩,
convert this,
ext1,
field_simp,
simp_rw div_eq_mul_inv,
apply summable.mul_left,
convert (summable_rie_twist (1 : ℂ)),
ext1,
field_simp,
end

lemma euler_sin_prod' (x : ℂ) (h0 : x ≠ 0):
tendsto (λ (n : ℕ), ∏ (i : ℕ) in finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2)) at_top
(𝓝 ((λ (t : ℂ), sin (↑π * t) / (↑π * t)) x)) :=
begin
have := tendsto_euler_sin_prod x,
rw metric.tendsto_at_top at *,
intros ε hε,
have hh : ↑π * x ≠ 0, by {apply mul_ne_zero, norm_cast, apply real.pi_ne_zero, apply h0,},
have hex: 0 < ε * complex.abs(π * x), by {apply mul_pos, apply hε, apply complex.abs.pos, apply hh},
have h1:= this (ε * complex.abs(π * x)) hex,
obtain ⟨N, hN⟩:= h1,
refine ⟨N,_⟩,
intros n hn,
have h2:= hN n hn,
simp,
rw dist_eq_norm at *,
have : ∏ (i : ℕ) in finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2) - sin (↑π * x) / (↑π * x) =
 (↑π * x * ∏ (i : ℕ) in finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2) - sin (↑π * x)) / (↑π * x),
 by {
    have := sub_div' (sin (↑π * x) ) (∏ (i : ℕ) in finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2))
      ( ↑π * x) hh,
    simp at *,
    rw this,
    ring,
       },
rw this,
--have hpix : 0 ≠ complex.abs (↑π * x), by {sorry},
field_simp,
rw div_lt_iff,
convert h2,
ext1,
rw sub_eq_add_neg,
field_simp,
simp only [absolute_value.map_mul, abs_of_real],
apply mul_pos,
simpa using real.pi_ne_zero,
apply complex.abs.pos,
exact h0,
end

lemma tendsto_locally_uniformly_euler_sin_prod' (z : ℍ) (r : ℝ):
  tendsto_uniformly_on
  (λ n:ℕ, λ z : ℂ,  (∏ j in finset.range n, (1 + - z ^ 2 / (j + 1) ^ 2)))
  (λ t, (complex.sin (π * t))/ ↑π * t) at_top  (ball z r):=
begin
by_cases hr : 0 < r ,
apply sum_prod_unif_conv _ (λ t, (complex.sin (π * t))/ ↑π * t) (ball z r),
have := tendsto_unif_on_restrict _ _ (ball z r),
rw this,
simp only [map_div₀, absolute_value.map_neg, complex.abs_pow],
set s : ℝ := complex.abs(z)+r,
have HH:= M_test_uniform _ (λ (n : ℕ) (x :  (ball z r)), complex.abs(x^2/(n+1)^2)) (λ (n : ℕ), complex.abs(s^2/(n+1)^2)) _ _,
rw ←tendst_unif_coe _ _ _,
convert HH,
simp only [coe_finset_sum, map_div₀, complex.abs_pow],
funext,
rw tsum_coe,
congr,
simp only [map_div₀, complex.abs_pow],
simp only [hr, nonempty_coe_sort, nonempty_ball],
intros n x,
simp only [map_div₀, complex.abs_pow, of_real_div, of_real_pow, abs_of_real, complex.abs_abs, of_real_add],
apply div_le_div_of_le,
apply pow_two_nonneg,
apply pow_le_pow_of_le_left (complex.abs.nonneg _),
convert assa r z x,
norm_cast,
simp only [abs_eq_self],
apply add_nonneg (complex.abs.nonneg _) (hr.le),
apply (summable_rie_twist s),
apply rie_twist_bounded_on_ball z r hr,
intro x,
convert (summable_rie_twist x),
ext1,
field_simp,
intros x hx,
have := tendsto_euler_sin_prod x,
sorry,
sorry,
/-
have := tendsto_euler_sin_prod z,
rw metric.tendsto_at_top at this,
have hh := auss,
apply uniform_cauchy_seq_on.tendsto_uniformly_on_of_tendsto,
rw uniform_cauchy_seq_on_iff,
intros ε hε,

rw tendsto_uniformly_iff at *,


set c : ℝ  := complex.abs (↑π * z * (∏ j in finset.range 3, (1 - z ^ 2 / (j + 1) ^ 2))),
intros ε hε,
have he : 0 < ε/c, by {sorry},
have hh2 := hh (ε/c) he,
simp at *,
obtain ⟨aa, H⟩ := hh2,
set a : ℕ := max 3 aa,
refine ⟨a,_⟩,
intros b hb x,
rw (euler_sine.sin_pi_mul_eq x b),
simp,
simp_rw dist_eq_norm at *,

/-
have A: tendsto_uniformly (λ n : ℕ, λ z : ℂ,
(∫ x in 0..π/2, complex.cos (2 * z * x) * real.cos x ^ (2 * n)) / ↑∫ x in 0..π/2, real.cos x ^ (2 * n))
1 at_top,
by {sorry},
have B : tendsto_uniformly  (λ n:ℕ, λ z : ℂ, ↑π * z * (∏ j in finset.range b, (1 - z ^ 2 / (j + 1) ^ 2)))
 (λ z : ℂ, ↑π * z * (∏ j in finset.range b, (1 - z ^ 2 / (j + 1) ^ 2))) at_top, by {sorry},
haveI : group ℂ, by {sorry},
have C:= tendsto_uniformly.mul A B,
-/

-/




end



lemma tendsto_euler_log_derv_sin_prodd (x : ℍ):
  tendsto  ( (λ n:ℕ,  log_deriv  (λ z, ↑π * (z : ℂ)  * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2))) x))
  at_top (𝓝 $ log_deriv (complex.sin ∘ (λ t, π * t)) x) :=
begin
--rw metric.tendsto_at_top,
--simp,
have := log_der_tendsto
  ( (λ n:ℕ,  (λ z, ↑π * (z : ℂ)  * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2))) ))
  (complex.sin ∘ (λ t, π * t)) (x) ,
apply this,

all_goals {sorry},

end
#exit

--lemma logder (f : ℕ → ℂ → ℂ) (x a : ℂ) (hx : f x ≠ 0) (hf : tendsto f at_top (𝓝 a))

lemma tendsto_euler_log_sin_prod' (z : ℍ) :
  tendsto  (complex.log ∘  (λ n:ℕ, (↑π * z * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)))))
  at_top (filter.map complex.log ((𝓝 $ (complex.sin (π * z))))) :=
begin
apply tendsto.comp,
swap,
apply tendsto_euler_sin_prod,
apply tendsto_map,
end

lemma clog_der11 (f : ℂ → ℂ) {f' x : ℂ} (h₁ : has_deriv_at f f' x)  (h₂ : f x ≠ 0)
 (h3 : (f x).re < 0 ∧ (f x).im = 0) :
 has_deriv_within_at (λ t, log (complex.abs (f t))) (f' / f x) {z : ℂ | 0 ≤ x.im} x :=
begin
have h1 : 0 < complex.abs (f x).re ∨ complex.abs(f x).im ≠ 0, by {sorry},
have h2: has_deriv_within_at (λ y, (complex.abs (f y) : ℂ)) (complex.abs f')  {z : ℂ | 0 ≤ x.im} x, by {sorry},
have h4:= has_deriv_within_at.clog h2 ,

sorry,
end


lemma clog_der1 (f : ℂ → ℂ) {f' x : ℂ} (h₁ : has_deriv_at f f' x)  (h₂ : f x ≠ 0)
 (h3 : (f x).re < 0 ∧ (f x).im = 0) :
 has_deriv_within_at (λ t, log (f t)) (f' / f x) {z : ℂ | 0 ≤ x.im} x :=
begin
rw has_deriv_within_at_iff_tendsto,
have h1:= tendsto_log_nhds_within_im_nonneg_of_re_neg_of_im_zero h3.1 h3.2,

have h23 := clog_der11 f h₁ h₂ h3,
rw has_deriv_within_at_iff_tendsto at h23,
apply tendsto.congr' _ h23,


end

lemma clog_der (f : ℂ → ℂ) {f' x : ℂ} (h₁ : has_deriv_at f f' x)  (h₂ : f x ≠ 0) :
 has_deriv_at (λ t, log (f t)) (f' / f x) x :=
begin

by_cases 0 ≤  (f x).re ∨ (f x).im ≠ 0,
sorry,
--apply has_deriv_at.clog h₁ h,
rw decidable.not_or_iff_and_not at h,
simp at h,
have h1:= tendsto_log_nhds_within_im_nonneg_of_re_neg_of_im_zero h.1 h.2,
have h2:= tendsto_log_nhds_within_im_neg_of_re_neg_of_im_zero h.1 h.2,
have hh :  has_deriv_within_at (λ t, log (f t)) (f' / f x) {z : ℂ | 0 ≤ x.im} x, by {sorry},




end


lemma has_strict_deriv_at_logg {x : ℂ} (h : x ≠ 0) :
  has_strict_deriv_at log x⁻¹ x :=
begin
by_cases 0 ≤ x.re ∨ x.im ≠ 0,
sorry,
rw decidable.not_or_iff_and_not at h,
simp at h,

end


lemma der_log_sin_eq_cott (x : ℍ') : has_deriv_at (complex.log ∘ (λ z, sin (π * z)) ) ((π : ℂ) * cot(π * x))  x:=
begin
rw has_deriv_at_iff_tendsto,
simp,
sorry,
end


lemma tendsto_der_euler_log_sin_prod' (z : ℍ) :
  tendsto  (deriv complex.log ∘  (λ n:ℕ, (↑π * z * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)))))
  at_top (𝓝 $ deriv (complex.log  ∘ complex.sin) (π * z))  :=
begin
apply tendsto.comp,
swap,
apply tendsto_euler_sin_prod,
apply continuous_at.tendsto,


sorry,
end


lemma tendsto_euler_log_sin_prod (z : ℍ)
(hz : 0 < (complex.sin (π * z)).re ∨ (complex.sin (π * z)).im ≠ 0 ) :
  tendsto  (complex.log ∘  (λ n:ℕ, (↑π * z * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)))))
  at_top (𝓝 $ complex.log (complex.sin (π * z))) :=
begin
apply tendsto.comp,
swap,
apply tendsto_euler_sin_prod,
apply continuous_at.tendsto,
apply continuous_at_clog,
apply hz,
end

lemma tendsto_euler_log_sin_prodd (z : ℍ):
  tendsto  (complex.log ∘  (λ n:ℕ, (↑π * z * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)))))
  at_top (𝓝 $ complex.log (complex.sin (π * z))) :=
begin
apply tendsto.comp,
swap,
apply tendsto_euler_sin_prod,
apply continuous_at.tendsto,
by_cases 0 ≤ (complex.sin (π * z)).re ∨ (complex.sin (π * z)).im ≠ 0,
sorry,
--apply continuous_at_clog h,
apply continuous_within_at.continuous_at,
apply continuous_within_at_log_of_re_neg_of_im_zero,
rw decidable.not_or_iff_and_not at h,
simp at h,
apply h.1,
rw decidable.not_or_iff_and_not at h,
simp at h,
apply h.2,
rw decidable.not_or_iff_and_not at h,
simp at h,
rw mem_nhds_subtype_iff_nhds_within,

end

lemma tendsto_euler_log_sin_prod'' (z : ℍ)
(hz : (complex.sin (π * z)).re < 0 ∧ (complex.sin (π * z)).im = 0 ) :
  tendsto  (complex.log ∘  (λ n:ℕ, (↑π * z * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)))))
  at_top (𝓝 $ (real.log (complex.abs((complex.sin (π * z)))) + I*π)) :=
begin
apply tendsto.comp,
swap,
apply tendsto_euler_sin_prod,
have := tendsto_log_nhds_within_im_nonneg_of_re_neg_of_im_zero hz.1 hz.2,

sorry,
end



lemma cot_series_rep (z : ℍ) : ↑π * cot (↑π* z) - 1/z =
 ∑' (n : ℕ+), (1/(z-n)+1/(z+n)) :=
begin
apply symm,
refine (has_sum.tsum_eq _),
sorry,
end
