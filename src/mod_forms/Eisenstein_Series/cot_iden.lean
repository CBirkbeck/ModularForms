import data.complex.exponential
import mod_forms.Eisenstein_Series.Eisen_is_holo
import mod_forms.Eisenstein_Series.exp_summable_lemmas
import analysis.special_functions.trigonometric.euler_sine_prod

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
(deriv (complex.log)) (f x) :=
begin
sorry,
end



lemma log_deriv_one : log_deriv 1 = 0 :=
begin
sorry,
end

lemma log_derv_mul (f g: ℂ → ℂ) (x : ℂ) (hfg : f x * g x ≠ 0) (hdf : differentiable_at ℂ f x)
 (hdg : differentiable_at ℂ g x) :
log_deriv (λz, f z * g z) x= log_deriv(f) x + log_deriv (g) x:=
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


lemma tendsto_euler_log_derv_sin_prodd (x : ℍ):
  tendsto  ( (λ n:ℕ,  log_deriv  (λ z, ↑π * (z : ℂ)  * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2))) x))
  at_top (𝓝 $ log_deriv (complex.sin) (π * x)) :=
begin
sorry,

end


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
  at_top (𝓝 $ deriv complex.log (complex.sin (π * z)))  :=
begin
apply tendsto.comp,
swap,
apply tendsto_euler_sin_prod,
apply continuous_at.tendsto,
rw ← log_derv_eq_derv_log,

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
