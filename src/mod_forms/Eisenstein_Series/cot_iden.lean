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


def log_deriv (f : ℂ → ℂ) := deriv f / f

lemma cot_log_derv_sin (z : ℍ) : cot (π *z) = ((deriv sin) (π * z))/ sin (π * z) :=
begin
rw cot,
simp,
end



lemma tendsto_euler_log_sin_prod' (z : ℍ) :
  tendsto  (complex.log ∘  (λ n:ℕ, (↑π * z * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)))))
  at_top (filter.map complex.log ((𝓝 $ (complex.sin (π * z))))) :=
begin
apply tendsto.comp,
swap,
apply tendsto_euler_sin_prod,
apply tendsto_map,
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
