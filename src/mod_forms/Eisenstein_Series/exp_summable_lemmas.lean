import data.complex.exponential
import analysis.calculus.iterated_deriv
import analysis.calculus.series
import mod_forms.Eisenstein_Series.tsum_lemmas
import for_mathlib.mod_forms2
import mod_forms.holomorphic_functions
import analysis.complex.upper_half_plane.basic
import mod_forms.Eisenstein_Series.Eisenstein_series_index_lemmas
import mod_forms.Eisenstein_Series.iterated_deriv_lemmas
import analysis.special_functions.exp_deriv

noncomputable theory

open modular_form Eisenstein_series upper_half_plane topological_space set  metric filter function complex
open_locale interval real nnreal ennreal topology big_operators nat classical

local notation `ℍ` := upper_half_plane
local notation `ℍ'`:=(⟨upper_half_plane.upper_half_space, upper_half_plane_is_open⟩: open_subs)




lemma exp_upper_half_plane_lt_one (z : ℍ) : complex.abs (complex.exp ( 2 *↑π * I * z)) < 1 :=
begin
rw ←upper_half_plane.re_add_im,
rw mul_add,
rw exp_add,
simp only [absolute_value.map_mul],
have h1 : complex.abs (exp (2 * ↑π * I * ↑(z.re))) = complex.abs (exp ((2 * ↑π  * ↑(z.re)) * I )),
  by {ring_nf},
rw h1,
norm_cast,
have := abs_exp_of_real_mul_I (2 * π * z.re),
rw this,
simp only [of_real_mul, of_real_bit0, of_real_one, one_mul],
have h2 :  complex.abs (exp (2 * ↑π * I * (↑(z.im) * I))) =
  complex.abs (exp (2 * ↑π * (↑(z.im) * I^2))), by {ring_nf,},
rw h2,
simp only [I_sq, mul_neg, mul_one],
norm_cast,
simp only [real.abs_exp, real.exp_lt_one_iff, right.neg_neg_iff],
apply mul_pos,
apply real.two_pi_pos,
exact z.2,
end

lemma summable_iter_derv' (k : ℕ) (y : ℍ'):
  summable (λ (n : ℕ), (2 *↑π * I * n)^k * complex.exp ( 2 *↑π * I * n * y)) :=
begin
apply summable_of_summable_norm,
simp,
have hv1 : ∀ b : ℕ ,   (b : ℝ)^k * (complex.abs (complex.exp ( 2 *↑π * I * y)))^(b : ℕ) =
 b^k * complex.abs (complex.exp ( 2 *↑π * I * b * y)), by {intro b,
  rw ←complex.abs_pow, congr, rw ←exp_nat_mul, ring_nf},
simp_rw mul_pow,
have h2ne : (2 : ℝ)^k ≠ 0, by {apply pow_ne_zero, exact ne_zero.ne 2,},
simp_rw mul_assoc,
rw (summable_mul_left_iff h2ne),
rw (summable_mul_left_iff _),
simp_rw ←mul_assoc,
apply summable.congr _ hv1,
apply summable_pow_mul_geometric_of_norm_lt_1,
simp,
apply exp_upper_half_plane_lt_one,
exact topological_semiring.mk,
apply pow_ne_zero,
simpa using real.pi_ne_zero,
end

lemma summable_pow_mul_exp  {k : ℕ} (z : ℍ) :
  summable (λ (i : ℕ+), complex.abs (2 * ↑i ^ (k + 1) * exp (2 * ↑π * I * ↑z * ↑i))) :=
begin
simp,
have h2ne : (2 : ℝ) ≠ 0, by {exact ne_zero.ne 2,},
simp_rw mul_assoc,
rw (summable_mul_left_iff h2ne),
simp_rw ←coe_coe,
have hv1 : ∀ (b : ℕ+), complex.abs (complex.exp ( 2 *↑π * I * z * b)) =
  (complex.abs (complex.exp ( 2 *↑π * I * z)))^(b : ℕ), by {intro b,
  rw ←complex.abs_pow, congr, rw ←exp_nat_mul, ring_nf},
simp_rw ←mul_assoc,
simp_rw hv1,
simp_rw coe_coe,
have lj :=nat_pos_tsum (λ (x : ℕ), (x : ℝ)^(k+1)* (complex.abs (complex.exp ( 2 *↑π * I * z)))^x ),
simp at lj,
rw lj,
apply summable_pow_mul_geometric_of_norm_lt_1,
simp,
apply exp_upper_half_plane_lt_one,
end

lemma exp_iter_deriv (n m : ℕ)  :
  iterated_deriv n (λ (s : ℂ), complex.exp ( 2 *↑π * I * m * s)) =
  (λ t, (2 *↑π * I * m)^n * complex.exp ( 2 *↑π * I * m * t)) :=
begin
induction n with n IH,
simp,
funext x,
rw iterated_deriv_succ,
rw IH,
simp,
ring_exp,
end

lemma iterated_deriv_within_of_is_open (n m : ℕ)  :
  eq_on (iterated_deriv_within n (λ (s : ℂ), complex.exp ( 2 *↑π * I * m * s)) ℍ')
    (iterated_deriv n (λ (s : ℂ), complex.exp ( 2 *↑π * I * m * s))) ℍ' :=
begin
 induction n with n IH,
  { assume x hx,
    simp  },
  { assume x hx,
    rw [iterated_deriv_succ, iterated_deriv_within_succ],
    dsimp,
    rw deriv_within_of_open  upper_half_plane_is_open,
    apply filter.eventually_eq.deriv_eq,
    filter_upwards [upper_half_plane_is_open.mem_nhds hx],
    apply IH,
    exact hx,
    apply is_open.unique_diff_within_at upper_half_plane_is_open hx,

    }

end

lemma exp_iter_deriv_within (n m : ℕ)   :
  eq_on (iterated_deriv_within n (λ (s : ℂ), complex.exp ( 2 *↑π * I * m * s)) ℍ')
  (λ t, (2 *↑π * I * m)^n * complex.exp ( 2 *↑π * I * m * t)) ℍ':=
begin
apply eq_on.trans (iterated_deriv_within_of_is_open n m),
rw eq_on,
intros x hx,
apply congr_fun (exp_iter_deriv n m),
end

lemma exp_iter_deriv_apply (n m : ℕ) (x : ℂ) :
  (iterated_fderiv ℂ n (λ (s : ℂ), complex.exp ( 2 *↑π * I * m * s))) x (λ(i : fin n), 1) =
   (2 *↑π * I * m)^n * complex.exp ( 2 *↑π * I * m * x) :=
begin
  apply congr_fun (exp_iter_deriv n m),
end


def uexp (n : ℕ) : ℍ' → ℂ :=
λ z, complex.exp ( 2 *↑π * I * z * n)

def funn (K: set ℂ) (hk1 : K ⊆ upper_half_space) (hk2 : is_compact K) : continuous_map K ℂ :={
  to_fun := (λ (r : K),  complex.exp ( 2 *↑π * I * r ))
}

def funn_n (K: set ℂ) (hk1 : K ⊆ upper_half_space) (hk2 : is_compact K) (n k : ℕ) : continuous_map K ℂ :={
  to_fun := (λ (r : K), (2 * π * I * n)^k * complex.exp ( 2 *↑π * I * r ))
}



lemma der_iter_eq_der_aux2 (k n : ℕ) (r : ↥upper_half_space) :
  differentiable_at ℂ (λ (z : ℂ), iterated_deriv_within k (λ (s : ℂ),  complex.exp ( 2 *↑π * I * n * s)) upper_half_space z) ↑r :=
begin
simp at *,
have hh : differentiable_on ℂ (λ t, (2 *↑π * I * n)^k * complex.exp ( 2 *↑π * I * n * t)) ℍ', by {
  apply differentiable.differentiable_on, simp,},
apply differentiable_on.differentiable_at,
apply differentiable_on.congr  hh,
intros x hx,
apply exp_iter_deriv_within k n hx,
apply upper_half_plane_is_open.mem_nhds r.2,
end

lemma der_iter_eq_der2 (k n : ℕ) (r : ↥upper_half_space) :
 deriv (iterated_deriv_within k (λ (s : ℂ),  complex.exp ( 2 *↑π * I * n * s)) ℍ') ↑r =
 deriv_within (iterated_deriv_within k (λ (s : ℂ),  complex.exp ( 2 *↑π * I * n * s)) ℍ' ) ℍ' ↑r :=
begin
simp,
apply symm,
apply differentiable_at.deriv_within,
apply der_iter_eq_der_aux2,
apply is_open.unique_diff_on upper_half_plane_is_open ,
apply r.2,
end

lemma der_iter_eq_der2' (k n : ℕ) (r : ↥upper_half_space) :
 deriv (iterated_deriv_within k (λ (s : ℂ),  complex.exp ( 2 *↑π * I * n * s)) ℍ') ↑r =
 iterated_deriv_within (k+1) (λ (s : ℂ),  complex.exp ( 2 *↑π * I * n * s)) ℍ'  ↑r :=
begin
rw der_iter_eq_der2 k n r,
rw iterated_deriv_within_succ,
apply is_open.unique_diff_on upper_half_plane_is_open ,
apply r.2,
end

lemma cray (n : ℕ) : 0 ≤ 2 * |π| * n :=
begin
apply mul_nonneg,
apply mul_nonneg,
linarith,
simp,
apply nat.cast_nonneg,
end

lemma iter_deriv_comp_bound2 (K : set ℂ) (hK1 : K ⊆ ℍ') (hK2 : is_compact K) (k : ℕ) :
(∃ (u : ℕ → ℝ), ( summable u ∧
∀ (n : ℕ) (r : K),
(complex.abs (deriv (iterated_deriv_within k (λ (s : ℂ),  complex.exp ( 2 *↑π * I * n * s)) ℍ') r)) ≤ u n )) :=
begin
  haveI : compact_space K, by {rw ←is_compact_univ_iff, rw is_compact_iff_is_compact_univ at hK2, apply hK2, },
  have hg := bounded_continuous_function.mk_of_compact (funn K hK1 hK2),
  set r : ℝ := ‖bounded_continuous_function.mk_of_compact (funn K hK1 hK2) ‖,
  have hr : ‖ bounded_continuous_function.mk_of_compact (funn K hK1 hK2)‖ < 1,
  by {rw bounded_continuous_function.norm_lt_iff_of_compact,
    intro x, rw bounded_continuous_function.mk_of_compact_apply, simp_rw funn,
    simp only [continuous_map.coe_mk, norm_eq_abs],
    apply exp_upper_half_plane_lt_one ⟨x.1 ,(hK1 x.2)⟩, linarith, },
have hr2 : 0 ≤ r, by {simp only [norm_nonneg], },
  have hu : summable (λ (n : ℕ),  complex.abs (( 2 *↑π * I * n)^(k+1) * r^n)),
 by {
  simp,
  simp_rw mul_pow,
  have h2ne : (2 : ℝ)^(k+1) ≠ 0, by {apply pow_ne_zero, exact ne_zero.ne 2,},
simp_rw mul_assoc,
rw (summable_mul_left_iff h2ne),
rw (summable_mul_left_iff _),
apply summable_pow_mul_geometric_of_norm_lt_1,
simp at *,
apply hr,
exact topological_semiring.mk,
apply pow_ne_zero,
simpa using real.pi_ne_zero,},
refine ⟨λ (n : ℕ),  complex.abs (( 2 *↑π * I * n)^(k+1) * r^n), hu,_⟩,
intros n t,
have go:= (der_iter_eq_der2' k n ⟨t.1, hK1 t.2⟩),
simp at *,
simp_rw go,
have h1:= exp_iter_deriv_within (k+1) n (hK1 t.2),
simp only [subtype.val_eq_coe, opens.coe_mk] at *,
rw h1,
simp,
have ineqe : complex.abs (complex.exp (2 * π * I * n * t)) ≤ ‖ r ‖^n, by {
  have hw1 : complex.abs (complex.exp (2 * π * I * n * t)) = complex.abs (complex.exp (2 * π * I * t))^n,
  by { rw ←complex.abs_pow, congr, rw ←exp_nat_mul, ring_nf,},
  rw hw1,
  apply le_of_pow',
  apply complex.abs.nonneg,
  simp only [norm_nonneg],
  have := bounded_continuous_function.norm_coe_le_norm
    (bounded_continuous_function.mk_of_compact (funn K hK1 hK2)) t,
    simp at *,
   exact this},
apply mul_le_mul,
simp,
simp at ineqe,
convert ineqe,
apply complex.abs.nonneg,
apply pow_nonneg (cray n),
end

lemma iter_deriv_comp_bound3 (K : set ℂ) (hK1 : K ⊆ ℍ') (hK2 : is_compact K) (k : ℕ) :
(∃ (u : ℕ → ℝ), ( summable u ∧
∀ (n : ℕ) (r : K),
( (2 * |π| * n)^k * complex.abs (complex.exp ( 2 *↑π * I * n * r))) ≤ u n )) :=
begin
  haveI : compact_space K, by {rw ←is_compact_univ_iff, rw is_compact_iff_is_compact_univ at hK2,
  apply hK2, },
  have hg := bounded_continuous_function.mk_of_compact (funn K hK1 hK2),
  set r : ℝ := ‖bounded_continuous_function.mk_of_compact (funn K hK1 hK2) ‖,
  have hr : ‖ bounded_continuous_function.mk_of_compact (funn K hK1 hK2)‖ < 1,
  by {rw bounded_continuous_function.norm_lt_iff_of_compact,
    intro x, rw bounded_continuous_function.mk_of_compact_apply, simp_rw funn,
    simp only [continuous_map.coe_mk, norm_eq_abs],
    apply exp_upper_half_plane_lt_one ⟨x.1 ,(hK1 x.2)⟩, linarith, },
have hr2 : 0 ≤ r, by {simp only [norm_nonneg], },
  have hu : summable (λ (n : ℕ),  complex.abs (( 2 *↑π * I * n)^(k) * r^n)),
 by {simp only [absolute_value.map_mul, complex.abs_pow, complex.abs_two, abs_of_real, abs_I,
  mul_one, abs_cast_nat, bounded_continuous_function.norm_mk_of_compact, abs_norm],
  simp_rw mul_pow,
  have h2ne : (2 : ℝ)^(k) ≠ 0, by {apply pow_ne_zero, exact ne_zero.ne 2,},
simp_rw mul_assoc,
rw (summable_mul_left_iff h2ne),
rw (summable_mul_left_iff _),
apply summable_pow_mul_geometric_of_norm_lt_1,
simp only [norm_norm, bounded_continuous_function.norm_mk_of_compact, norm_nonneg, ne.def] at *,
apply hr,
exact topological_semiring.mk,
apply pow_ne_zero,
simpa using real.pi_ne_zero,},
refine ⟨λ (n : ℕ),  complex.abs (( 2 *↑π * I * n)^(k) * r^n), hu,_⟩,
intros n t,
have ineqe : complex.abs (complex.exp (2 * π * I * n * t)) ≤ ‖ r ‖^n, by {
  have hw1 : complex.abs (complex.exp (2 * π * I * n * t)) =
    complex.abs (complex.exp (2 * π * I * t))^n,
  by { rw ←complex.abs_pow, congr, rw ←exp_nat_mul, ring_nf,},
  rw hw1,
  apply le_of_pow',
  apply complex.abs.nonneg,
  simp only [norm_nonneg],
  have := bounded_continuous_function.norm_coe_le_norm
    (bounded_continuous_function.mk_of_compact (funn K hK1 hK2)) t,
    simp only [norm_norm, bounded_continuous_function.norm_mk_of_compact, norm_nonneg,
    absolute_value.map_mul, complex.abs_pow,
    complex.abs_two, abs_of_real, abs_I, mul_one, abs_cast_nat,
    bounded_continuous_function.mk_of_compact_apply, norm_eq_abs, abs_norm] at *,
   exact this},
simp only [absolute_value.map_mul, complex.abs_pow, complex.abs_two, abs_of_real, abs_I, mul_one,
abs_cast_nat,bounded_continuous_function.norm_mk_of_compact, abs_norm],
apply mul_le_mul,
simp only,
simp only [norm_norm, bounded_continuous_function.norm_mk_of_compact] at ineqe,
convert ineqe,
apply complex.abs.nonneg,
apply pow_nonneg (cray n),
end


lemma exp_series_ite_deriv_uexp2 (k : ℕ) (x : ℍ')  :
  iterated_deriv_within k (λ z, ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)) ℍ' x =
   (∑' (n : ℕ), iterated_deriv_within k (λ (s : ℂ),  complex.exp ( 2 *↑π * I * n * s)) ℍ' x ) :=
begin
induction k with k IH generalizing x,
simp only [iterated_deriv_within_zero],
rw iterated_deriv_within_succ,
have HH: deriv_within (iterated_deriv_within k (λ z, ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)) ℍ' ) ℍ' x =
  deriv_within (λ z,
  (∑' (n : ℕ), iterated_deriv_within k (λ (s : ℂ), complex.exp ( 2 *↑π * I * n * s)) ℍ' z)) ℍ' x,
 by {
  apply deriv_within_congr,
  intros y hy,
  apply IH ⟨y,hy⟩,
  apply IH x,},
simp_rw HH,
rw deriv_tsum_fun',
simp only,
apply tsum_congr,
intro b,
rw iterated_deriv_within_succ,
apply (is_open.unique_diff_within_at upper_half_plane_is_open x.2 ),
exact upper_half_plane_is_open,
exact x.2,
intros y hy,
apply summable.congr (summable_iter_derv' k ⟨y,hy⟩ ),
intro b,
apply symm,
apply exp_iter_deriv_within k b hy,
intros K hK1 hK2,
simp only,
apply iter_deriv_comp_bound2 K hK1 hK2 k,
apply der_iter_eq_der_aux2,
apply (is_open.unique_diff_within_at upper_half_plane_is_open x.2 ),
end


lemma exp_series_ite_deriv_uexp'' (k : ℕ) (x : ℍ')  :
  iterated_deriv_within k (λ z, ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)) ℍ' x =
   (∑' (n : ℕ), (2 *↑π * I * n)^k * complex.exp ( 2 *↑π * I * n * x)) :=
begin
rw exp_series_ite_deriv_uexp2 k x,
apply tsum_congr,
intro b,
apply exp_iter_deriv_within k b x.2,
end

lemma exp_series_ite_deriv_uexp''' (k : ℕ)   :
  eq_on (iterated_deriv_within k (λ z, ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)) ℍ')
   (λ (x : ℂ), (∑' (n : ℕ), (2 *↑π * I * n)^k * complex.exp ( 2 *↑π * I * n * x))) ℍ' :=
begin
intros x hx,
apply exp_series_ite_deriv_uexp'' k ⟨x,hx⟩,
end

lemma uexp_cont_diff_on (k n : ℕ) :
cont_diff_on ℂ k (λ(z : ℂ), complex.exp ( 2 *↑π * I * n * z)) ℍ' :=
begin
apply cont_diff.cont_diff_on,
apply cont_diff.cexp,
apply cont_diff.mul,
apply cont_diff_const,
apply cont_diff_id,
end


lemma tsum_uexp_cont_diff_on (k : ℕ) :
cont_diff_on ℂ k (λ(z : ℂ), ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)) ℍ' :=
begin
apply  cont_diff_on_of_differentiable_on_deriv,
intros m hm,
apply differentiable_on.congr _ (exp_series_ite_deriv_uexp''' m),
intros x hx,
apply has_deriv_within_at.differentiable_within_at,
apply has_deriv_within_at_tsum_fun _ (upper_half_plane_is_open),
apply hx,
intros y hy,
apply summable_iter_derv' m ⟨y, hy⟩,
intros K hK1 hK2,
have := iter_deriv_comp_bound3 K hK1 hK2 (m+1),
obtain ⟨u, hu, hu2⟩ := this,
refine ⟨u, hu, _⟩,
intros n r,
have HU2 := hu2 n r,
simp,
apply le_trans _ HU2,
apply le_of_eq,
ring_exp,
intros n r,
apply differentiable.differentiable_at,
simp only [differentiable.mul, differentiable_const, differentiable.cexp, differentiable_id'],
exact at_top_ne_bot,
end


lemma iter_der_within_add (k : ℕ+) (x : ℍ') :
iterated_deriv_within k
  (λ z, ↑π * I - (2 *  ↑π * I) • ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)) ℍ' x =
  -(2 *  ↑π * I)*∑' (n : ℕ), (2 *  ↑π * I*n)^(k : ℕ) *complex.exp ( 2 *↑π * I * n * x) :=
begin
rw iter_der_within_const_neg k k.2 x,
simp,
have := iter_der_within_neg' k x (λ z, (2 *  ↑π * I) • ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)),
simp at this,
rw this,
rw neg_eq_neg_one_mul,
have t2:=  iter_der_within_const_mul' k x (2 *  ↑π * I)
  (λ z,  ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)),
simp at t2,
rw t2,
simp,
have h3:= exp_series_ite_deriv_uexp'' k x,
simp at h3,
left,
apply h3,
apply tsum_uexp_cont_diff_on k,
have := cont_diff_on.const_smul (2 *  ↑π * I) (tsum_uexp_cont_diff_on k),
simpa using this,
end
