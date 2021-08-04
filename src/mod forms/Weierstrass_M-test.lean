import order.filter.archimedean
import data.complex.basic
import topology.instances.nnreal
import analysis.complex.basic
import order.filter.at_top_bot
universes u v w

noncomputable theory

open complex metric open_locale big_operators nnreal classical filter topological_space 

variables {α : Type u} {β : Type v}

lemma summable_if_complex_abs_summable {f : α → ℂ} :
  summable (λ x, complex.abs (f x)) →  summable f :=
begin
intro h,
apply summable_of_norm_bounded  (λ x, complex.abs (f x))  h,
intro i,
unfold norm, exact complete_of_proper,
end


lemma M_test_summable (F: ℕ → α → ℂ) (M: ℕ → ℝ) (h1: ∀ (n: ℕ), ∀ (a: α), (complex.abs (F n a)) ≤ (M n)) 
(h2: summable M): (∀ (a: α), summable (λ (n : ℕ), F n a)) :=
begin
intro a,
apply summable_if_complex_abs_summable,
have c1: ∀ (n: ℕ), 0 ≤ (complex.abs (F n a)), by {intro n, apply complex.abs_nonneg (F n a),},
have H1: ∀ (n: ℕ), (complex.abs (F n a)) ≤ (M n), by {simp [h1]},

apply summable_of_nonneg_of_le c1 H1,exact h2,

end  

lemma sum_sub_tsum_nat_add  {f : ℕ → ℂ} (k : ℕ) (h : summable f) :
 ∑' i, f i - (∑ i in finset.range k, f i) = (∑' i, f (i + k))  :=
begin
have:= sum_add_tsum_nat_add  k h, 
exact sub_eq_of_eq_add' (eq.symm this),
end



lemma M_test_uniform (F: ℕ → α → ℂ) (M: ℕ → ℝ) (h1: ∀ (n: ℕ), ∀ (a: α), (complex.abs (F n a)) ≤ (M n)) 
(h2: summable M):
tendsto_uniformly (λ (n: ℕ), (λ (a : α), ∑ i in (finset.range n), F i a)) ( (λ (a: α), ∑' (n: ℕ), F n a)) filter.at_top :=
begin


rw metric.tendsto_uniformly_iff,
intros ε hε,
have hS:= M_test_summable F M h1 h2,
simp at *,
have H:=summable_iff_vanishing_norm.1 h2 ε hε, simp at H,
have HU: ∃ (a: ℕ), ∀ (b: ℕ), a ≤ b → ∥ ∑' i, M (i+b) ∥ < ε, by {sorry,},

/-
simp_rw dist_eq_norm,
--let aa:= classical.some H,
have H2: ∀ (a: α) (k: ℕ), ∑' (n : ℕ), F n a - ∑ (i : ℕ) in finset.range k, F i a=∑' (n: ℕ), F (n+k) a, by {
intros a k, apply  sum_sub_tsum_nat_add k, exact hS a,

},
simp_rw H2,
have HC: ∀ (a: α), filter.tendsto (λn:ℕ, ∑ i in finset.range n, F i a) filter.at_top (𝓝 (∑'(n : ℕ), F n a) ), by {
intro a,
apply has_sum.tendsto_sum_nat,
exact (hS a).has_sum,
},
simp [tendsto_iff_dist_tendsto_zero] at HC, simp at HC, 
 simp_rw dist_eq_norm at HC, simp at HC, 
 simp_rw metric.tendsto_nhds at HC, simp only [filter.eventually_at_top, gt_iff_lt, ge_iff_le, dist_zero_right, norm_norm] at HC,
 have HC2:= HC _ ε hε,
-/
 have c1: ∀ (a: α) (n: ℕ), 0 ≤ (complex.abs (F n a)), by {intros a n, apply complex.abs_nonneg (F n a),},
have H1: ∀ (a: α) (n: ℕ), (complex.abs (F n a)) ≤ (M n), by {simp [h1]},


have B1: ∀ (a: α), (∑' (n: ℕ), complex.abs(F n a)) ≤ ∑' (n: ℕ), M n, by{
intro a, apply tsum_le_tsum, simp [h1], apply summable_of_nonneg_of_le (c1 a) (H1 a) h2, exact h2,


},
have BU: ∃ (a: ℕ), ∀ (b: ℕ), a ≤ b → ∀ (r: α), ∥ ∑' i, complex.abs (F (i+b) r) ∥ < ε, by {
let a':= classical.some HU,  
use a',
intros b hb,  intro r,
  sorry,},

--have:= summable.tendsto_at_top_zero (hS _), simp at *, rw tendsto_iff_dist_tendsto_zero at this,
 --simp_rw dist_eq_norm at this, simp at *,

end  