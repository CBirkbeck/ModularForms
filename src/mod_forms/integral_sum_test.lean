import analysis.sum_integral_comparisons

open topological_space set measure_theory
open_locale big_operators



lemma lb (N : ℕ) (f : ℝ → ℝ) (hf : monotone_on f (set.Ici (N : ℝ))) :
 ∑' x : (set.Ici N), f x ≤ f(N) + ∫ x in (set.Ici (N : ℝ)), f x ∂(volume.restrict (set.Ici (N : ℝ))) :=
begin
have n1 : N ≤ (N + 1), by {linarith},
have hfmon : monotone_on f (set.Icc N ((N+1) : ℕ)), by {sorry},
have := @monotone_on.sum_le_integral_Ico N (N+1)  f n1 hfmon,
simp only [coe_coe, measure.restrict_restrict, measurable_set_Ici, Ici_inter_Ici, sup_idem],

sorry,
end
