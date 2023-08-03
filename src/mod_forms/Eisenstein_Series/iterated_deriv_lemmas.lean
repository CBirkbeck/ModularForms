import analysis.calculus.iterated_deriv
import analysis.calculus.series
import data.complex.exponential
import analysis.complex.upper_half_plane.basic
import for_mathlib.mod_forms2
import mod_forms.holomorphic_functions



noncomputable theory

open upper_half_plane topological_space set  metric filter function complex
open_locale interval  nnreal ennreal topology big_operators nat classical

local notation `ℍ'`:=(⟨upper_half_plane.upper_half_space, upper_half_plane_is_open⟩: open_subs)


lemma iter_der_eq_on_cong (f g : ℂ → ℂ) (k : ℕ) (S : set ℂ) (hs : is_open S)
(hfg : eq_on f g S ) : eq_on (iterated_deriv_within k f S) (iterated_deriv_within k g S) S :=
begin
induction k with k IH generalising f g,
simp only [iterated_deriv_within_zero],
apply hfg,
intros x hx,
rw iterated_deriv_within_succ,
rw iterated_deriv_within_succ,
apply deriv_within_congr,
apply IH,
apply IH hx,
all_goals {apply is_open.unique_diff_within_at hs hx},
end


lemma iter_deriv_within_add (k : ℕ) (x : ℍ') (f g : ℂ → ℂ)
(hf : cont_diff_on ℂ k f ℍ')  (hg : cont_diff_on ℂ k g ℍ') :
 iterated_deriv_within k (f + g) ℍ' x =  iterated_deriv_within k f ℍ' x +
  iterated_deriv_within k g ℍ' x :=
begin
simp_rw iterated_deriv_within,
rw iterated_fderiv_within_add_apply,
simp,
apply hf,
apply hg,
apply is_open.unique_diff_on upper_half_plane_is_open,
apply x.2,

end


lemma iter_der_within_const_neg (k : ℕ) (hk : 0 < k) (x : ℍ') (c : ℂ) (f : ℂ → ℂ) :
 iterated_deriv_within k (λ z : ℂ, c - f z) ℍ' x =  iterated_deriv_within k (λ z, - f z) ℍ' x :=
begin
simp,
induction k with k IH,
exfalso,
simpa using hk,
rw iterated_deriv_within_succ',
rw iterated_deriv_within_succ',
apply iter_der_eq_on_cong,
apply upper_half_plane_is_open,
intros y hy,
rw deriv_within.neg,
apply deriv_within_const_sub,
repeat {apply is_open.unique_diff_within_at upper_half_plane_is_open hy},
apply x.2,
apply is_open.unique_diff_on upper_half_plane_is_open,
apply x.2,
apply is_open.unique_diff_on upper_half_plane_is_open,
apply x.2,
end

lemma iter_der_within_const_mul (k : ℕ)  (x : ℍ') (c : ℂ) (f : ℂ → ℂ)
  (hf : cont_diff_on ℂ k f ℍ') :
 iterated_deriv_within k (c • f) ℍ' x =  c • (iterated_deriv_within k f ℍ' x) :=
begin
simp_rw iterated_deriv_within,
rw iterated_fderiv_within_const_smul_apply,
simp only [continuous_multilinear_map.smul_apply] at *,
apply hf,
apply is_open.unique_diff_on upper_half_plane_is_open,
apply x.2,
end

lemma iter_der_within_const_mul' (k : ℕ)  (x : ℍ') (c : ℂ) (f : ℂ → ℂ)
  (hf : cont_diff_on ℂ k f ℍ') :
 iterated_deriv_within k (λ z, c * f z) ℍ' x =  c * (iterated_deriv_within k f ℍ' x) :=
begin
simpa using (iter_der_within_const_mul k x c f hf),

end


lemma iter_der_within_neg (k : ℕ)  (x : ℍ') (f : ℂ → ℂ)
  (hf : cont_diff_on ℂ k f ℍ') :
 iterated_deriv_within k (-f) ℍ' x =  - (iterated_deriv_within k f ℍ' x) :=
begin
rw neg_eq_neg_one_mul,
nth_rewrite 1 neg_eq_neg_one_mul,
rw ← smul_eq_mul,
rw ← smul_eq_mul,
apply iter_der_within_const_mul k x (-1),
apply hf,
end

lemma iter_der_within_neg' (k : ℕ)  (x : ℍ') (f : ℂ → ℂ)
  (hf : cont_diff_on ℂ k f ℍ') :
 iterated_deriv_within k (λ z, -f z) ℍ' x =  - (iterated_deriv_within k f ℍ' x) :=
begin
convert iter_der_within_neg k x f hf,
end

lemma iter_deriv_within_sub (k : ℕ) (x : ℍ') (f g : ℂ → ℂ)
(hf : cont_diff_on ℂ k f ℍ')  (hg : cont_diff_on ℂ k g ℍ') :
 iterated_deriv_within k (f - g) ℍ' x =  iterated_deriv_within k f ℍ' x -
  iterated_deriv_within k g ℍ' x :=
begin
have h1 : f - g = f + (-g), by {refl},
rw h1,
rw iter_deriv_within_add k x,
rw iter_der_within_neg  k x g hg,
refl,
apply hf,
apply cont_diff_on.neg hg,
end
