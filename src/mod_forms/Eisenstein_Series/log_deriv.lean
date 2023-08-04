import data.complex.exponential
import analysis.complex.locally_uniform_limit
import analysis.complex.upper_half_plane.basic


noncomputable theory

open  upper_half_plane topological_space set measure_theory
interval_integral metric filter function complex
open_locale interval real nnreal ennreal topology big_operators nat classical

local notation `ℍ` := upper_half_plane

def log_deriv (f : ℂ  → ℂ) := deriv f / f


lemma log_deriv_one : log_deriv 1 = 0 :=
begin
rw log_deriv,
simp,
ext1,
simp,
apply (deriv_const x (1 : ℂ)),
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

lemma differentiable_at.product {α : Type* } {ι : finset α} (F : α → ℂ → ℂ) (s : ℂ)
  (hd : ∀ (i : ι), differentiable_at ℂ (λ z, F i z ) s):
  differentiable_at ℂ (λ z, ∏ i in ι, F i z ) s :=
begin
induction ι using finset.cons_induction_on with a s ha ih,
simp only [finset.prod_empty, differentiable_at_const],
simp only [finset.cons_eq_insert],
rw ←finset.prod_fn,
rw finset.prod_insert,
apply differentiable_at.mul,
simp only [finset.forall_coe, subtype.coe_mk, finset.mem_cons, forall_eq_or_imp] at *,
apply hd.1,
rw ←finset.prod_fn at ih,
apply ih,
intros r,
simp at *,
apply hd.2,
exact r.2,
exact ha,
end


lemma log_deriv_prod {α : Type*} (s : finset  α) (f : α → ℂ → ℂ) (t : ℂ) (hf : ∀ x ∈ s, f x t ≠ 0)
   (hd : ∀ x ∈ s, differentiable_at ℂ (f x) t) :
  log_deriv (∏ i in s, f i) t = ∑ i in s, log_deriv (f i) t :=
begin
  induction s using finset.cons_induction_on with a s ha ih,
  { simp [log_deriv_one] },
  { rw [finset.forall_mem_cons] at hf,
    simp [ih hf.2], rw finset.prod_insert, rw finset.sum_insert,
    have := log_derv_mul (f a) (∏ i in s, f i) t _ _ _,
    convert this,
    apply symm,
    apply (ih hf.2),
    intros x hx,
    apply hd,
    simp only [hx, finset.cons_eq_insert, finset.mem_insert, or_true],
    apply mul_ne_zero hf.1,
    simp only [finset.prod_apply],
    rw finset.prod_ne_zero_iff,
    exact hf.2,
    apply hd,
    simp only [finset.cons_eq_insert, finset.mem_insert, eq_self_iff_true, true_or],
    rw finset.prod_fn,
    apply differentiable_at.product,
    intro r,
    apply hd,
    simp [r.2],
    repeat {exact ha},
   }
end

/-
lemma log_derv_diff (f : ℂ → ℂ) (s : set ℂ) (hs : is_open s) (hf : differentiable_on ℂ f s) (x : s)
 (hf2 : ∀ x ∈ s, f x ≠ 0) : differentiable_on ℂ (log_deriv f) s :=
begin
rw log_deriv,
apply differentiable_on.div,
all_goals{sorry},


end
-/

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


lemma log_deriv_pi_z (x : ℂ) : log_deriv (λ z : ℂ, π * z) x = 1/x :=
begin
rw log_deriv,
simp,
field_simp,
apply div_mul_right,
norm_cast,
apply real.pi_ne_zero,

end

lemma log_deriv_tendsto (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (s : set ℂ) (hs : is_open s) (x : s)
  (hF : tendsto_locally_uniformly_on f g at_top s)
  (hf : ∀ᶠ (n : ℕ) in at_top, differentiable_on ℂ (f n) s) (hg : g x ≠0 ):
tendsto (λ n : ℕ, (log_deriv (f n) x)) at_top (𝓝 ((log_deriv g) x)) :=
begin
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
apply hs,
apply hg,
end
