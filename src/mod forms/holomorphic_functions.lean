import analysis.complex.basic
import analysis.calculus.deriv
import tactic.pi_instances
import ring_theory.subring
import analysis.normed_space.basic

local attribute [instance] classical.prop_decidable
noncomputable theory

universes u v

open filter complex
/-
def has_complex_derivative_at
(f : ℂ → ℂ)
(f'z : ℂ)
(z : ℂ) : Prop :=
let error_term (h : ℂ) : ℝ :=
    abs((f (z + h) - (f z + f'z * h))/h) in
(tendsto error_term (nhds 0) (nhds 0))

lemma has_complex_derivative_at_iff (f f'z z) :
  has_complex_derivative_at f f'z z
  ↔ (∀ ε > 0, ∃ δ > 0, ∀ h:ℂ, h ≠ 0 → abs h < δ → abs ((f(z+h)-f(z)-f'z*h)/h) < ε) :=

begin
split,
intros H1 ε hε, 
sorry,
sorry,
end   


⟨λ H ε hε, let ⟨δ, hδ1, hδ2⟩ := tendsto_nhds_of_metric.1 H ε hε in
  ⟨δ, hδ1, λ h h1 h2, by simp only [dist, sub_zero, complex.abs_abs, sub_add_eq_sub_sub] at hδ2;
    from hδ2 h2⟩,
λ H, tendsto_nhds_of_metric.2 $ λ ε hε, let ⟨δ, hδ1, hδ2⟩ := H ε hε in
  ⟨δ, hδ1, λ h h1, if H : h = 0 then by unfold dist;
    rwa [H, add_zero, mul_zero, add_zero, sub_self, zero_div, sub_zero, complex.abs_zero, _root_.abs_zero]
  else by unfold dist at h1 ⊢; rw [sub_zero] at h1;
    rw [sub_zero, complex.abs_abs, sub_add_eq_sub_sub]; from hδ2 h H h1⟩⟩

lemma has_complex_derivative_at_iff' (f f'z z) :
  has_complex_derivative_at f f'z z
  ↔ (∀ ε > 0, ∃ δ > 0, ∀ h:ℂ, abs h < δ → abs ((f(z+h)-f(z)-f'z*h)/h) < ε) :=
by simp only [has_complex_derivative_at, tendsto_nhds_of_metric, dist,
sub_zero, complex.abs_abs, sub_add_eq_sub_sub]

lemma has_complex_derivative_at_iff'' (f f'z z) :
  has_complex_derivative_at f f'z z
  ↔ tendsto (λ h, (f(z+h)-f(z)-f'z*h)/h) (nhds 0) (nhds 0) :=
by simp only [has_complex_derivative_at, tendsto_nhds_of_metric, dist,
sub_zero, complex.abs_abs, sub_add_eq_sub_sub]-/

section
variables {α : Type*} {β : Type*} {s : set α}

def extend_by_zero [has_zero β] (f : s → β) : α → β :=
λ z, if h : z ∈ s then f ⟨z, h⟩ else 0


def extend_by_const (c: β) [has_zero β] (f : s → β) : α → β :=
λ z, if h : z ∈ s then f ⟨z, h⟩ else c

lemma extend_by_zero_zero [has_zero β] :
extend_by_zero (λ s, 0 : s → β) = (λ h, 0) :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

lemma extend_by_zero_zero' [has_zero β] :
extend_by_zero (0 : s → β) = 0 :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

lemma extend_by_zero_add [add_group β] (f g : s → β) :
extend_by_zero (f + g) = extend_by_zero f + extend_by_zero g :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

lemma extend_by_zero_mul [semiring β] (f g : s → β) :
extend_by_zero (f * g) = extend_by_zero f * extend_by_zero g :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

lemma extend_by_zero_neg [add_group β] (f : s → β) :
extend_by_zero (-f) = -extend_by_zero f :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

lemma extend_by_zero_sub [add_group β] (f g : s → β) :
extend_by_zero (f - g) = extend_by_zero f - extend_by_zero g :=
--(extend_by_zero_add f _).trans $ congr_arg _ $ extend_by_zero_neg  g
begin
have h1:= extend_by_zero_add f (-g),
have h2:= extend_by_zero_neg g,
rw h2 at h1, convert h1, ring_nf, ext z, simp only [pi.add_apply, pi.neg_apply, pi.sub_apply], ring_nf,
end

lemma extend_by_zero_smul [ring β] (c : β) (f : s → β) :
extend_by_zero (c • f) = c • extend_by_zero f :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

end

def open_subs:={domain: set ℂ | is_open domain}

/-- holomorphic function from a subset of ℂ. Correct definition if domain is open. -/
def is_holomorphic {domain : open_subs} (f : domain → ℂ) : Prop :=
∀ z : domain, ∃ f', has_deriv_at (extend_by_zero f) (f') z

def is_holomorphic' {domain : open_subs} (f : domain → ℂ)  :=  
 deriv_within (extend_by_zero f) domain.val 

 def is_holomorphic'' {domain : open_subs} (f : domain → ℂ) : Prop :=
∀ z : domain, ∃ f', has_deriv_within_at (extend_by_zero f) (f') domain z

--fderiv_within 𝕜 f s x 1
#check is_holomorphic

variable {domain : open_subs}


lemma const_hol  (c : ℂ) : is_holomorphic'' (λ z : domain, (c : ℂ)) :=
begin
rw is_holomorphic'', simp_rw [has_deriv_within_at, has_deriv_at_filter],
 simp [has_fderiv_at_filter_iff_tendsto],
intro z, use (0: ℂ ), simp, rw extend_by_zero, simp,   sorry,


end

/- have:= has_deriv_within_at_const  z.1 domain.1 c, use (0: ℂ), 
 
simp at this,
rw has_deriv_within_at,
rw has_deriv_at_filter,
rw has_fderiv_at_filter, 
rw has_deriv_within_at at this,
rw has_deriv_at_filter at this,
rw has_fderiv_at_filter at this, convert this, simp, 
end  

/-
λ z₀, ⟨(0 : ℂ), let ⟨δ, hδ1, hδ2⟩ := is_open_metric.1 domain_open z₀.1 z₀.2 in
tendsto_nhds_of_metric.2 $ λ ε hε, ⟨δ, hδ1, λ z hz,
have H1 : ↑z₀ + z ∈ domain, from show z₀.1 + z ∈ domain,
  from hδ2 $ by simpa [dist] using hz,
have H2 : ↑z₀ ∈ domain, from z₀.2,
by simpa [extend_by_zero, H1, H2, -add_comm] using hε⟩⟩-/-/

lemma zero_hol (domain: open_subs) : is_holomorphic'' (λ z : domain, (0 : ℂ)) :=
begin
  sorry,
end 
--λ z₀, ⟨0, show tendsto _ _ _, by simp [extend_by_zero_zero, tendsto_const_nhds]⟩

lemma one_hol  : is_holomorphic'' (λ z : domain, (1 : ℂ)) := 
begin
 sorry, 
--const_hol domain.property 1,
end
lemma add_hol (f g : domain → ℂ) (f_hol : is_holomorphic'' f) (g_hol : is_holomorphic'' g) : is_holomorphic'' (f + g) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ Hf,
  cases g_hol z₀ with g'z₀ Hg,
  existsi (f'z₀ + g'z₀),
  rw extend_by_zero_add,
  have:=has_deriv_within_at.add Hf Hg,
  exact this,
end

lemma mul_hol (f g : domain → ℂ) (f_hol : is_holomorphic'' f) (g_hol : is_holomorphic'' g) : is_holomorphic'' (f * g) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ Hf,
  cases g_hol z₀ with g'z₀ Hg,
  existsi f'z₀*(extend_by_zero g z₀) + (extend_by_zero f z₀)*g'z₀,
  rw extend_by_zero_mul,
 have:=has_deriv_within_at.mul Hf Hg,
 exact this,
end




lemma neg_hol (f : domain → ℂ) (f_hol : is_holomorphic'' f) : is_holomorphic'' (-f) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ H,
  existsi -f'z₀,
  rw extend_by_zero_neg,
  have h3:=has_deriv_within_at.neg H,
  exact h3,
end

instance (domain: open_subs) : is_subring {f : domain → ℂ | is_holomorphic'' f} :=
{ zero_mem := zero_hol,
  add_mem  := add_hol,
  neg_mem  := neg_hol,
  mul_mem  := mul_hol,
  one_mem  := one_hol domain.property
}

instance xyzzy {F : Type u} [normed_field F] : normed_space F F :=
{ dist_eq := normed_field.dist_eq,
  norm_smul := normed_field.norm_mul }

lemma smul_hol (c : ℂ) (f : domain → ℂ) (f_hol : is_holomorphic f) : is_holomorphic (c • f) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ Hf,
  existsi c * f'z₀,
  rw extend_by_zero_smul,
  rw has_complex_derivative_at_iff'' at *,
  conv { congr,
    { funext, simp only [pi.smul_apply, smul_eq_mul],
      rw [← mul_sub, mul_assoc, ← mul_sub, mul_div_assoc] },
    skip, rw ← mul_zero c },
  exact tendsto_mul tendsto_const_nhds Hf
end

instance hol_submodule : module (ℂ) {f : domain → ℂ | is_holomorphic f} :=
{ zero_ := zero_hol,
  add_  := add_hol,
  smul  := smul_hol }
