import analysis.complex.basic
import analysis.calculus.deriv
import tactic.pi_instances
import ring_theory.subring
import analysis.normed_space.basic



local attribute [instance] classical.prop_decidable
noncomputable theory

universes u v

open filter complex

section
variables {α : Type*} {β : Type*} {s : set α}

def extend_by_zero [has_zero β] (f : s → β) : α → β :=
λ z, if h : z ∈ s then f ⟨z, h⟩ else 0


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

@[simp]lemma open_subs_mem  (S : set ℂ ): S ∈ open_subs ↔ is_open S:=iff.rfl



/--A function is Holomorphic on an open subset of the complex numbers, if for every point in the domain
there is a neibourhood around the point containing the derivative of the function. In order to make it work 
with has_deriv_within_at, we first extend the function by zero to the entire complex plane. -/

 def is_holomorphic {domain : open_subs} (f : domain → ℂ) : Prop :=
∀ z : domain, ∃ f', has_deriv_within_at (extend_by_zero f) (f') domain z



variable {domain : open_subs}


lemma ext_by_zero_eq (domain: open_subs) (c : ℂ):∀ (y : ℂ), (y ∈ (domain : set ℂ)) → extend_by_zero (λ z : domain, (c : ℂ)) y =c :=
begin
intros y hy, rw extend_by_zero, simp only [dite_eq_ite], cases domain, dsimp at *, simp only [ite_eq_left_iff] at *, 
intros ᾰ, tactic.ext1 [] {new_goals := tactic.new_goals.all}, work_on_goal 0 { dsimp at *, solve_by_elim }, 
dsimp at *, solve_by_elim,
end  

lemma ext_by_zero_eq' (domain: open_subs) (f : domain → ℂ) (y : ℂ) (h: y ∈ (domain : set ℂ)): extend_by_zero (f ) y = (f ⟨ y, h⟩) :=
begin
 rw extend_by_zero, simp, cases domain, dsimp at *, exact dif_pos h,

end 

lemma const_hol  (c : ℂ) : is_holomorphic (λ z : domain, (c : ℂ)) :=
begin
rw is_holomorphic, intro z, use (0: ℂ), have h1:=has_deriv_within_at_const  z.1 domain c,

have H:= has_deriv_within_at.congr_of_eventually_eq_of_mem h1 _ z.property , convert H, rw  eventually_eq,
 rw eventually_iff_exists_mem, use domain, have H2:= ext_by_zero_eq domain c, split,
 have h3:= domain.2, simp only [open_subs_mem, subtype.val_eq_coe] at h3, have h4:=is_open.mem_nhds h3 z.2, 
 simp only [subtype.val_eq_coe], 
 convert h4, simp, rw nhds_within, simp only [inf_eq_left, le_principal_iff], exact h4, exact H2,

end



lemma zero_hol (domain: open_subs) : is_holomorphic (λ z : domain, (0 : ℂ)) :=
begin
  apply const_hol (0:ℂ ),
end 


lemma one_hol (domain: open_subs) : is_holomorphic (λ z : domain, (1 : ℂ)) := 
begin
apply const_hol (1: ℂ),

end
lemma add_hol (f g : domain → ℂ) (f_hol : is_holomorphic f) (g_hol : is_holomorphic g) : is_holomorphic (f + g) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ Hf,
  cases g_hol z₀ with g'z₀ Hg,
  existsi (f'z₀ + g'z₀),
  rw extend_by_zero_add,
  have:=has_deriv_within_at.add Hf Hg,
  exact this, 
end

lemma mul_hol (f g : domain → ℂ) (f_hol : is_holomorphic f) (g_hol : is_holomorphic g) : is_holomorphic (f * g) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ Hf,
  cases g_hol z₀ with g'z₀ Hg,
  existsi f'z₀*(extend_by_zero g z₀) + (extend_by_zero f z₀)*g'z₀,
  rw extend_by_zero_mul,
 have:=has_deriv_within_at.mul Hf Hg,
 exact this,
end




lemma neg_hol (f : domain → ℂ) (f_hol : is_holomorphic f) : is_holomorphic (-f) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ H,
  existsi -f'z₀,
  rw extend_by_zero_neg,
  have h3:=has_deriv_within_at.neg H,
  exact h3,
end

instance (domain: open_subs) : is_subring {f : domain → ℂ | is_holomorphic f} :=
{ zero_mem := zero_hol domain,
  add_mem  := add_hol,
  neg_mem  := neg_hol,
  mul_mem  := mul_hol,
  one_mem  := one_hol domain
}

--instance xyzzy {F : Type u} [normed_field F] : normed_space F F :=
--{ dist_eq := normed_field.dist_eq,
--norm_smul := normed_field.norm_mul }

lemma smul_hol (c : ℂ) (f : domain → ℂ) (f_hol : is_holomorphic f) : is_holomorphic (c • f) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ Hf,
  existsi c * f'z₀,
  rw extend_by_zero_smul,
  have h2:= has_deriv_within_at.const_smul c Hf,
  exact h2,
  
end

def hol_submodule (domain: open_subs) : submodule (ℂ)  (domain → ℂ) :=
{ carrier := {f : domain → ℂ | is_holomorphic f},
  zero_mem' := zero_hol domain,
  add_mem' := add_hol,
  smul_mem' := smul_hol}

