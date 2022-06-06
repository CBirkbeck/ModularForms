import analysis.complex.basic
import analysis.analytic.basic
import analysis.calculus.fderiv
import analysis.calculus.fderiv_analytic
import analysis.complex.cauchy_integral
import analysis.calculus.iterated_deriv
open nat
noncomputable theory
local attribute [instance] classical.prop_decidable

def add_zeros (f:ℂ → ℂ) (x:ℂ) (k: ℕ) : ℂ → ℂ :=
λz, f(z)*(z-x)^k

def meromorphic_at_integer (f : ℂ → ℂ ) (x : ℂ) (k:ℕ) : Prop :=
analytic_at ℂ (add_zeros f x k) x

def meromorphic_at (f : ℂ → ℂ ) (x : ℂ) : Prop :=
∃ (k : ℕ), meromorphic_at_integer f x k


def pole_order_at  (f:ℂ → ℂ) (x:ℂ): ℕ :=
if hk:  ∃ (k : ℕ), meromorphic_at_integer f x k ∧  ¬ meromorphic_at_integer f x (k-1)
then classical.some hk else 0

--how to extract the lemma from this definition
lemma pole_order_analytic_at (f:ℂ → ℂ ) (x:ℂ)(hf: meromorphic_at f x) :
meromorphic_at_integer f x (pole_order_at f x):=
begin
let k:= pole_order_at f x,
unfold pole_order_at,

sorry

end


lemma meromorphic_at.add (f:ℂ → ℂ) (g: ℂ → ℂ) (x: ℂ) (hf: meromorphic_at f x)
(hg: meromorphic_at g x) : meromorphic_at (f+g) x :=
begin
  cases hf with k hk,
  cases hg with l hl,
  let K:= max k l,
  have h1 : analytic_at ℂ (add_zeros f x K) x,
  sorry,
  have h2 : analytic_at ℂ (add_zeros g x K) x,
  sorry,
  rw meromorphic_at,
  use K,
  rw meromorphic_at_integer,
  convert analytic_at.add h1 h2,
  simp_rw add_zeros,
  simp,
  ring_nf,
end

-- probably already defined somewhere?
def recip (f:ℂ → ℂ) :=
λz, 1/f(z)

lemma recip_meromorphic (f: ℂ → ℂ) (x:ℂ) (hf: analytic_at ℂ f x) :
meromorphic_at (recip f) x :=
begin
  sorry
end

def residue_at_simple_pole (f:ℂ → ℂ) (x: ℂ) (hs: meromorphic_at_integer f x 1) :=
(add_zeros f x 1)(x)



--add junk value 0 here for non-meromorphic (also analytic) functions
def residue_at (f:ℂ → ℂ) (x: ℂ) (hf: meromorphic_at f x): ℂ :=
begin
rw meromorphic_at at hf,
simp_rw meromorphic_at_integer at hf,
let k:= pole_order_at f x,
have h1: differentiable_at ℂ (add_zeros f x k) x,
apply analytic_at.differentiable_at,
exact pole_order_analytic_at f x hf,
let g:= iterated_deriv (k-1) (add_zeros f x k) x,
let z:= g/(factorial (k-1)),
end


def isolated_zeros (f: ℂ → ℂ) (x:ℂ):=
∃ ε > 0, ∀ z ≠ x,  ∥z-x∥ < ε → f z ≠ 0

def pole_at (f:ℂ → ℂ) (x:ℂ) :=
meromorphic_at f x ∧ ¬ analytic_at ℂ f x

def isolated_poles (f: ℂ → ℂ) (x:ℂ) :=
∃ ε > 0, ∀ z ≠ x, ∥z-x∥ < ε → analytic_at ℂ f z


-- probably don't need isolated zeros here
def meromorphic_function (f:ℂ → ℂ) :=
∀x:ℂ, (meromorphic_at f x) ∧ (f x = 0 → isolated_zeros f x ) ∧ (pole_at f x → isolated_poles f x)

def deriv_over (f:ℂ → ℂ) :=
λx, (deriv f x)/(f x)

lemma deriv_over_meromorphic (f:ℂ → ℂ) (x:ℂ) :
meromorphic_at f x → meromorphic_at (deriv_over f) x :=
begin
sorry
end

def order_of_vanishing_at (f:ℂ → ℂ) (x:ℂ) (hf: meromorphic_at f x): ℕ :=
begin
let k₁ := pole_order_at f x,
let k₂ := pole_order_at (recip f) x,
use k₂ - k₁
end

lemma vanishing_res (f:ℂ → ℂ) (x:ℂ) (hf: meromorphic_at f x) :
residue_at (deriv_over f) x (deriv_over_meromorphic f x (hf)) = order_of_vanishing_at f x hf :=
begin
  sorry
end
