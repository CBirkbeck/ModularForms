import analysis.complex.basic
import analysis.analytic.basic
import analysis.calculus.fderiv
import analysis.calculus.fderiv_analytic
import analysis.complex.cauchy_integral
import data.nat.enat
noncomputable theory

def add_zeros (f:ℂ → ℂ) (x:ℂ) (k: ℕ) : ℂ → ℂ :=
λz, f(z)*(z-x)^k

def meromorphic_at_integer (f : ℂ → ℂ ) (x : ℂ) (k:ℕ) : Prop :=
analytic_at ℂ (add_zeros f x k) x

def meromorphic_at [decidable_prop] (f : ℂ → ℂ ) (x : ℂ) : Prop :=
∃ (k : ℕ), meromorphic_at_integer f x k



def pole_order_at  (f:ℂ → ℂ) (x:ℂ) (hf: meromorphic_at f x): ℕ :=
if hk:  ∃ (k : ℕ), k ≤ classical.some hf ∧   meromorphic_at_integer f x k ∧  ¬ meromorphic_at_integer f x (k-1)
then classical.some hk else 0


def meromorphic_around (f : ℂ → ℂ ) (x : ℂ) :=
∃ ε > 0,  ∀ z, ∥z-x∥<ε → meromorphic_at f z


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
  have h3 : analytic_at ℂ (add_zeros (f+g) x K) x,
  sorry,
  exact analytic_at.add ℂ h1 h2,
  use K,
end

def recip (f:ℂ → ℂ) :=
λz, 1/f(z)

lemma recip_meromorphic (f: ℂ → ℂ) (x:ℂ) (hf: analytic_at ℂ f x) :
meromorphic_at (recip f) x :=
begin
  sorry
end



def residue_at_simple_pole (f:ℂ → ℂ) (x: ℂ) (hf: meromorphic_at f x)
(hs: analytic_at ℂ (add_zeros f x 1) x ) :=
(add_zeros f x 1)(x)

def residue_at (f:ℂ → ℂ) (x: ℂ) (hf: meromorphic_at f x): ℂ :=
sorry

def isolated_zeros (f: ℂ → ℂ) (x:ℂ):=
∃ ε > 0, ∀ z ≠ x,  ∥z-x∥ < ε → f z ≠ 0

def pole_at (f:ℂ → ℂ) (x:ℂ) :=
  meromorphic_at f x ∧ ¬ analytic_at ℂ f x

def isolated_poles (f: ℂ → ℂ) (x:ℂ) :=
∃ ε > 0, ∀ z ≠ x, ∥z-x∥ < ε → analytic_at ℂ f z

def meromorphic_function (f:ℂ → ℂ) :=
∀x:ℂ, (meromorphic_at f x) ∧ (f x = 0 → isolated_zeros f x ) ∧ (pole_at f x → isolated_poles f x)


def order_of_vanishing_at (f:ℂ → ℂ) (x:ℂ) (hf: meromorphic_at f x): ℕ :=
sorry
