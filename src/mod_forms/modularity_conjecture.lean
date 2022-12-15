import for_mathlib.mod_forms2
import number_theory.modular_forms.congruence_subgroups
import algebraic_geometry.elliptic_curve.weierstrass
import for_mathlib.unform_limits_of_holomorphic

open modular_form complex
open_locale interval real modular_form

local notation `ℍ`:=upper_half_plane

noncomputable theory

def map_to_upper (x : ℝ) : ℍ := ⟨(x + I),
  by {simp only [complex.add_im, complex.of_real_im, complex.I_im, zero_add, zero_lt_one],} ⟩

def modular_form_an (n : ℕ) {N : ℕ} {k : ℤ} (f : cusp_form (Gamma0 N) k)
: ℂ := ∫ (x : ℝ) in 0..1, ( exp (-2 * π * I * n *(x + I))) * f.1 (map_to_upper x)

local notation `a_[`:73 n:0`]` f  :72 := modular_form_an n f

def rat_red (q : ℚ) ( p : ℕ) : (zmod p) := (q.num : zmod p) * (q.denom : zmod p)⁻¹

def set_of_points_mod_n (E : elliptic_curve ℚ) (n : ℕ) := {P : (zmod n) × (zmod n) |
  let ⟨x, y⟩ := P in  y^2 + (rat_red E.a₁ n)* x * y+ (rat_red E.a₃ n) * y   =
  x^3 +(rat_red E.a₂ n)* x^2 + (rat_red E.a₄ n) * x + (rat_red E.a₆ n)}

def EllipticCurve.ap (E : elliptic_curve ℚ) (p : ℕ) : ℕ :=
  p-(cardinal.mk (set_of_points_mod_n E p)).to_nat

def is_normalised_eigenform {N : ℕ} {k : ℤ}
(f : cusp_form (Gamma0 N) k) : Prop :=
(a_[1] f) = 1 ∧
∀ (m n : ℕ) (hmn : m.coprime n), ((a_[n * m] f) = (a_[n] f) * (a_[m] f)) ∧
∀ (p r : ℕ) (hp : p.prime ) (hr : 2 ≤ r),
(a_[p^r] f) = (a_[p] f) * (a_[p^(r-1)] f) - (p^(k-1)) * (a_[p^(r-2)] f)


theorem modularity_conjecture (E : elliptic_curve ℚ) : ∃ (N : ℕ)
  (f : cusp_form (Gamma0 N) 2)
  (hf : is_normalised_eigenform f),
  ∀ (p : ℕ) (hp : p.prime ) (hN : (N : zmod p ) ≠ 0 ), a_[p] f = E.ap p :=
begin
sorry,
end
