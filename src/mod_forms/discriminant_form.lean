import mod_forms.Eisen_is_holo
import data.complex.exponential

noncomputable theory

open modular_form Eisenstein_series

def Eisenstein_series (k : ℤ) := if h : 3 ≤ k then (Eisenstein_series_is_modular_form k h) else 0

local notation `G[` k `]` :=  (Eisenstein_series k)

def Eisenstein_4 := 60 • G[4]

def Eisenstein_6 := 140 • G[6]

local notation `E₄` := Eisenstein_4

local notation `E₆` := Eisenstein_6

def discriminant_form : modular_form ⊤ 12 := (E₄).mul ((E₄).mul E₄) - 27 • ((E₆).mul E₆)

open_locale direct_sum big_operators




example  : comm_ring (⨁ (n : ℤ),  modular_form ⊤ n) := by apply_instance


universes u v w
variables (ι : Type v) (A : ℤ → Type*)
[add_comm_monoid ι] [Π i, add_comm_group (A i)] [direct_sum.gcomm_ring A]
(f : A 2)



lemma test : direct_sum.of _ 4 (graded_monoid.ghas_mul.mul f f) = (direct_sum.of _ 2 f)^2:=
begin
rw pow_two,
simp_rw direct_sum.of_mul_of,
congr,
end


variable (v :(⨁ (n : ℕ),  modular_form ⊤ n))

def E4:= direct_sum.of _ 4 Eisenstein_4

def E6:= direct_sum.of _ 6 Eisenstein_6

lemma gmul_eq_mul {a b : ℤ} (f : modular_form ⊤ a) (g : modular_form ⊤ b) :
  graded_monoid.ghas_mul.mul f g = f.mul g :=
begin
refl,
end

def Delta := E4^3-27*E6^2

lemma eqvs_of_defs : direct_sum.of _ 12 discriminant_form = Delta :=
begin
  rw Delta,
  rw E4,
  rw E6,
  rw discriminant_form,
  simp only [map_sub, map_nsmul, nsmul_eq_mul, nat.cast_bit1, nat.cast_bit0, algebra_map.coe_one],
  congr,
  rw pow_three,
  simp_rw direct_sum.of_mul_of,
  simp_rw gmul_eq_mul,
  congr,
  rw pow_two,
  simp_rw direct_sum.of_mul_of,
  simp_rw gmul_eq_mul,
  congr,
end

def cot (z : ℂ) := (complex.cos z)/(complex.sin z)

lemma cot_series_rep (z : ℂ) : (real.pi : ℂ) * cot ((real.pi : ℂ) * z) =
1/z + ∑' (n : ℕ), (1/(z-(n+1))-1/(z+(n+1))) :=
begin
sorry,
end


def sigma_fn (k n : ℕ) : ℤ := ∑ (d : ℕ)  in nat.divisors n, d^(k-1)

lemma sigme_fn_one (k : ℕ) : sigma_fn k 1 = 1 :=
begin
rw sigma_fn,
rw nat.divisors_one,

simp_rw finset.sum_singleton,
simp,
end
