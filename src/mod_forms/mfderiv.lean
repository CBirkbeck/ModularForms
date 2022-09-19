
import geometry.manifold.mfderiv

noncomputable theory
open_locale classical topological_space manifold

open set

universe u



variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
{M' : Type*} [topological_space M'] [charted_space H' M']


section arithmetic
/-! #### Arithmetic -/

variables {S: topological_space.opens 𝕜}

lemma mdifferentiable_add {f g : S → 𝕜}
(hf : mdifferentiable 𝓘(𝕜) 𝓘(𝕜) f) (hg : mdifferentiable 𝓘(𝕜) 𝓘(𝕜) g) :
mdifferentiable 𝓘(𝕜) 𝓘(𝕜) (f + g) :=
begin
  simp_rw mdifferentiable at *,
  simp only [mdifferentiable_at, differentiable_within_at_univ] at *,
  intro x,
  split,
  { apply continuous_at.add (hf x).1 (hg x).1 },
  { convert (differentiable_within_at.add (hf x).2 (hg x).2) },
end

lemma mdifferentiable_mul {f g : S → 𝕜}
(hf : mdifferentiable 𝓘(𝕜) 𝓘(𝕜) f) (hg : mdifferentiable 𝓘(𝕜) 𝓘(𝕜) g) :
mdifferentiable 𝓘(𝕜) 𝓘(𝕜) (f * g) :=
begin
  simp_rw mdifferentiable at *,
  simp only [mdifferentiable_at, differentiable_within_at_univ] at *,
  intro x,
  split,
  apply continuous_at.mul (hf x).1 (hg x).1,
  convert (differentiable_within_at.mul (hf x).2 (hg x).2),
end

lemma mdifferentiable_smul {f : S → 𝕜} (s : 𝕜) (hf : mdifferentiable 𝓘(𝕜) 𝓘(𝕜) f) :
  mdifferentiable 𝓘(𝕜) 𝓘(𝕜) (s • f) :=
begin
  simp_rw mdifferentiable at *,
  simp only [mdifferentiable_at, differentiable_within_at_univ] at *,
  intro x,
  split,
  { apply continuous_at.const_smul (hf x).1,
  exact has_continuous_smul.has_continuous_const_smul },
  apply differentiable_within_at.congr (differentiable_within_at.const_smul (hf x).2 s),
  { intro x, simp },
  { refl },
end

lemma mdifferentiable_zero :
mdifferentiable 𝓘(𝕜) 𝓘(𝕜) (0 : S → 𝕜) :=
begin
  intro x,
  rw mdifferentiable_at,
  simp [mdifferentiable_at, differentiable_within_at_univ] at *,
  split,
  { apply continuous_zero.continuous_at },
  { apply differentiable_at_const (0 : 𝕜) },
end

lemma mdifferentiable_one :
mdifferentiable 𝓘(𝕜) 𝓘(𝕜) (1 : S → 𝕜) :=
begin
  intro x,
  rw mdifferentiable_at,
  simp [mdifferentiable_at, differentiable_within_at_univ] at *,
  split,
  { apply continuous_const.continuous_at },
  { apply differentiable_at_const (1 : 𝕜) },
end

end arithmetic
