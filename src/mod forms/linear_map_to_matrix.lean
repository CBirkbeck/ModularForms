import linear_algebra.basic
import .matrices

universes u v w

variables {K : Type u} [field K]
variables {V : Type v} [vector_space K V]
variables {W : Type v} [vector_space K W]
variables {bV : set V} [fintype bV] (hV : is_basis bV)
variables {bW : set W} [fintype bW] (hW : is_basis bW)
include hV hW

noncomputable def matrix_of_linear_map (f : V → W) [is_linear_map f] : matrix bV bW K :=
λ i, (hW.1.repr (f i)).to_fun ∘ subtype.val
