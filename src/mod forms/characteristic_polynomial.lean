import data.polynomial
import linear_algebra.determinant

universes u v w

namespace matrix
variables {m n : Type u} [fintype m] [fintype n] [decidable_eq n]
variables {R : Type v} [comm_ring R] [decidable_eq R]

open polynomial

def map {X Y : Type w} (f : X → Y) : matrix m n X → matrix m n Y :=
λ M i j, f (M i j)

def characteristic_polynomial (M : matrix n n R) : polynomial R :=
det (scalar X - map C M)

end matrix
