import linear_algebra.determinant

universe u

def GL (n : ℕ) (R : Type u) [ring R] := units (matrix (fin n) (fin n) R)

namespace GL

variables {n : ℕ} {R : Type u} [comm_ring R]

instance : group (GL n R) := by unfold GL; apply_instance

def det : GL n R → units R := units.map  matrix.det

instance : is_group_hom (det : GL n R → units R) := by unfold det; apply_instance

@[simp] lemma det_one : det (1 : GL n R) = 1 := is_group_hom.one det

@[simp] lemma det_mul (M : GL n R) (N : GL n R) : det (M * N) = det M * det N := is_group_hom.mul det M N

end GL

def SL (n : ℕ) (R : Type u) [comm_ring R] := is_group_hom.ker (GL.det : GL n R → units R)
