/-
    A faster, computable version of matrices implemented entirely in terms of d_array, 
    trying to rely on fast pre-existing array and d_array functions as much as possible.

    A slightly more "serious" version of fast_matrix (?)

    Still a WIP.

    The second half of the document is a bit of a mess.
-/

import data.vector
import data.list.basic
import .matrices

universes u v

def computable_d_matrix (m n : ℕ) (α : fin m → fin n → Type u) := d_array m (λ j, d_array n (α j))

namespace computable_d_matrix
    variables {m n : ℕ} {α : fin m → fin n → Type u} {β : Type v}
    def nil {α} : computable_d_matrix 0 0 α := 
    ⟨λ i, absurd (fin.is_lt i) (nat.not_lt_zero (fin.val i))⟩

    def read (a : computable_d_matrix m n α) (i : fin m) (j : fin n) : α i j :=
    d_array.read (d_array.read a i) j

    def read_row (a : computable_d_matrix m n α) (i : fin m) : d_array n (α i) :=
    d_array.read a i
    
    def read_col (a : computable_d_matrix m n α) (j : fin n) : d_array m (λ i, α i j) :=
    ⟨λ i, d_array.read (d_array.read a i) j⟩

    def transpose (a : computable_d_matrix m n α) : computable_d_matrix n m (λ (j : fin n) (i : fin m), α i j) :=
    ⟨λ j, ⟨λ i, a.read i j⟩⟩ -- TODO: This can probably be optimised

    def write (a : computable_d_matrix m n α) (i : fin m) (j : fin n) (v : α i j) : computable_d_matrix m n α :=
    d_array.write a i (d_array.write (d_array.read a i) j v)

    def write_row (a : computable_d_matrix m n α) (i : fin m) (v : d_array n (α i)) : computable_d_matrix m n α :=
    d_array.write a i v
    
    def write_col (a : computable_d_matrix m n α) (j : fin n) (v : d_array m (λ i, α i j)) : computable_d_matrix m n α :=
    transpose (d_array.write (transpose a) j v) -- TODO: This can probably be optimised, by not relying on transpose

    def iterate (a : computable_d_matrix m n α) (b : β) (f : Π (i : fin m) (j : fin n), α i j → β → β) : β :=
    d_array.iterate a b (λ i arr state, d_array.iterate arr state (λ j, f i j))            

    def iterate_row (a : computable_d_matrix m n α) (b : β) (f : Π (i : fin m), (d_array n (α i)) → β → β) : β :=
    d_array.iterate a b f

    def iterate_col (a : computable_d_matrix m n α) (b : β) (f : Π (j : fin n), d_array m (λ i, α i j) → β → β) : β :=
    d_array.iterate (transpose a) b f -- TODO: this can probably be optimised, by not relying on transpose

    def foreach (a : computable_d_matrix m n α) (f : Π (i : fin m) (j : fin n), α i j → α i j) : computable_d_matrix m n α :=
    iterate a a $ λ i j v a', a'.write i j (f i j v)

    def map (f : Π (i : fin m) (j : fin n), α i j → α i j) (a : computable_d_matrix m n α) : computable_d_matrix m n α :=
    foreach a f

    def map₂ (f : Π (i : fin m) (j : fin n), α i j → α i j → α i j) (a b : computable_d_matrix m n α) : computable_d_matrix m n α :=
    foreach b (λ i j, f i j (a.read i j))

    def foldl (a : computable_d_matrix m n α) (b : β) (f : Π (i : fin m) (j : fin n), α i j → β → β) : β :=
    iterate a b f

    @[simp] lemma read_write (a : computable_d_matrix m n α) (i : fin m) (j : fin n) (v : α i j) : read (write a i j v) i j = v :=
    by simp [read, write]

    @[simp] lemma read_write_row (a : computable_d_matrix m n α) (i : fin m) (v : d_array n (α i)) : read_row (write_row a i v) i = v :=
    by simp [read_row, write_row]

    -- TODO: This one
    -- @[simp] lemma read_write_col (a : computable_d_matrix m n α) (j : fin n) (v : d_array m (λ i, α i j)) : read_col (write_col a j v) j = v :=
    -- by simp [read_col, write_col, transpose, d_array.write, d_array.read, read, write, read_row, write_row]

    @[simp] lemma read_write_of_ne (a : computable_d_matrix m n α) {i j : fin m} {k l : fin n} (v : α i k) : i ≠ j → k ≠ l → (read (write a i k v) j l) = (read a j l):=
    by intros h₁ h₂; simp [read, write, h₁, h₂]

    protected lemma ext {a b : computable_d_matrix m n α} (h : ∀ i j, read a i j = read b i j) : a = b :=
    by cases a; cases b; congr; funext i; exact d_array.ext (h i)

    protected lemma ext' {a b : computable_d_matrix m n α} (h : ∀ (i j : nat) (h₁ : i < m) (h₂ : j < n), read a ⟨i, h₁⟩ ⟨j, h₂⟩ = read b ⟨i, h₁⟩ ⟨j, h₂⟩) : a = b :=
    begin   -- TODO: Clean this up
    cases a,
    cases b,
    congr,
    funext i,
    apply d_array.ext,
    intros j,
    have hi : i = ⟨i.val, (fin.is_lt i)⟩, by simp,
    have hj : j = ⟨j.val, (fin.is_lt j)⟩, by simp,
    rw hi,
    rw hj,
    from (h (fin.val i) (fin.val j) (fin.is_lt i) (fin.is_lt j)),
    end

    protected def beq_aux [∀ i j, decidable_eq (α i j)] (a b : computable_d_matrix m n α) : Π (i : nat), i ≤ m → bool :=
    @d_array.beq_aux _ _ _ a b

    protected def beq [∀ i j, decidable_eq (α i j)] (a b : computable_d_matrix m n α) : bool :=
    @d_array.beq_aux _ _ _ a b _ (le_refl m)

    instance [∀ i j, decidable_eq (α i j)] : decidable_eq (computable_d_matrix m n α) :=
    d_array.decidable_eq

end computable_d_matrix

def computable_matrix (m n : ℕ) (α : Type u) := computable_d_matrix m n (λ i j, α)

namespace computable_matrix
    variables {m n : nat} {α : Type u} {β : Type v}
    def nil : computable_matrix 0 0 α :=
    computable_d_matrix.nil

    def read (a : computable_matrix m n α) (i : fin m) (j : fin n) : α :=
    computable_d_matrix.read a i j

    def read_row (a : computable_matrix m n α) (i : fin m) : array n α :=
    computable_d_matrix.read_row a i

    def read_col (a : computable_matrix m n α) (j : fin n) : array m α :=
    computable_d_matrix.read_col a j

    def transpose (a : computable_matrix m n α) : computable_matrix n m α :=
    computable_d_matrix.transpose a

    def write (a : computable_matrix m n α) (i : fin m) (j : fin n) (v : α) : computable_matrix m n α :=
    computable_d_matrix.write a i j v

    def write_row (a : computable_matrix m n α) (i : fin m) (v : array n α) : computable_matrix m n α :=
    computable_d_matrix.write_row a i v

    def write_col (a : computable_matrix m n α) (j : fin n) (v : array m α) : computable_matrix m n α :=
    computable_d_matrix.write_col a j v

    def iterate_row (a : computable_matrix m n α) (b : β) (f : fin m → array n α → β → β) : β :=
    computable_d_matrix.iterate_row a b (λ i V₁, f i ⟨V₁.data⟩)

    def iterate_col (a : computable_matrix m n α) (b : β) (f : fin n → array m α → β → β) : β :=
    computable_d_matrix.iterate_col a b (λ i V₁, f i ⟨V₁.data⟩)

    def iterate (a : computable_matrix m n α) (b : β) (f : fin m → fin n → α → β → β) : β :=
    computable_d_matrix.iterate a b (λ i j v, f i j v)

    def foreach (a : computable_matrix m n α) (f : fin m → fin n → α → α) : computable_matrix m n α :=
    iterate a a (λ i j v a', a'.write i j (f i j v))

    def map (f : α → α) (a : computable_matrix m n α) : computable_matrix m n α :=
    foreach a (λ _ _, f)

    def map₂ (f : α → α → α) (a b : computable_matrix m n α) : computable_matrix m n α :=
    foreach b (λ i j, f (a.read i j))

    def foldl_row (a : computable_matrix m n α) (b : β) (f : (array n α) → β → β) : β :=
    iterate_row a b (λ _, f)

    def foldl_col (a : computable_matrix m n α) (b : β) (f : (array m α) → β → β) : β :=
    iterate_col a b (λ _, f)

    def rev_list_row (a : computable_matrix m n α) : list (array n α) :=
    a.foldl_row [] (::)

    def rev_list_col (a : computable_matrix m n α) : list (array m α) :=
    a.foldl_col [] (::)

    @[simp] lemma read_write (a : computable_matrix m n α) (i : fin m) (j : fin n) (v : α) : read (write a i j v) i j = v :=
    by simp [read, write]

    @[simp] lemma read_write_of_ne (a : computable_matrix m n α) {i j : fin m} {k l : fin n} (v : α) : i ≠ j → k ≠ l → (read (write a i k v) j l) = (read a j l):=
    by intros h₁ h₂; simp [read, write, h₁, h₂]

    protected lemma ext {a b : computable_matrix m n α} (h : ∀ i j, read a i j = read b i j) : a = b :=
    by cases a; cases b; congr; funext i; exact array.ext (h i)

    protected lemma ext' {a b : computable_matrix m n α} (h : ∀ (i j : nat) (h₁ : i < m) (h₂ : j < n), read a ⟨i, h₁⟩ ⟨j, h₂⟩ = read b ⟨i, h₁⟩ ⟨j, h₂⟩) : a = b :=
    begin   -- TODO: Golf this one
    cases a,
    cases b,
    congr,
    funext i,
    apply array.ext,
    intros j,
    have hi : i = ⟨i.val, (fin.is_lt i)⟩, by simp,
    have hj : j = ⟨j.val, (fin.is_lt j)⟩, by simp,
    rw hi,
    rw hj,
    from (h (fin.val i) (fin.val j) (fin.is_lt i) (fin.is_lt j)),
    end

    protected def beq [decidable_eq α] (a b : computable_matrix m n α) : bool :=
    @computable_d_matrix.beq m n (λ i j, α) _ a b

    instance [decidable_eq α] : decidable_eq (computable_matrix m n α) :=
    computable_d_matrix.decidable_eq

    def to_list (a : computable_matrix m n α) : list (list (α)) :=
    iterate_row a [] (λ i v b, list.concat b (array.to_list v))

    instance repr [has_repr α] : has_repr (computable_matrix m n α) :=
    ⟨λ a, list.repr (to_list a)⟩

    -- Matrix row operations. Not sure if it's actually worth having these implemented like this here.

    def exchange_rows (a : computable_matrix m n α) (i₁ i₂ : fin m) : computable_matrix m n α :=
    ⟨λ i, if h₁ : i₁ = i then eq.rec_on h₁ (a.read_row i₂) else if h₂ : i₂ = i then eq.rec_on h₂ (a.read_row i₁) else a.read_row i⟩

    def exchange_cols (a : computable_matrix m n α) (j₁ j₂ : fin n) : computable_matrix m n α :=
    (computable_matrix.exchange_rows (a.transpose) j₁ j₂).transpose -- TODO: Can probably be optimised without transpose

    def add_multiple_of_row_to_row (a : computable_matrix m n α) [has_add α] [has_mul α] (i₁ : fin m) (s : α) (i₂ : fin m) : computable_matrix m n α :=
    computable_matrix.write_row a i₁ (array.map₂ (has_add.add) (a.read_row i₁) (array.map (has_mul.mul s) (a.read_row i₂)))

    def add_multiple_of_col_to_col (a : computable_matrix m n α) [has_add α] [has_mul α] (j₁ : fin n) (s : α) (j₂ : fin n) : computable_matrix m n α :=
    (add_multiple_of_row_to_row (a.transpose) j₁ s j₂).transpose -- TODO: Can probably be optimised without transpose

end computable_matrix


-- A number of these coercions are probably completely unncessary. 
-- I think I probably went more than a bit overboard. Will probably remove some later.

def array_of_vector {α : Type u} {n : ℕ} : vector α n → array n α :=
λ v, ⟨λ i, vector.nth v i⟩

instance coe_array_of_vector {α : Type u} {n : ℕ} : has_coe (vector α n) (array n α) :=
⟨array_of_vector⟩

def vector_of_array {α : Type u} {n : ℕ} : array n α → vector α n :=
 λ a, ⟨list.reverse (array.to_list a), by simp ⟩

instance coe_vector_of_array {α : Type u} {n : ℕ} : has_coe (array n α) (vector α n) :=
⟨vector_of_array⟩ 

-- TODO: These coes are unrelated and probably shouldn't be here.
instance coe_matrix_of_array_of_array {α : Type u} {m n : ℕ} : has_coe (array m (array n α)) (computable_matrix m n α) :=
⟨λ M, M⟩

instance coe_distributes_over_list {α β : Type u} [has_coe α β] : has_coe (list α) (list β) :=
⟨λ l, l.map coe⟩

instance coe_distributes_over_array {α β : Type u} {n : ℕ} [has_coe α β] : has_coe (array n α) (array n β) :=
⟨λ a, ⟨λ i, a.read i⟩⟩

instance coe_distributes_over_vector {α β : Type u} {n : ℕ} [has_coe α β] : has_coe (vector α n) (vector β n) :=
⟨λv, v.map coe⟩
-----------------------------------------------------------------

instance coe_matrix_of_vector_of_vector {α : Type u} {m n : ℕ} : has_coe (vector (vector α n) m) (computable_matrix m n α) :=
begin
    constructor,
    intros M,
    unfold computable_matrix,
    unfold computable_d_matrix,
    apply coe_array_of_vector.coe,
    apply coe_distributes_over_vector.coe, 
    from M, 
    from coe_array_of_vector,
end -- Todo: Golf this

instance coe_distributes_over_computable_matrix {m n : ℕ} {α β : Type u} [has_coe α β] : has_coe (computable_matrix m n α) (computable_matrix m n β) :=
⟨λ M, ⟨λ i, ⟨λ j, M.read i j⟩⟩⟩

-- Notation

def array.mk {α : Type*} {n : ℕ} (l : list α) (pr : l.length = n) : array n α :=
array_of_vector ⟨l, pr⟩

notation `![` l:(foldr `, ` (h t, list.cons h t) list.nil `]`) :=
  array.mk l (refl _)

def test1 : computable_matrix 2 3 ℤ := -- Just like our old friend fast_matrix!
![![ 1 , 1,  5 ], 
  ![ 0 , 1, 2 ]]

#eval test1 -- Reads the right value!




