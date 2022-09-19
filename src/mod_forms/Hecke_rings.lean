import group_theory.double_coset
import group_theory.commensurable
import data.finsupp.antidiagonal
import algebra.monoid_algebra.basic
import group_theory.free_abelian_group

variables {G : Type*} { I : Type*} [group G]
open commensurable
open_locale pointwise

lemma family_commensurable (H : subgroup G) (ι : I → subgroup G)
(hι : ∀ i, commensurable (ι i) H) (g : commensurable.commensurator H) (i j : I) :
  commensurable ((conj_act.to_conj_act (g : G))  • (ι i)) (ι j) :=
begin
 have h1 : commensurable ((conj_act.to_conj_act (g : G))  • (ι i)) H, by {
  have : commensurable ((conj_act.to_conj_act (g : G))  • (ι i)) (ι i), by {
  have ceq := commensurable.eq (hι i),
  rw ←commensurator_mem_iff,
  rw ceq,
  apply g.2,},
  apply trans this (hι i),},
 have h2 : commensurable H (ι j), by {apply commensurable.symm, apply (hι j)},
 apply commensurable.trans h1 h2,
end

lemma inf_relindex_nezero (H L R: subgroup G) (hL : commensurable L H) (hR : commensurable H R)
  (g : commensurable.commensurator H) : ((conj_act.to_conj_act (g : G))  • (R)).relindex L ≠ 0 :=
begin
  sorry,
end

def doset_coset_equiv (H L R: subgroup G) (hL : commensurable L H) (hR : commensurable H R)
  (g : commensurable.commensurator H) :
 (L ⧸ ((conj_act.to_conj_act (g : G))  • (R)).subgroup_of L) ≃ (doset (g : G) L R) :=
begin
  set f : (L ⧸ ((conj_act.to_conj_act (g : G))  • (R)).subgroup_of L) →  (doset (g : G) L R) :=
  λ x , ⟨ x.out' * (g : G) , by {rw doset.mem_doset, use x.out', simp, apply subgroup.one_mem,  }⟩,
  apply equiv.of_bijective f,
  rw function.bijective,
  split,
  rw function.injective,
  intros a b hab,
  simp_rw f at hab,
  simp at hab,
  rw ← quotient.out_inj,
  convert hab,

end


lemma doset_fin_coset_decomp  (H L R: subgroup G) (hL : commensurable L H) (hR : commensurable H R)
  (g : commensurable.commensurator H) : ∃ (s : finset G),
  doset (g : G) L R = (⋃ (h : s), right_coset R (h : G)) :=
begin
  have := doset.doset_union_right_coset L R g,
  rw ← this,
  have u2 : fintype (L ⧸ ((conj_act.to_conj_act (g : G))  • (R)).subgroup_of L ),
    by {apply subgroup.fintype_of_index_ne_zero, sorry,},
  have u3 := u2.elems,
  have u4 : (L ⧸ ((conj_act.to_conj_act (g : G))  • (R)).subgroup_of L ) ↪ G, by {sorry},
  have s := finset.map u4 u3,
  use s,
  ext,
  split,
  intro hx,
  simp_rw set.mem_Union at *,
  simp_rw mem_right_coset_iff at *,



end

def commensurable_fam (H : subgroup G) (ι : I → subgroup G) (g : commensurable.commensurator H)
  (i j : I) : set G := doset g (ι i) (ι j)

def setc2  (H L R: subgroup G) (hL : commensurable L H) (hR : commensurable H R) :=
  {s : set G // ∃ (g : commensurable.commensurator H), s = doset g L R}


def hecke_abelian_group (H L R: subgroup G) (hL : commensurable L H) (hR : commensurable H R) :=
  free_abelian_group (setc2 H L R hL hR)

/-
lemma doset_deg (H : subgroup G) (ι : I → subgroup G)
(hι : ∀ i, commensurable (ι i) H) (g : commensurable.commensurator H) (i j : I) :
  doset (g : G) (ι i) (ι j) =
-/
