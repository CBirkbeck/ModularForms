import group_theory.group_action



universes v u
variables {X : Type v} {G : Type u} [group G] [mul_action G X]

lemma is_group_action.inverse_left (g : G) (x : X):  g⁻¹ •  g • x = x :=
begin
  rw ← mul_smul,
  simp, 
end

lemma is_group_action.inverse_right (g : G) (x: X) :  g •  g⁻¹ • x = x :=
begin
  rw ← mul_smul,
  simp, 
end


def orbit_rel' : setoid X :=
{ r := λ a b, a ∈ mul_action.orbit G b,
  iseqv := ⟨mul_action.mem_orbit_self, λ a b, by simp [mul_action.orbit_eq_iff.symm, eq_comm],
    λ a b, by simp [mul_action.orbit_eq_iff.symm, eq_comm] {contextual := tt}⟩ }

 