import group_theory.index
import group_theory.p_group
import group_theory.quotient_group
import group_theory.coset
import group_theory.specific_groups.cyclic
import group_theory.abelianization

/-
lemma if_p_then_centre_nontrivial (n : ℕ) [fact (nat.prime n)] {H : Type*} [fintype H] [nontrivial H] [group H] : is_p_group n H → nontrivial (subgroup.center H) :=
begin
  intro h1,
  apply center_nontrivial h1,
end
-/

--open p_group

open fintype
open is_p_group
open group

variables (p : ℕ) [fact (nat.prime p)]
variables (G : Type*) [fintype G] [group G]

--def P : Type := {p : ℕ // prime p}  -- it's already defined, namely, as nat.primes

def order_psq : Prop := card G = p^2

namespace order_psq

lemma has_ord_psq : order_psq p G → ∃ q : ℕ , card G = q^2 :=
begin
  intro h1,
  use p,
  apply h1,
end

section G_has_order_psq

variables (hG : order_psq p G)
include hG

lemma p_group : is_p_group p G :=
begin
  exact of_card hG,
end

lemma centre_nontrivial [nontrivial G] : nontrivial (subgroup.center G) :=
center_nontrivial (p_group p G hG)

--def ZG : Type* := G ⧸ subgroup.center G --quotient_group.quotient.group (G) (subgroup.center G) --G / (subgroup.center G)

/--/
lemma centre_index_not_prime (H : Type*) [group H] [fintype H] [h0 : fintype (H ⧸ (subgroup.center H))] [nZ : fact (subgroup.center H).normal ] : ¬ ( prime (card (H ⧸ (subgroup.center H)))) :=
begin
  intro h1,
  have h2 : is_cyclic (H ⧸ subgroup.center H),
  {
    apply is_cyclic_of_prime_card _,
    exact h0,
    library_search, -- the output of library_search isn't closing the goal for some reason
  },
  --obtain ⟨ g , hg ⟩ : _,
  cases h2 with g,
  cases g with a ha,

  have h4 : (∀ x : G, ∃ y1 : H ⧸ subgroup.center H, ∃ y2 : subgroup.center H , x = y1 * y2),
  {
    sorry,
  },
  
  sorry,
end
-/

@[instance] noncomputable lemma quotient_with_center_is_fintype [decidable_rel setoid.r] : fintype (G ⧸ subgroup.center G) :=
begin
  apply quotient_group.fintype (subgroup.center G),
  sorry,
end

lemma centre_index_not_prime : ¬ nat.prime (card (G ⧸ subgroup.center G))
begin
  sorry,
end

theorem order_psq_are_abelian : (∀ x1 x2 : G, x1 * x2 = x2 * x1) :=
begin
  sorry,
end

-- hello

end G_has_order_psq

end order_psq