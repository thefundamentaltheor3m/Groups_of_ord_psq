import tactic

import group_theory.index
import group_theory.p_group
import group_theory.quotient_group
import group_theory.coset
import group_theory.specific_groups.cyclic
import group_theory.abelianization
import data.finite.basic
import data.finite.card

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

lemma group.center_eq_top_of_comm {H : Type*} [group H] (h : ∀ a b : H, a * b = b * a) : subgroup.center H = ⊤ :=
begin
  rw subgroup.eq_top_iff',
  intros x y,
  exact (h y x),
end

lemma group.center_eq_top_of_comm_comm_group {H : Type*} [comm_group H] : subgroup.center H = ⊤ :=
begin
  exact comm_group.center_eq_top,
end

lemma group.of_comm_center_eq_top {H : Type*} [group H] (h : (subgroup.center H = ⊤)) : (∀ a b : H, a * b = b * a) :=
begin
  rw subgroup.eq_top_iff' at h,
  intros x y,
  rw (h x),
end

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

lemma psq_center_nontrivial [nontrivial G] : nontrivial (subgroup.center G) :=
center_nontrivial (p_group p G hG)

--def ZG : Type* := G ⧸ subgroup.center G --quotient_group.quotient.group (G) (subgroup.center G) --G / (subgroup.center G)

/-
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

open_locale classical

@[instance] def quotient_with_center_is_fintype : finite (G ⧸ subgroup.center G) :=
infer_instance


/-
lemma center_index_not_prime_BAD : ¬ nat.prime (nat.card (G ⧸ subgroup.center G)) :=
begin
  sorry,
end
-/


lemma center_index_not_prime : ¬ nat.prime (fintype.card (G ⧸ subgroup.center G)) :=
begin
  intro h1,
  haveI : fact(nat.prime (card (G ⧸ subgroup.center G))) := ⟨h1⟩,
  haveI := is_cyclic_of_prime_card (rfl : card (G ⧸ subgroup.center G) = _),
  have h2 := commutative_of_cyclic_center_quotient (quotient_group.mk' (subgroup.center G)) (by simp),
  --have h3 : subgroup.center G = ⊤,
  --{
  --  exact group.center_eq_top_of_comm h2,
  --},
  have h4 : card (G ⧸ subgroup.center G) = 1,  -- That `card` is actually `fintype.card`
  {
    simp_rw [group.center_eq_top_of_comm h2, ← nat.card_eq_fintype_card],
    -- Need to go to `nat.card`
    --rw nat.card_eq_fintype_card.symm,
    exact subgroup.index_top,
  },
  rw h4 at h1,
  --revert h1,
  --change ¬ nat.prime (1 : ℕ),
  exact nat.not_prime_one h1,
end

lemma center_index_not_prime_2 : ¬ nat.prime (fintype.card (G ⧸ subgroup.center G)) :=
begin
  intro h1,
  haveI : fact(nat.prime (card (G ⧸ subgroup.center G))) := ⟨h1⟩,
  haveI := is_cyclic_of_prime_card (rfl : card (G ⧸ subgroup.center G) = _),
  haveI := comm_group_of_cycle_center_quotient (quotient_group.mk' (subgroup.center G)) (by simp),
  have h4 : card (G ⧸ subgroup.center G) = 1,
  {
    sorry,
  },
  rw h4 at h1,
  exact nat.not_prime_one h1,
end

/-
lemma center_index_not_prime_2 : ¬ nat.prime (fintype.card (G ⧸ subgroup.center G)) :=
begin
  intro h1,
  haveI : fact(nat.prime (card (G ⧸ subgroup.center G))) := ⟨h1⟩,
  haveI := is_cyclic_of_prime_card (rfl : card (G ⧸ subgroup.center G) = _),
  have h2 := commutative_of_cyclic_center_quotient (quotient_group.mk' (subgroup.center G)) (by simp),
  haveI := comm_group (G ⧸ (subgroup.center G)),
  --have h3 : subgroup.center G = ⊤,
  --{
  --  exact group.center_eq_top_of_comm h2,
  --},
  have h4 : card (G ⧸ subgroup.center G) = 1,  -- That `card` is actually `fintype.card`
  {
    rw ← comm_group.center_eq_top,
    rw ← nat.card_eq_fintype_card,
    -- Need to go to `nat.card`
    --rw nat.card_eq_fintype_card.symm,
    exact subgroup.index_top,
  },
  rw h4 at h1,
  --revert h1,
  --change ¬ nat.prime (1 : ℕ),
  exact nat.not_prime_one h1,
end
-/

/-
theorem order_psq_are_abelian [nontrivial G] : (∀ x1 x2 : G, x1 * x2 = x2 * x1) :=
begin
  apply group.of_comm_center_eq_top,
  have h1 : (card (subgroup.center G) ∣ card (G)),
  {
    exact (subgroup.center G).card_subgroup_dvd_card,
  },
  have h2 : (card G = p^2),
  {
    exact hG,
    --apply hG,
  },
  rw h2 at h1,
  rw nat.dvd_prime_pow at h1,
  rcases h1 with ⟨k, hk1, hk2⟩,
  swap,
  apply fact.out,
  interval_cases k,
  {
    exfalso,
    have h31 : nontrivial (subgroup.center G),
    {
      exact center_nontrivial (p_group p G hG),
    },
    rw subgroup.nontrivial_iff_exists_ne_one at h31,
    have h32 : (1:G) ∈ subgroup.center G,
    {
      --finish,
      --exact subgroup.has_one (subgroup.center G),
      sorry,
    },
    have h33 : (card (subgroup.center G) ≠ (1 : ℕ)),
    {
      intro hh,
      rw card_eq_one_iff at hh,
      cases h31 with x hhx,
      cases hhx with h34 hx,
      cases hh with y hy,
      cases y,
      have h35 : y_val = x,
      {
        norm_cast at *,
      },
      --cases h31 with y hh1,
      --cases hh1 with h34 hh2,
    },
    contradiction,
  },
  {
    exfalso,
    have h41 : card ()
    sorry,
  },
  {
    sorry,
  },
end
-/

theorem order_psq_are_abelian [nontrivial G] : (∀ x1 x2 : G, x1 * x2 = x2 * x1) :=
begin
  apply group.of_comm_center_eq_top,
  have h1 : (card (subgroup.center G) ∣ card (G)),
  {
    exact (subgroup.center G).card_subgroup_dvd_card,
  },
  have h2 : (card G = p^2),
  {
    exact hG,
    --apply hG,
  },
  rw h2 at h1,
  rw nat.dvd_prime_pow at h1,
  rcases h1 with ⟨k, hk1, hk2⟩,
  swap,
  apply fact.out,
  interval_cases k,
  {
    exfalso,
    have h31 : nontrivial (subgroup.center G),
    {
      exact center_nontrivial (p_group p G hG),
    },
    rw subgroup.nontrivial_iff_exists_ne_one at h31,
    
  },
  {
    exfalso,
    have h41 : card ()
    sorry,
  },
  {
    sorry,
  },
end

end G_has_order_psq

end order_psq