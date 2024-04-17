import tactic

import group_theory.index
import group_theory.p_group
import group_theory.quotient_group
import group_theory.coset
import group_theory.specific_groups.cyclic
import group_theory.abelianization
import data.finite.basic
import data.finite.card
import data.real.basic
import group_theory.subgroup.basic

open fintype
open is_p_group
open group

/-- A group that is commutative can be turned into a comm_group
(See https://github.com/leanprover-community/mathlib/pull/14960#issuecomment-1178880188)
-/
instance {G} : can_lift (group G) (comm_group G) :=
{ coe := @comm_group.to_group G,
  cond := λ g, by exactI (∀ x y : G, commute x y),
  prf := λ g hg, ⟨{mul_comm := hg, ..g}, by cases g; refl⟩ }


/-- My lemma -/
lemma group.center_eq_top_of_comm {H : Type*} [group H] (h : ∀ a b : H, a * b = b * a) : subgroup.center H = ⊤ :=
begin
  rw subgroup.eq_top_iff',
  intros x y,
  exact (h y x),
end

lemma group.of_comm_center_eq_top {H : Type*} [group H] (h : (subgroup.center H = ⊤)) : (∀ a b : H, a * b = b * a) :=
begin
  rw subgroup.eq_top_iff' at h,
  intros x y,
  rw (h x),
end

variables (p : ℕ) [fact (nat.prime p)]
variables (G : Type*) [fintype G] [group G]

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

open_locale classical

@[instance] def quotient_with_center_is_fintype : finite (G ⧸ subgroup.center G) :=
infer_instance

lemma center_index_not_prime : ¬ nat.prime (fintype.card (G ⧸ subgroup.center G)) :=
begin
  intro h1,
  haveI : fact(nat.prime (card (G ⧸ subgroup.center G))) := ⟨h1⟩,
  haveI := is_cyclic_of_prime_card (rfl : card (G ⧸ subgroup.center G) = _),
  --letI := comm_group_of_cycle_center_quotient (quotient_group.mk' (subgroup.center G)) (by simp),
  have h2 := commutative_of_cyclic_center_quotient (quotient_group.mk' (subgroup.center G)) (by simp),
  unfreezingI { lift ‹group G› to comm_group G using h2 },
  have h3 : subgroup.center G = ⊤,
  {
    exact comm_group.center_eq_top,  -- working
  },
  have h4 : card (G ⧸ subgroup.center G) = 1,
  {
    simp_rw [h3, ← nat.card_eq_fintype_card],
    exact subgroup.index_top,
  },
  rw h4 at h1,
  exact nat.not_prime_one h1,
end

open_locale cardinal

#check subgroup.card_mul_index (subgroup.center G)

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
  },
  rw h2 at h1,
  rw nat.dvd_prime_pow at h1,
  rcases h1 with ⟨k, hk1, hk2⟩,
  swap,
  apply fact.out,
  interval_cases k,
  -- # |Z(G)| = 1
  {
    simp at hk2,
    exfalso,
    have h31 : nontrivial (subgroup.center G),
    {
      exact center_nontrivial (p_group p G hG),
    },
    rw subgroup.nontrivial_iff_exists_ne_one at h31,
    rcases h31 with ⟨x, hx, hxx⟩,
    have h32 : subgroup.center G = ⊥,
    {
      --have hcalc : card (subgroup.center G) ≤ 1, linarith,
      --rw ← subgroup.card_le_one_iff_eq_bot,
      --exact hcalc,
      --simp_rw hk2,
      rw [← subgroup.card_le_one_iff_eq_bot, hk2],
    },
    have hxx' : x = 1,
    {
      --finish,
      --rw h32 at hx,
      rw subgroup.eq_bot_iff_forall at h32,
      exact h32 x hx,
    },
    contradiction,
  },
  -- # |Z(G)| = p
  {
    exfalso,
    have h41 : p * (subgroup.center G).index = p^2,
    {
      simp at hk2,
      simp_rw ← nat.card_eq_fintype_card at hk2,
      simp_rw ← nat.card_eq_fintype_card at h2,
      rw [← h2, ← hk2],
      exact subgroup.card_mul_index (subgroup.center G),
    },
    have h42 : (subgroup.center G).index = p,
    {
      have hcalc : p * (subgroup.center G).index = p * p,
      {
        simp_rw h41,
        exact sq p,
      },
      simp at hcalc,
      have hcalc2 : ¬ (p = 0),
      {
        intro hcp,
        have hcp2 := _inst_1.out,
        rw hcp at hcp2,
        have hcp3 := nat.not_prime_zero,
        contradiction,
      },
      cases hcalc with hcl hcr,
      {
        exact hcl,
      },
      {
        exfalso,
        contradiction,
      },
      --finish,  -- works
      --sorry,  -- Compiles much faster than it would with `finish`
    },
    have h43 : nat.prime (card (G ⧸ subgroup.center G)),
    {
      have hcalc : nat.card (G ⧸ subgroup.center G) = p, exact h42,
      rw nat.card_eq_fintype_card at hcalc,
      rw hcalc,
      exact _inst_1.out,
    },
    have h44 : ¬ nat.prime (fintype.card (G ⧸ subgroup.center G)),
    {
      apply center_index_not_prime p G,
      exact hG,
    },
    contradiction,
  },
  -- # |Z(G)| = p^2
  {
    apply subgroup.eq_top_of_card_eq,
    rw h2,
    exact hk2,
  },
end

end G_has_order_psq

end order_psq
