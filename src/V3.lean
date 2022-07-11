import tactic

import group_theory.index
import group_theory.p_group
import group_theory.quotient_group
import group_theory.coset
import group_theory.specific_groups.cyclic
import group_theory.abelianization
import data.finite.basic
import data.finite.card

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
  have h2 := commutative_of_cyclic_center_quotient (quotient_group.mk' (subgroup.center G)) (by simp),
  have h4 : card (G ⧸ subgroup.center G) = 1,
  {
    simp_rw [group.center_eq_top_of_comm h2, ← nat.card_eq_fintype_card],
    exact subgroup.index_top,
  },
  rw h4 at h1,
  exact nat.not_prime_one h1,
end

lemma center_index_not_prime_2 : ¬ nat.prime (fintype.card (G ⧸ subgroup.center G)) :=
begin
  intro h1,
  haveI : fact(nat.prime (card (G ⧸ subgroup.center G))) := ⟨h1⟩,
  haveI := is_cyclic_of_prime_card (rfl : card (G ⧸ subgroup.center G) = _),
  letI := comm_group_of_cycle_center_quotient (quotient_group.mk' (subgroup.center G)) (by simp),
  have h3 : subgroup.center G = ⊤,
  {
    exact comm_group.center_eq_top,  -- not working
  },
  have h4 : card (G ⧸ subgroup.center G) = 1,
  {
    simp_rw [h3, ← nat.card_eq_fintype_card],
    exact subgroup.index_top,
  },
  rw h4 at h1,
  exact nat.not_prime_one h1,
end

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