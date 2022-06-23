import group_theory.p_group

--open p_group

open fintype
open is_p_group

variables (p : ℕ) (G : Type*) [fintype G] [group G] [is_p_group p G]

def order_psq {H : Type*} (p : ℕ) [fintype H] [group H] (p : ℕ) [fact p.prime]: Prop := card G = p^2

variables {p} {G}

namespace order_psq

lemma iff_ord_psq : order_psq G ↔ card G = p^2 :=
begin
  refl,
end

variable (hG : order_psq p G)
include hG

lemma center_nontrivial : nontrivial (subgroup.center G) :=
begin

  sorry,
end

end order_psq