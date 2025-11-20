import Mathlib.Data.Real.Archimedean

import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Data.PFun

open OmegaCompletePartialOrder

/-! A domain is an ω-complete partial order with a bottom element. -/
class Domain (α : Type*) extends OmegaCompletePartialOrder α, OrderBot α

namespace PFun

/-
α →. β is definitionally equal to α → Part β, but typeclass inference
does not unfold most definitions, so we use inferInstanceAs to use
definitional equality instead.
-/

variable {α β : Type*}

noncomputable instance : OmegaCompletePartialOrder (α →. β) :=
  inferInstanceAs (OmegaCompletePartialOrder (α → Part β))

instance : OrderBot (α →. β) := inferInstanceAs (OrderBot (α → Part β))

noncomputable instance : Domain (α →. β) where

end PFun

section Q1

/-!
# Exercises

## Exercise: Chains form a domain

For a partially ordered set `(P, ⊑)`, let `(Ch(P), ⊑_ptw)` be the partially ordered set
of chains in `P` ordered pointwise.

Show that if `P` is a domain then so is `Ch(P)`.
-/

instance [Domain P] : LE (Chain P) where
  le x y := ∀ n, x n ≤ y n

instance [Domain P] : PartialOrder (Chain P) where
  le x y := x ≤ y
  le_refl x n := le_refl (x n)
  le_trans x y z hxy hyz n := le_trans (hxy n) (hyz n)
  le_antisymm x y hxy hyx := OrderHom.ext _ _ <| funext fun n => le_antisymm (hxy n) (hyx n)

def chainωSup [Domain P] (c : Chain (Chain P)) : Chain P where
  toFun := fun n => ωSup {
    toFun := fun m => c m n
    monotone' := fun i j hij => (c.monotone' hij) n
  }
  monotone' := by
    intro i j hij
    apply ωSup_le
    intro m
    have h1 : c m i ≤ c m j := (c m).monotone' hij
    let chain_j : Chain P := {
      toFun := fun k => c k j
      monotone' := fun a b hab => by
        have : c a ≤ c b := c.monotone' hab
        exact this j
    }
    have h2 : c m j ≤ ωSup chain_j := le_ωSup chain_j m
    exact le_trans h1 h2

instance [Domain P] : OmegaCompletePartialOrder (Chain P) where
  ωSup := chainωSup
  le_ωSup (c : Chain (Chain P)) (i : ℕ) n := by
    show c i n ≤ (chainωSup c) n
    convert le_ωSup _ i using 1
    rfl
  ωSup_le (c : Chain (Chain P)) (x : Chain P) (h : ∀ i, c i ≤ x) := by
    intro n
    apply ωSup_le
    intro i
    exact h i n

instance [Domain P] : OrderBot (Chain P) where
  bot := { toFun := fun _ => ⊥, monotone' := fun _ _ _ => le_refl ⊥ }
  bot_le := fun _ _ => bot_le

instance [Domain P] : Domain (Chain P) where

end Q1

section Q2

/-!
## Exercise: Function spaces form a domain

For partially ordered sets `(P, ⊑_P)` and `(Q, ⊑_Q)`, define the set
`(P ⇒ Q) = {f | f is a monotone function from (P, ⊑_P) to (Q, ⊑_Q)}`
and, for all `f, g ∈ (P ⇒ Q)`, let
`f ⊑_(P⇒Q) g ⟺ ∀ p ∈ P. f(p) ⊑_Q g(p)`

(i) Prove that `((P ⇒ Q), ⊑_(P⇒Q))` is a partially ordered set

(ii) Prove that if `(Q, ⊑_Q)` is a domain then so is `((P ⇒ Q), ⊑_(P⇒Q))`
-/

variable {P Q : Type*} [PartialOrder P]

section i

/-! Part (i): `(P →o Q)` forms a partial order -/

variable [PartialOrder Q]

instance : PartialOrder (P →o Q) := inferInstance

/-! Part (ii): If Q is a domain, then so is `(P →o Q)` -/

end i

section ii

variable [Domain Q]

noncomputable instance : OmegaCompletePartialOrder (P →o Q) where
  ωSup c := {
    toFun := fun p => ωSup (c.map (OrderHom.apply p))
    monotone' := by
      intro p₁ p₂ hp
      apply ωSup_le
      intro n
      calc
        c n p₁ ≤ c n p₂ := (c n).monotone' hp
        c n p₂ ≤ ωSup (c.map (OrderHom.apply p₂)) :=le_ωSup (c.map (OrderHom.apply p₂)) n
  }
  le_ωSup c i := by
    intro p
    exact le_ωSup (c.map (OrderHom.apply p)) i
  ωSup_le c g h := by
    intro p
    apply ωSup_le
    intro n
    exact h n p

instance : OrderBot (P →o Q) where
  bot := { toFun := fun _ => ⊥, monotone' := fun _ _ _ => le_refl ⊥ }
  bot_le := fun _ _ => bot_le

noncomputable instance : Domain (P →o Q) where

end ii

end Q2

section Q3

/-!
## Exercise: Corollary from Q1 applied to Q2(ii)

Q1: If P is a domain, then Ch(P) (chains in P) is a domain.
Q2(ii): If Q is a domain, then (P ⇒ Q) is a domain.

Corollary: If Q is a domain, then Ch(P ⇒ Q) (chains of monotone functions) is also a domain.
-/

variable {P Q : Type*} [PartialOrder P] [Domain Q]

noncomputable instance : Domain (Chain (P →o Q)) := inferInstance

end Q3

section Q7

/-!
## Exercise Q7: Chain-complete posets without bottom elements

Suppose that (D, ⊑) is a poset which is chain-complete but does not have a
least element, and that f : D → D is a continuous function.

(i) Give an example of such (D, ⊑) and f for which f has no fixed point.

(ii) If d ∈ D satisfies d ⊑ f(d), prove that there is a least element e ∈ D
     satisfying d ⊑ e = f(e).
-/

section i

/-!
Part (i): A chain-complete poset without bottom where a continuous function
has no fixed point

Example: D = (0, 1] with the usual ordering, f(x) = x / 2
-/

abbrev Ioc01 : Set ℝ := Set.Ioc 0 1

private lemma Ioc01_bddAbove (c : Chain Ioc01) : BddAbove (Set.range fun n => (c n).val) := by
  use 1
  rintro _ ⟨n, rfl⟩
  exact (c n).property.2

private lemma Ioc01_nonempty (c : Chain Ioc01) : (Set.range fun n => (c n).val).Nonempty :=
  ⟨(c 0).val, 0, rfl⟩

noncomputable instance : OmegaCompletePartialOrder Ioc01 where
  ωSup c := by
    let s := sSup (Set.range fun n => (c n).val)
    refine ⟨s, ?_, ?_⟩
    · have : (c 0).val ≤ s := le_csSup (Ioc01_bddAbove c) ⟨0, rfl⟩
      linarith [(c 0).property.1]
    · apply csSup_le (Ioc01_nonempty c)
      rintro _ ⟨n, rfl⟩; exact (c n).property.2
  le_ωSup c i := le_csSup (Ioc01_bddAbove c) ⟨i, rfl⟩
  ωSup_le c x h := by
    apply csSup_le (Ioc01_nonempty c)
    rintro _ ⟨n, rfl⟩; exact h n

noncomputable def halve : Ioc01 →o Ioc01 where
  toFun := fun ⟨x, hpos, hle⟩ => ⟨x / 2, by
    constructor
    · exact div_pos hpos zero_lt_two
    · linarith⟩
  monotone' := by
    intro ⟨x, _, _⟩ ⟨y, _, _⟩ (h : x ≤ y)
    simp only [Subtype.mk_le_mk]
    linarith

theorem not_fix_halve : ¬∃ x, halve x = x := by
  intro ⟨⟨x, hpos, hle⟩, h_fix⟩
  have : x / 2 = x := Subtype.ext_iff.mp h_fix
  linarith

end i

section ii

/-! Part (ii): Existence of least fixed point above d when d ⊑ f(d) -/

variable {D : Type*} [OmegaCompletePartialOrder D] (f : D →𝒄 D)

theorem least_fixed_point_above (d : D) (h : d ≤ f d) :
    ∃ e, IsLeast {x | d ≤ x ∧ f x = x} e := by
  let chain := OmegaCompletePartialOrder.fixedPoints.iterateChain f d h
  use ωSup chain
  constructor
  · constructor
    · exact le_ωSup chain 0
    · exact OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_mem_fixedPoint f d h
  · intro e' ⟨hd, he'⟩
    -- Use mathlib's theorem that ωSup of iterates is ≤ any fixed point
    exact OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_le_fixedPoint f d h he' hd

end ii

end Q7

namespace Scott

variable {D : Type*} [Domain D]

def iterateChain (f : D →o D) : Chain D := fixedPoints.iterateChain f ⊥ bot_le

/-! fix f = ωSup of the chain: ⊥, f(⊥), f²(⊥), ... -/
def fix (f : D →o D) : D := ωSup (iterateChain f)

theorem fix_eq (f : D →𝒄 D) : f (fix f.toOrderHom) = fix f.toOrderHom :=
  fixedPoints.ωSup_iterate_mem_fixedPoint f ⊥ bot_le

/-
Scott induction principle for ω-CPOs:
Let D be a domain, f : D → D be continuous, and S ⊆ D. If the set S
(i) contains ⊥,
(ii) is chain-closed, i.e. the lub of any chain of elements of S is also in S,
(iii) is stable for f, i.e. f(S) ⊆ S,
then fix(f) ∈ S.

The least fixed point fix(f) is the ωSup of the chain: ⊥, f(⊥), f²(⊥), f³(⊥), ...
-/
@[elab_as_elim]
theorem scott_induction {f : D →o D} {p : D → Prop}
  (h_bot : p ⊥)
  (h_chain_closed : ∀ (c : Chain D), (∀ n, p (c n)) → p (ωSup c))
  (h_stable : ∀ d, p d → p (f d))
  : p (fix f) := by
  have h_iterates n : p (iterateChain f n) := by
    induction n with
    | zero => exact h_bot
    | succ n ih =>
      change p (f^[n + 1] ⊥)
      rw [Function.iterate_succ_apply']
      exact h_stable (f^[n] ⊥) ih
  exact h_chain_closed (iterateChain f) h_iterates

noncomputable def g (f : D × D →𝒄 D) : D × D →o D × D where
  toFun := fun (d₁, d₂) => (f (d₁, f (d₁, d₂)), f (f (d₁, d₂), d₂))
  monotone' := by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨h₁, h₂⟩
    constructor
    · exact f.monotone' ⟨h₁, f.monotone' ⟨h₁, h₂⟩⟩
    · exact f.monotone' ⟨f.monotone' ⟨h₁, h₂⟩, h₂⟩
end Scott

section Q9

/-!
## Q9: Fixed point of commutative function

Suppose that D is a domain and f : D × D → D is a continuous function satisfying
the property ∀ d, e ∈ D. f(d, e) = f(e, d). Let g : D × D → D × D be defined by
g(d₁, d₂) = (f(d₁, f(d₁, d₂)), f(f(d₁, d₂), d₂))
Let (u₁, u₂) = fix(g). Show that u₁ = u₂ using Scott induction.
-/

variable {D : Type*} [Domain D]

noncomputable instance {P Q : Type*} [Domain P] [Domain Q] : Domain (P × Q) where

open Scott

theorem fix_commutative (f : D × D →𝒄 D) (hf_comm : ∀ d₁ d₂, f (d₁, d₂) = f (d₂, d₁)) :
    let (u₁, u₂) := fix (g f); u₁ = u₂ := by
  refine scott_induction ?base ?chain_closed ?stable
  case base => rfl
  case chain_closed =>
    intro c h_chain
    change ωSup (c.map ⟨Prod.fst, fun _ _ h => h.1⟩) = ωSup (c.map ⟨Prod.snd, fun _ _ h => h.2⟩)
    congr 1
    ext n
    exact h_chain n
  case stable =>
    intro d ih
    change f (d.1, f (d.1, d.2)) = f (f (d.1, d.2), d.2)
    rw [ih, hf_comm]

end Q9

section Q10

/-!
## Q10: Fixed points of product functions

Let D and E be domains and let f : D → D and g : E → E be continuous functions.
(i) Define f × g : D × E → D × E to be the continuous function given by (f × g)(d, e) =
(f(d), g(e)) and let π₁ : D × E → D and π₂ : D × E → E respectively denote the
first and second projection functions. Show that fix (f × g) ⊑ (fix (f), fix (g)) and that
fix (f) ⊑ π₁(fix (f × g)) and fix (g) ⊑ π₂(fix (f × g)).
(ii) It follows from part (i) that fix (f × g) = (fix (f), fix (g)). Use this and Scott's Fixed
Point Induction Principle to show that, for all strict continuous functions h : D → E,
h ◦ f = g ◦ h =⇒ h(fix (f)) = fix (g).
-/

open Scott

variable {D E : Type*} [Domain D] [Domain E]

section i


/-! Product of two continuous functions -/
def prod_map (f : D →o D) (g : E →o E) : D × E →o D × E where
  toFun := fun (d, e) => (f d, g e)
  monotone' := by
    intro ⟨d₁, e₁⟩ ⟨d₂, e₂⟩ ⟨hd, he⟩
    exact ⟨f.monotone' hd, g.monotone' he⟩

def π₁ : D × E →o D where
  toFun := Prod.fst
  monotone' := fun _ _ h => h.1

def π₂ : D × E →o E where
  toFun := Prod.snd
  monotone' := fun _ _ h => h.2

/-! Product of two continuous functions is continuous -/
def prod_map_cont (f : D →𝒄 D) (g : E →𝒄 E) : D × E →𝒄 D × E where
  toFun := fun (d, e) => (f d, g e)
  monotone' := by
    intro ⟨d₁, e₁⟩ ⟨d₂, e₂⟩ ⟨hd, he⟩
    exact ⟨f.monotone' hd, g.monotone' he⟩
  map_ωSup' := by
    intro c
    ext
    · have h₁ := f.map_ωSup' (c.map OrderHom.fst)
      convert h₁ using 2
    · have h₂ := g.map_ωSup' (c.map OrderHom.snd)
      convert h₂ using 2

-- Part (i): Three lemmas showing fix (f × g) = (fix f, fix g)

/-- The fixed point of a product is bounded above by the product of fixed points -/
theorem fix_prod_le (f : D →𝒄 D) (g : E →𝒄 E) :
    fix (prod_map_cont f g).toOrderHom ≤ (fix f.toOrderHom, fix g.toOrderHom) := by
  refine scott_induction ?base ?chain_closed ?stable
  case base => exact bot_le
  case chain_closed =>
    intro c h_chain
    constructor
    · apply ωSup_le
      intro n
      exact (h_chain n).1
    · apply ωSup_le
      intro n
      exact (h_chain n).2
  case stable =>
    intro d hd
    constructor
    · calc
        f d.1 ≤ f (fix f) := f.monotone' hd.1
        _ = fix f := fix_eq f
    · calc
        g d.2 ≤ g (fix g) := g.monotone' hd.2
        _ = fix g := fix_eq g

/-! The first component of fix(f × g) is bounded below by fix f -/
theorem fix_le_fst_fix_prod (f : D →𝒄 D) (g : E →𝒄 E) :
    fix f.toOrderHom ≤ π₁ (fix (prod_map_cont f g).toOrderHom) := by
  refine scott_induction ?base ?chain_closed ?stable
  case base => exact bot_le
  case chain_closed =>
    intro c h_chain
    apply ωSup_le
    exact h_chain
  case stable =>
    intro d hd
    calc
      f d ≤ f (π₁ (fix (prod_map_cont f g).toOrderHom)) := f.monotone' hd
      _ = π₁ ((prod_map_cont f g) (fix (prod_map_cont f g).toOrderHom)) := by
        simp [prod_map_cont, π₁]
      _ = π₁ (fix (prod_map_cont f g).toOrderHom) := by rw [fix_eq]

/-! The second component of fix(f × g) is bounded below by fix g -/
theorem fix_le_snd_fix_prod (f : D →𝒄 D) (g : E →𝒄 E) :
    fix g.toOrderHom ≤ π₂ (fix (prod_map_cont f g).toOrderHom) := by
  refine scott_induction ?base ?chain_closed ?stable
  case base => exact bot_le
  case chain_closed =>
    intro c h_chain
    apply ωSup_le
    exact h_chain
  case stable =>
    intro d hd
    calc
      g d ≤ g (π₂ (fix (prod_map_cont f g).toOrderHom)) := g.monotone' hd
      _ = π₂ ((prod_map_cont f g) (fix (prod_map_cont f g).toOrderHom)) := by
        simp [prod_map_cont, π₂]
      _ = π₂ (fix (prod_map_cont f g).toOrderHom) := by rw [fix_eq]

/-! Corollary: The fixed point of a product equals the product of fixed points -/
theorem fix_prod (f : D →𝒄 D) (g : E →𝒄 E) :
    fix (prod_map_cont f g).toOrderHom = (fix f.toOrderHom, fix g.toOrderHom) :=
  le_antisymm (fix_prod_le f g) ⟨fix_le_fst_fix_prod f g, fix_le_snd_fix_prod f g⟩

end i

section ii

def IsStrict {D E : Type*} [PartialOrder D] [PartialOrder E] [OrderBot D] [OrderBot E]
    (h : D → E) : Prop :=
  h ⊥ = ⊥

/-!
For strict continuous functions that commute with fixed points via h ∘ f = g ∘ h,
the function preserves fixed points: h(fix f) = fix g
-/
theorem strict_hom_preserves_fix (f : D →𝒄 D) (g : E →𝒄 E) (h : D →𝒄 E)
    (h_strict : IsStrict h.toFun)
    (h_comm : ∀ d, h (f d) = g (h d)) :
    h (fix f) = fix g := by
  apply le_antisymm
  · show h (fix f) ≤ fix g
    refine scott_induction ?base ?chain_closed ?stable
    case base =>
      change h.toFun ⊥ ≤ fix g
      rw [h_strict]
      exact bot_le
    case chain_closed =>
      intro c h_chain
      calc
        h.toFun (ωSup c) = ωSup (c.map h) := h.map_ωSup' c
        _ ≤ fix g := by
          apply ωSup_le
          exact h_chain
    case stable =>
      intro d hd
      calc
        h (f d) = g (h d) := h_comm d
        _ ≤ g (fix g) := g.monotone' hd
        _ = fix g := fix_eq g
  · show fix g ≤ h (fix f)
    refine scott_induction ?base ?chain_closed ?stable
    case base => exact bot_le
    case chain_closed =>
      intro c h_chain
      apply ωSup_le
      exact h_chain
    case stable =>
      intro d hd
      calc
        g d ≤ g (h (fix f.toOrderHom)) := g.monotone' hd
        _ = h (f (fix f.toOrderHom)) := by rw [← h_comm]
        _ = h (fix f.toOrderHom) := by rw [fix_eq]

end ii

end Q10
