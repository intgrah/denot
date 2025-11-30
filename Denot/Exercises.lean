import Mathlib.Data.Real.Archimedean
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Data.PFun
import Mathlib.Data.Vector.Defs

open OmegaCompletePartialOrder

/-! A `Domain` is an ω-complete partial order with a bottom element. -/
class Domain (α : Type*) extends OmegaCompletePartialOrder α, OrderBot α

/-
`α →o β` is notation for `OrderHom`, homomorphisms on orders, or monotone functions.
`Chain α` is an abbreviation for `ℕ →o α`, i.e. increasing sequences of `α`.
-/

namespace PFun

/-
`α →. β` is notation for partial functions between `α` and `β`.
`α →. β` is definitionally equal to `α → Part β`, but typeclass inference
does not unfold most definitions, so we use inferInstanceAs to use
definitional equality instead.
-/

variable {α β : Type*}

noncomputable instance : OmegaCompletePartialOrder (α →. β) :=
  inferInstanceAs (OmegaCompletePartialOrder (α → Part β))

instance : OrderBot (α →. β) := inferInstanceAs (OrderBot (α → Part β))

noncomputable instance : Domain (α →. β) where

end PFun

section P1

section Q1

/-!
# Exercises

## Question 1: Chains form a domain

For a partially ordered set `(P, ⊑)`, let `(Ch(P), ⊑_ptw)` be the partially ordered set
of chains in `P` ordered pointwise.

Show that if `P` is a domain then so is `Ch(P)`.
-/

/- Let P be a domain. -/
variable {P : Type*} [Domain P]

/-- Define the pointwise ordering on chains: x ⊑ y iff x(n) ⊑ y(n) for all n -/
instance : LE (Chain P) where
  le x y := ∀ n, x n ≤ y n

/--
To show Ch(P) is a partially ordered set, we verify:
1. Reflexivity: x ⊑ x holds pointwise since P is a partial order
2. Transitivity: If x ⊑ y and y ⊑ z, then x ⊑ z by transitivity in P
3. Antisymmetry: If x ⊑ y and y ⊑ x, then x = y by extensionality and antisymmetry in P
-/
instance : PartialOrder (Chain P) where
  -- Reflexivity: For all x, x ≤ x because for all n, x n ≤ x n
  le_refl x := fun n => le_refl (x n)
  -- Transitivity: For all n, x n ≤ y n and y n ≤ z n implies x n ≤ z n
  le_trans {x y z} := fun hxy hyz n => le_trans (hxy n) (hyz n)
  -- Antisymmetry: Chains are equal if they agree pointwise
  le_antisymm {x y} := by
    -- Let x y be chains, and assume x ≤ y and y ≤ x.
    intro hxy hyx
    apply OrderHom.ext
    -- Function extensionality: we show that x and y agree on all values n
    funext n
    -- Use the definition of ≤ on Chains and antisymmetry.
    exact le_antisymm (hxy n) (hyx n)

/--
Given a chain c : ℕ → Ch(P) of chains, we construct its supremum as a chain in P.
For each index n, we take the supremum over all chains c m at position n.
That is, (ωSup c)(n) = ωSup_m (c m n).

To verify this is monotone, we show that for i ≤ j:
  ωSup_m (c m i) ≤ ωSup_m (c m j)
This holds because each c m i ≤ c m j (by monotonicity of c m).
-/
def chainωSup (c : Chain (Chain P)) : Chain P where
  toFun := fun n => ωSup {
    toFun := fun m => c m n
    monotone' := fun i j hij => (c.monotone' hij) n
  }
  monotone' := by
    intro i j hij
    -- Show ωSup_m (c m i) ≤ ωSup_m (c m j)
    apply ωSup_le
    intro m
    -- Construct the chain at position j
    let chain_j : Chain P := {
      toFun := fun k => c k j
      monotone' := fun a b hab => by
        have : c a ≤ c b := c.monotone' hab
        exact this j
    }
    -- Each c m i ≤ c m j since c m is monotone, and c m j is bounded by the supremum
    calc
      c m i ≤ c m j := (c m).monotone' hij
      _ ≤ ωSup chain_j := le_ωSup chain_j m

/--
To show Ch(P) is ω-complete, we define ωSup as above and verify:
1. For each i, c i ⊑ ωSup c (each chain in the sequence is below the supremum)
2. If c i ⊑ x for all i, then ωSup c ⊑ x (the supremum is the least upper bound)
-/
instance : OmegaCompletePartialOrder (Chain P) where
  ωSup := chainωSup
  -- For each position n, c i n ≤ (ωSup c) n
  le_ωSup := by
    intro c i n
    show c i n ≤ (chainωSup c) n
    convert le_ωSup _ i using 1
    rfl
  -- If all c i ≤ x, then ωSup c ≤ x pointwise
  ωSup_le := by
    intro c x h n
    show chainωSup c n ≤ x n
    apply ωSup_le
    intro i
    exact h i n

/-! The bottom element of Ch(P) -/
instance : OrderBot (Chain P) where
  bot := {
    -- The bottom element of Ch(P) is the constant chain ⊥(n) = ⊥_P for all n.
    toFun _ := ⊥
    -- This is indeed a chain since ⊥ ≤ ⊥ by reflexivity.
    monotone' := fun _ _ _ => le_refl ⊥
  }
  -- It is below all other chains, since ∀ x, ⊥ ≤ x
  bot_le _ := fun _ => bot_le

/-- Combining the above, Ch(P) is a domain. -/
instance : Domain (Chain P) where

end Q1

section Q2

/-!
## Question 2: Function spaces form a domain

For partially ordered sets `(P, ⊑_P)` and `(Q, ⊑_Q)`, define the set
`(P ⇒ Q) = {f | f is a monotone function from (P, ⊑_P) to (Q, ⊑_Q)}`
and, for all `f, g ∈ (P ⇒ Q)`, let
`f ⊑_(P⇒Q) g ⟺ ∀ p ∈ P. f(p) ⊑_Q g(p)`

(i) Prove that `((P ⇒ Q), ⊑_(P⇒Q))` is a partially ordered set

(ii) Prove that if `(Q, ⊑_Q)` is a domain then so is `((P ⇒ Q), ⊑_(P⇒Q))`
-/

variable {P Q : Type*} [PartialOrder P]

section i

/-!
### Part (i): `(P →o Q)` forms a partial order
-/

variable [PartialOrder Q]

/--
The pointwise ordering on monotone functions forms a partial order.
This is already in Mathlib.
-/
instance : PartialOrder (P →o Q) := OrderHom.instPartialOrder

/--
Explicit construction showing that `P →o Q` is a partial order.
The ordering f ⊑ g is defined by ∀ p, f p ⊑ g p.
-/
instance : PartialOrder (P →o Q) where
  le f g := ∀ p, f p ≤ g p
  -- Reflexivity: f p ≤ f p for all p
  le_refl f := fun p => le_refl (f p)
  -- Transitivity: If f ⊑ g and g ⊑ h, then f ⊑ h pointwise
  le_trans {f g h} := fun hfg hgh p => le_trans (hfg p) (hgh p)
  -- Antisymmetry: If f ⊑ g and g ⊑ f, then f = g by extensionality
  le_antisymm {f g} := by
    intro hfg hgf
    apply OrderHom.ext
    funext p
    exact le_antisymm (hfg p) (hgf p)

end i

section ii

/-!
### Part (ii): If Q is a domain, then so is `(P →o Q)`

To show (P →o Q) is a domain, we show it is ω-complete and has a bottom element.
-/

variable [Domain Q]

/--
The supremum of a chain of monotone functions is computed pointwise:
  (ωSup c) p = ωSup_n (c n p)
Since each c n is monotone and Q is ω-complete, this defines a monotone function.
-/
noncomputable instance : OmegaCompletePartialOrder (P →o Q) where
  ωSup c := {
    toFun p := ωSup (c.map (OrderHom.apply p))
    -- To show the supremum is monotone: if p₁ ≤ p₂, then (ωSup c) p₁ ≤ (ωSup c) p₂
    monotone' := by
      intro p₁ p₂ hp
      -- Show ωSup_n (c n p₁) ≤ ωSup_n (c n p₂)
      apply ωSup_le
      intro n
      -- For each n, c n p₁ ≤ c n p₂ (by monotonicity of c n)
      calc
        c n p₁ ≤ c n p₂ := (c n).monotone' hp
        c n p₂ ≤ ωSup (c.map (OrderHom.apply p₂)) := le_ωSup (c.map (OrderHom.apply p₂)) n
  }
  -- For each i, c i ⊑ ωSup c, which means (c i) p ≤ (ωSup c) p for all p
  le_ωSup c i p := le_ωSup (c.map (OrderHom.apply p)) i
  -- If c i ⊑ g for all i, then ωSup c ⊑ g
  ωSup_le c g := by
    intro (h : ∀ i, c i ≤ g) p
    apply ωSup_le
    intro n
    exact h n p

/--
The bottom element of (P →o Q) is the constant function mapping everything to ⊥_Q.
-/
instance : OrderBot (P →o Q) where
  bot := {
    toFun _ := ⊥
    monotone' := fun _ _ _ => le_refl ⊥
  }
  bot_le _ := fun _ => bot_le

/-- Combining ω-completeness and bottom element, (P →o Q) is a domain. -/
noncomputable instance : Domain (P →o Q) where

end ii

end Q2

section Q3

/-!
## Question 3: Q1 as a special case of  Q2(ii)

Q1: If P is a domain, then Ch(P) (chains in P) is a domain.
Q2(ii): If Q is a domain, then (P ⇒ Q) is a domain.

Take P to be ℕ with the usual ordering. Chain P is by definition ℕ →o P.
-/

noncomputable instance {P : Type*} [Domain P] : Domain (Chain P) :=
  inferInstanceAs (Domain (ℕ →o P))

end Q3

section Q7

/-!
## Question 7: Chain-complete posets without bottom elements

Suppose that (D, ⊑) is a poset which is chain-complete but does not have a
least element, and that f : D → D is a continuous function.

(i) Give an example of such (D, ⊑) and f for which f has no fixed point.

(ii) If d ∈ D satisfies d ⊑ f(d), prove that there is a least element e ∈ D
     satisfying d ⊑ e = f(e).
-/

section i

/-!
### Part (i): A chain-complete poset without bottom where a continuous function has no fixed point

Example: D = (0, 1] with the usual ordering, f(x) = x / 2

This is ω-complete because the supremum of any chain exists in the reals and stays in (0, 1].
However, there is no least element (0 is not in the set).
The function f(x) = x / 2 has no fixed point since x = x/2 implies x = 0, which is not in (0, 1].
-/

/-- The interval (0, 1] as a subset of the reals -/
abbrev Ioc01 : Set ℝ := Set.Ioc 0 1

/-- Every chain in (0, 1] is bounded above by 1 -/
private lemma Ioc01_bddAbove (c : Chain Ioc01) : BddAbove (Set.range fun n => (c n).val) := by
  use 1
  rintro _ ⟨n, rfl⟩
  exact (c n).property.2

/-- Every chain in (0, 1] is nonempty (contains its first element) -/
private lemma Ioc01_nonempty (c : Chain Ioc01) : (Set.range fun n => (c n).val).Nonempty :=
  ⟨(c 0).val, 0, rfl⟩

/--
The interval (0, 1] is ω-complete:
Given a chain c : ℕ → (0, 1], we define ωSup c as the supremum in ℝ.
- The supremum exists since the chain is bounded above by 1
- The supremum is > 0 since c 0 > 0 and c 0 ≤ sSup
- The supremum is ≤ 1 since all elements are ≤ 1
-/
noncomputable instance : OmegaCompletePartialOrder Ioc01 where
  ωSup c := by
    let s := sSup (Set.range fun n => (c n).val)
    refine ⟨s, ?_, ?_⟩
    -- Show 0 < s: since c 0 > 0 and c 0 ≤ s, we have 0 < s
    · have : (c 0).val ≤ s := le_csSup (Ioc01_bddAbove c) ⟨0, rfl⟩
      linarith [(c 0).property.1]
    -- Show s ≤ 1: since all c n ≤ 1, their supremum is ≤ 1
    · apply csSup_le (Ioc01_nonempty c)
      rintro _ ⟨n, rfl⟩; exact (c n).property.2
  -- Each element of the chain is below the supremum
  le_ωSup c i := le_csSup (Ioc01_bddAbove c) ⟨i, rfl⟩
  -- The supremum is the least upper bound
  ωSup_le c x h := by
    apply csSup_le (Ioc01_nonempty c)
    rintro _ ⟨n, rfl⟩; exact h n

/--
The halving function f(x) = x/2 on (0, 1].
- For x ∈ (0, 1], we have 0 < x/2 < x ≤ 1, so x/2 ∈ (0, 1]
- This function is monotone
-/
noncomputable def halve : Ioc01 →o Ioc01 where
  toFun := fun ⟨x, hpos, hle⟩ => ⟨x / 2, by linarith, by linarith⟩
  -- Monotonicity: if x ≤ y then x/2 ≤ y/2
  monotone' := by
    intro ⟨x, _, _⟩ ⟨y, _, _⟩ (h : x ≤ y)
    simp only [Subtype.mk_le_mk]
    linarith

/--
The halving function has no fixed point.
If x = x/2, then x = 0, but 0 ∉ (0, 1].
-/
theorem not_fix_halve : ¬∃ x, Function.IsFixedPt halve x := by
  intro ⟨⟨x, hpos, hle⟩, h_fix⟩
  -- From halve x = x, we get x/2 = x
  have : x / 2 = x := Subtype.ext_iff.mp h_fix
  -- This implies x = 0, contradicting x > 0
  linarith

noncomputable instance : OmegaCompletePartialOrder Empty where
  le _ _ := True
  le_refl _ := trivial
  le_trans {_ _ _} := fun _ _ => trivial
  le_antisymm {a _} := fun _ _ => a.elim
  ωSup c := c 0
  le_ωSup _ _ := trivial
  ωSup_le _ _ _ := trivial
  lt_iff_le_not_ge {a _ } := a.elim

def f : Empty →𝒄 Empty where
  toFun := id
  monotone' := fun _ _ h => h
  map_ωSup' := fun _ => rfl

theorem not_fix_f : ¬∃ x, Function.IsFixedPt f x := fun ⟨x, _⟩ => x.elim

end i

section ii

/-!
### Part (ii): Existence of least fixed point above d when d ⊑ f(d)

If d ≤ f(d), we can construct an ascending chain:
  d ≤ f(d) ≤ f²(d) ≤ f³(d) ≤ ...
The supremum e = ωSup {fⁿ(d) | n ∈ ℕ} is a fixed point with d ≤ e,
and it is the least such fixed point.
-/

variable {D : Type*} [OmegaCompletePartialOrder D] (f : D →𝒄 D)

/--
Kleene's theorem for ω-CPOs without bottom:
If d ≤ f(d), then the supremum of iterating f from d is the least fixed point above d.
-/
theorem least_fixed_point_above (d : D) (h : d ≤ f d) :
    ∃ e, IsLeast {x | d ≤ x ∧ f x = x} e := by
  -- Construct the chain d, f(d), f²(d), ...
  let chain := OmegaCompletePartialOrder.fixedPoints.iterateChain f d h
  use ωSup chain
  constructor
  · constructor
    -- d ≤ ωSup chain since d is the first element
    · exact le_ωSup chain 0
    -- ωSup chain is a fixed point by continuity
    · exact OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_mem_fixedPoint f d h
  · intro e' ⟨hd, he'⟩
    -- ωSup chain is the least fixed point above d
    exact OmegaCompletePartialOrder.fixedPoints.ωSup_iterate_le_fixedPoint f d h he' hd

end ii

end Q7

namespace Scott

/-!
# Scott's Fixed Point Theory

This namespace contains definitions and theorems for computing least fixed points in domains.
-/

variable {D : Type*} [Domain D]

/--
The iteration chain starting from ⊥: ⊥, f(⊥), f²(⊥), f³(⊥), ...
This chain is monotone since ⊥ ≤ f(⊥) for any function with a domain.
-/
def iterateChain (f : D →o D) : Chain D := fixedPoints.iterateChain f ⊥ bot_le

/--
The least fixed point of f is defined as the supremum of the iteration chain.
fix(f) = ωSup {⊥, f(⊥), f²(⊥), f³(⊥), ...}
-/
def fix (f : D →o D) : D := ωSup (iterateChain f)

/--
Kleene's fixed point theorem: f(fix f) = fix f
The supremum of iterating f from ⊥ is indeed a fixed point of f.
-/
theorem fix_eq (f : D →𝒄 D) : f (fix f.toOrderHom) = fix f.toOrderHom :=
  fixedPoints.ωSup_iterate_mem_fixedPoint f ⊥ bot_le

/-!
## Scott Induction Principle

Let D be a domain, f : D → D be monotone, and p : D → Prop be a predicate. If:
1. p(⊥) holds (base case)
2. p is chain-closed: if p(cₙ) for all n, then p(ωSup c) (inductive case)
3. p is stable: if p(d) then p(f d) (preservation under f)

Then p(fix f) holds.
-/
@[elab_as_elim]
theorem scott_induction {f : D →o D} {p : D → Prop}
  (h_bot : p ⊥)
  (h_chain_closed : ∀ (c : Chain D), (∀ n, p (c n)) → p (ωSup c))
  (h_stable : ∀ d, p d → p (f d))
  : p (fix f) := by
  -- Show p holds for all elements of the iteration chain
  have h_iterates n : p (iterateChain f n) := by
    induction n with
    | zero =>
        -- Base case: p(⊥)
        exact h_bot
    | succ n ih =>
        -- Inductive case: if p(fⁿ(⊥)) then p(fⁿ⁺¹(⊥))
        change p (f^[n + 1] ⊥)
        rw [Function.iterate_succ_apply']
        exact h_stable (f^[n] ⊥) ih
  -- Apply chain-closure to conclude p(fix f)
  exact h_chain_closed (iterateChain f) h_iterates

/--
For a continuous function f : D × D → D, define g : D × D → D × D by:
  g(d₁, d₂) = (f(d₁, f(d₁, d₂)), f(f(d₁, d₂), d₂))
This function is used in Q9 to show that fixed points of commutative functions
have equal components.
-/
noncomputable def g (f : D × D →𝒄 D) : D × D →o D × D where
  toFun := fun (d₁, d₂) => (f (d₁, f (d₁, d₂)), f (f (d₁, d₂), d₂))
  -- Monotonicity: if (a₁, a₂) ≤ (b₁, b₂), then g(a₁, a₂) ≤ g(b₁, b₂)
  monotone' := by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨h₁, h₂⟩
    constructor
    -- First component: f(a₁, f(a₁, a₂)) ≤ f(b₁, f(b₁, b₂))
    · exact f.monotone' ⟨h₁, f.monotone' ⟨h₁, h₂⟩⟩
    -- Second component: f(f(a₁, a₂), a₂) ≤ f(f(b₁, b₂), b₂)
    · exact f.monotone' ⟨f.monotone' ⟨h₁, h₂⟩, h₂⟩

end Scott

section Q9

/-!
## Question 9: Fixed point of commutative function

Suppose that D is a domain and f : D × D → D is a continuous function satisfying
the property ∀ d, e ∈ D. f(d, e) = f(e, d). Let g : D × D → D × D be defined by
g(d₁, d₂) = (f(d₁, f(d₁, d₂)), f(f(d₁, d₂), d₂))
Let (u₁, u₂) = fix(g). Show that u₁ = u₂ using Scott induction.
-/

variable {D : Type*} [Domain D]

/-- The product of two domains is a domain -/
noncomputable instance {P Q : Type*} [Domain P] [Domain Q] : Domain (P × Q) where

open Scott

/--
If f : D × D → D is commutative and (u₁, u₂) = fix(g(f)), then u₁ = u₂.

Proof by Scott induction on the predicate p(d₁, d₂) = (d₁ = d₂):
- Base: (⊥, ⊥) satisfies ⊥ = ⊥
- Chain-closed: If all (cₙ)₁ = (cₙ)₂, then (ωSup c)₁ = (ωSup c)₂
- Stable: If d₁ = d₂, then g(d₁, d₂) = (f(d₁, f(d₁, d₂)), f(f(d₁, d₂), d₂))
         By commutativity: f(d₁, f(d₁, d₂)) = f(d₁, f(d₂, d₁)) = f(f(d₂, d₁), d₂)
         Since d₁ = d₂, this simplifies to show the components are equal.
-/
theorem fix_commutative (f : D × D →𝒄 D) (hf_comm : ∀ d₁ d₂, f (d₁, d₂) = f (d₂, d₁)) :
    let (u₁, u₂) := fix (g f); u₁ = u₂ := by
  refine scott_induction ?base ?chain_closed ?stable
  -- Base case: ⊥.1 = ⊥.2
  case base => rfl
  -- Chain-closed: if cₙ.1 = cₙ.2 for all n, then (ωSup c).1 = (ωSup c).2
  case chain_closed =>
    intro c h_chain
    change ωSup (c.map ⟨Prod.fst, fun _ _ h => h.1⟩) = ωSup (c.map ⟨Prod.snd, fun _ _ h => h.2⟩)
    -- The chains of first and second components are equal
    congr 1
    ext n
    exact h_chain n
  -- Stable: if d.1 = d.2, then (g f d).1 = (g f d).2
  case stable =>
    intro d ih
    change f (d.1, f (d.1, d.2)) = f (f (d.1, d.2), d.2)
    -- Use the inductive hypothesis d.1 = d.2 and commutativity
    rw [ih, hf_comm]

end Q9

section Q10

/-!
## Question 10: Fixed points of product functions

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

section
i

/-!
### Part (i): The fixed point of a product function

We show that fix(f × g) = (fix f, fix g) by proving both directions of the inequality.
-/

/--
The product of two monotone functions: (f × g)(d, e) = (f d, g e)
This is monotone componentwise.
-/
def prod_map (f : D →o D) (g : E →o E) : D × E →o D × E where
  toFun := fun (d, e) => (f d, g e)
  monotone' := by
    intro ⟨d₁, e₁⟩ ⟨d₂, e₂⟩ ⟨hd, he⟩
    exact ⟨f.monotone' hd, g.monotone' he⟩

/-- First projection π₁(d, e) = d is monotone -/
def π₁ : D × E →o D where
  toFun := Prod.fst
  monotone' := fun _ _ h => h.1

/-- Second projection π₂(d, e) = e is monotone -/
def π₂ : D × E →o E where
  toFun := Prod.snd
  monotone' := fun _ _ h => h.2

/--
The product of two continuous functions is continuous.
Continuity follows because suprema are computed componentwise:
  (f × g)(ωSup c) = (f(ωSup c₁), g(ωSup c₂))
                  = (ωSup(f ∘ c₁), ωSup(g ∘ c₂))
                  = ωSup((f × g) ∘ c)
-/
def prod_map_cont (f : D →𝒄 D) (g : E →𝒄 E) : D × E →𝒄 D × E where
  toFun := fun (d, e) => (f d, g e)
  -- Monotonicity inherited from f and g
  monotone' := by
    intro ⟨d₁, e₁⟩ ⟨d₂, e₂⟩ ⟨hd, he⟩
    exact ⟨f.monotone' hd, g.monotone' he⟩
  -- Continuity: (f × g)(ωSup c) = ωSup((f × g) ∘ c)
  map_ωSup' := by
    intro c
    ext
    -- First component: f preserves suprema
    · have h₁ := f.map_ωSup' (c.map OrderHom.fst)
      convert h₁ using 2
    -- Second component: g preserves suprema
    · have h₂ := g.map_ωSup' (c.map OrderHom.snd)
      convert h₂ using 2

/--
The fixed point of a product is bounded above by the product of fixed points.
That is, fix(f × g) ≤ (fix f, fix g).

Proof by Scott induction on p(d, e) = (d, e) ≤ (fix f, fix g):
- Base: (⊥, ⊥) ≤ (fix f, fix g) trivially
- Chain-closed: If cₙ ≤ (fix f, fix g) for all n, then ωSup c ≤ (fix f, fix g) componentwise
- Stable: If d ≤ (fix f, fix g), then (f × g)(d) ≤ (fix f, fix g) by monotonicity
-/
theorem fix_prod_le (f : D →𝒄 D) (g : E →𝒄 E) :
    fix (prod_map_cont f g).toOrderHom ≤ (fix f.toOrderHom, fix g.toOrderHom) := by
  refine scott_induction ?base ?chain_closed ?stable
  -- Base: (⊥, ⊥) ≤ (fix f, fix g)
  case base => exact bot_le
  -- Chain-closed: supremum of bounded elements is bounded
  case chain_closed =>
    intro c h_chain
    constructor
    · apply ωSup_le
      intro n
      exact (h_chain n).1
    · apply ωSup_le
      intro n
      exact (h_chain n).2
  -- Stable: if d ≤ (fix f, fix g) then (f × g)(d) ≤ (fix f, fix g)
  case stable =>
    intro (d, e) ⟨hd, he⟩
    constructor
    · calc
        f d ≤ f (fix f) := f.monotone' hd
        _ = fix f := fix_eq f
    · calc
        g e ≤ g (fix g) := g.monotone' he
        _ = fix g := fix_eq g

/--
The first component of fix(f × g) is bounded below by fix f.
That is, fix f ≤ π₁(fix(f × g)).

Proof by Scott induction on p(d) = d ≤ π₁(fix(f × g)):
- Base: ⊥ ≤ π₁(fix(f × g)) trivially
- Chain-closed: If cₙ ≤ π₁(fix(f × g)) for all n, then ωSup c ≤ π₁(fix(f × g))
- Stable: If d ≤ π₁(fix(f × g)), then f(d) ≤ π₁((f × g)(fix(f × g))) = π₁(fix(f × g))
-/
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

/--
The second component of fix(f × g) is bounded below by fix g.
That is, fix g ≤ π₂(fix(f × g)).
The proof is symmetric to the first component case.
-/
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

/--
The fixed point of a product equals the product of fixed points.
fix(f × g) = (fix f, fix g)

This follows from the three inequalities proven above.
-/
theorem fix_prod (f : D →𝒄 D) (g : E →𝒄 E) :
    fix (prod_map_cont f g).toOrderHom = (fix f.toOrderHom, fix g.toOrderHom) :=
  le_antisymm (fix_prod_le f g) ⟨fix_le_fst_fix_prod f g, fix_le_snd_fix_prod f g⟩

end i

section ii

/-!
### Part (ii): Strict homomorphisms preserve fixed points

A function h : D → E is *strict* if h(⊥) = ⊥.
If h is strict, continuous, and commutes with f and g (h ∘ f = g ∘ h),
then h preserves fixed points: h(fix f) = fix g.
-/

/--
A function is strict if it preserves the bottom element.
-/
def IsStrict {D E : Type*} [PartialOrder D] [PartialOrder E] [OrderBot D] [OrderBot E]
    (h : D → E) : Prop :=
  h ⊥ = ⊥

/--
Strict homomorphisms preserve fixed points.

Given:
- f : D → D and g : E → E are continuous functions
- h : D → E is a strict continuous function
- h commutes with f and g: h ∘ f = g ∘ h

Then: h(fix f) = fix g

Proof: We show both inequalities using Scott induction.

Direction 1 (h(fix f) ≤ fix g):
By Scott induction on p(d) = h(d) ≤ fix g:
- Base: h(⊥) = ⊥ ≤ fix g (by strictness)
- Chain-closed: h preserves suprema by continuity
- Stable: If h(d) ≤ fix g, then h(f(d)) = g(h(d)) ≤ g(fix g) = fix g

Direction 2 (fix g ≤ h(fix f)):
By Scott induction on p(e) = e ≤ h(fix f):
- Base: ⊥ ≤ h(fix f) trivially
- Chain-closed: supremum of bounded elements is bounded
- Stable: If e ≤ h(fix f), then g(e) ≤ g(h(fix f)) = h(f(fix f)) = h(fix f)
-/
theorem strict_hom_preserves_fix (f : D →𝒄 D) (g : E →𝒄 E) (h : D →𝒄 E)
    (h_strict : IsStrict h.toFun)
    (h_comm : ∀ d, h (f d) = g (h d)) :
    h (fix f) = fix g := by
  apply le_antisymm
  -- Direction 1: h(fix f) ≤ fix g
  · show h (fix f) ≤ fix g
    refine scott_induction ?base ?chain_closed ?stable
    -- Base: h(⊥) = ⊥ ≤ fix g
    case base =>
      change h.toFun ⊥ ≤ fix g
      rw [h_strict]
      exact bot_le
    -- Chain-closed: h(ωSup c) = ωSup(h ∘ c) ≤ fix g
    case chain_closed =>
      intro c h_chain
      calc
        h.toFun (ωSup c) = ωSup (c.map h) := h.map_ωSup' c
        _ ≤ fix g := by
          apply ωSup_le
          exact h_chain
    -- Stable: If h(d) ≤ fix g, then h(f(d)) = g(h(d)) ≤ g(fix g) = fix g
    case stable =>
      intro d hd
      calc
        h (f d) = g (h d) := h_comm d
        _ ≤ g (fix g) := g.monotone' hd
        _ = fix g := fix_eq g
  -- Direction 2: fix g ≤ h(fix f)
  · show fix g ≤ h (fix f)
    refine scott_induction ?base ?chain_closed ?stable
    -- Base: ⊥ ≤ h(fix f)
    case base => exact bot_le
    -- Chain-closed: If cₙ ≤ h(fix f) for all n, then ωSup c ≤ h(fix f)
    case chain_closed =>
      intro c h_chain
      apply ωSup_le
      exact h_chain
    -- Stable: If e ≤ h(fix f), then g(e) ≤ g(h(fix f)) = h(f(fix f)) = h(fix f)
    case stable =>
      intro d hd
      calc
        g d ≤ g (h (fix f.toOrderHom)) := g.monotone' hd
        _ = h (f (fix f.toOrderHom)) := by rw [← h_comm]
        _ = h (fix f.toOrderHom) := by rw [fix_eq]

end ii

end Q10

end P1

section P2

namespace PCF

inductive Ty : Type where
| nat : Ty
| bool : Ty
| arrow : Ty → Ty → Ty

notation "nat" => Ty.nat
notation "bool" => Ty.bool
notation:40 τ₁ " →' " τ₂ => Ty.arrow τ₁ τ₂

inductive Tm : Nat → Type where
| zero : Tm n
| succ : Tm n → Tm n
| pred : Tm n → Tm n
| true : Tm n
| false : Tm n
| zero? : Tm n → Tm n
| if : Tm n → Tm n → Tm n → Tm n
| var : Fin n → Tm n
| fun : Ty → Tm (n + 1) → Tm n
| app : Tm n → Tm n → Tm n
| fix : Tm n → Tm n

notation "zero" => Tm.zero
notation "succ(" e ")" => Tm.succ e
notation "pred(" e ")" => Tm.pred e
notation "true" => Tm.true
notation "false" => Tm.false
notation "zero?(" e ")" => Tm.zero? e
notation "if' " b " then " e₁ " else " e₂ => Tm.if b e₁ e₂
notation "#" i => Tm.var i
notation "fix(" e ")" => Tm.fix e

def shiftAbove (c : Nat) : Tm n → Tm (n + 1)
| zero => zero
| succ(e) => succ(shiftAbove c e)
| pred(e) => pred(shiftAbove c e)
| true => true
| false => false
| zero?(e) => zero?(shiftAbove c e)
| if' b then e₁ else e₂ => if' shiftAbove c b then shiftAbove c e₁ else shiftAbove c e₂
| #i => #(if i.val < c then ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩ else i.succ)
| .fun τ e => .fun τ (shiftAbove (c + 1) e)
| .app e₁ e₂ => .app (shiftAbove c e₁) (shiftAbove c e₂)
| fix(e) => fix(shiftAbove c e)

def shift : Tm n → Tm (n + 1) := shiftAbove 0

def substAt (j : Fin (n + 1)) (u : Tm n) : Tm (n + 1) → Tm n
| zero => zero
| succ(e) => succ(substAt j u e)
| pred(e) => pred(substAt j u e)
| true => true
| false => false
| zero?(e) => zero?(substAt j u e)
| if' b then e₁ else e₂ => if' substAt j u b then substAt j u e₁ else substAt j u e₂
| .var i =>
    if h₁ : i = j then u
    else if h₂ : i < j then #⟨i, Nat.lt_of_lt_of_le h₂ (Nat.lt_succ_iff.mp j.isLt)⟩
    else .var ⟨i - 1, Nat.sub_lt_right_of_lt_add
      (Nat.one_le_of_lt (Nat.lt_of_le_of_ne (Fin.not_lt.mp h₂) (Ne.symm (Fin.val_ne_of_ne h₁))))
      i.isLt⟩
| .fun τ e => .fun τ (substAt j.succ (shift u) e)
| .app e₁ e₂ => .app (substAt j u e₁) (substAt j u e₂)
| fix(e) => fix(substAt j u e)

def subst (u : Tm n) : Tm (n + 1) → Tm n := substAt 0 u

def Ctx := List.Vector Ty

set_option hygiene false

notation:40 Γ " ⊢ " e " : " τ => HasType Γ e τ
notation:max Γ "; " τ => List.Vector.cons τ Γ

inductive HasType : Ctx n → Tm n → Ty → Prop where
| zero {Γ} :
  (Γ ⊢ zero : nat)
| succ {Γ e} :
  (Γ ⊢ e : nat) →
  (Γ ⊢ succ(e) : nat)
| pred {Γ e} :
  (Γ ⊢ e : nat) →
  (Γ ⊢ pred(e) : nat)
| true {Γ} :
  (Γ ⊢ true : bool)
| false {Γ} :
  (Γ ⊢ false : bool)
| isz {Γ e} :
  (Γ ⊢ e : nat) →
  (Γ ⊢ zero?(e) : bool)
| if {Γ e₁ e₂ e₃ τ} :
  (Γ ⊢ e₁ : bool) →
  (Γ ⊢ e₂ : τ) →
  (Γ ⊢ e₃ : τ) →
  (Γ ⊢ if' e₁ then e₂ else e₃ : τ)
| var {Γ i} :
  (Γ ⊢ #i : Γ.get i)
| fun {Γ τ₁ e τ₂} :
  ((Γ; τ₁) ⊢ e : τ₂) →
  (Γ ⊢ .fun τ₁ e : τ₁ →' τ₂)
| app {Γ e₁ τ₁ e₂ τ₂} :
  (Γ ⊢ e₁ : τ₁ →' τ₂) →
  (Γ ⊢ e₂ : τ₁) →
  (Γ ⊢ e₁.app e₂ : τ₂)
| fix {Γ e τ} :
  (Γ ⊢ e : τ →' τ) →
  (Γ ⊢ fix(e) : τ)

theorem substitution {Γ : Ctx n} {e₁ τ₁ e₂ τ₂}
    (he₁ : Γ ⊢ e₁ : τ₁)
    (he₂ : (Γ; τ₁) ⊢ e₂ : τ₂) :
    (Γ ⊢ subst e₁ e₂ : τ₂) := by
  sorry

inductive IsValue : Tm 0 → Prop where
| zero : IsValue zero
| succ {e} : IsValue e → IsValue succ(e)
| true : IsValue true
| false : IsValue false
| fun {τ e} : IsValue (.fun τ e)

def Value := { e : Tm 0 // IsValue e }
def Value.zero : Value := ⟨.zero, IsValue.zero⟩
def Value.succ (v : Value) : Value := ⟨v.val.succ, v.property.succ⟩
def Value.true : Value := ⟨.true, IsValue.true⟩
def Value.false : Value := ⟨.false, IsValue.false⟩
def Value.fun (τ : Ty) (e : Tm 1) : Value := ⟨.fun τ e, IsValue.fun⟩

notation:40 e " (⇓" τ ") " v => Eval e τ v

inductive Eval : Tm 0 → Ty → Value → Prop where
| val {τ v} :
    (.nil ⊢ v.val : τ) →
    (v.val (⇓τ) v)
| succ {e v} :
    (e (⇓nat) v) →
    (succ(e) (⇓nat) v.succ)
| pred {e v} :
    (e (⇓nat) v.succ) →
    (pred(e) (⇓nat) v)
| zero_z {e} :
    (e (⇓nat) .zero) →
    (zero?(e) (⇓bool) .true)
| zero_s {e v} :
    (e (⇓nat) .succ v) →
    (zero?(e) (⇓bool) .false)
| if_t {b e₁ e₂ τ v} :
    (b (⇓bool) .true) →
    (e₁ (⇓τ) v) →
    ((if' b then e₁ else e₂) (⇓τ) v)
| if_f {b e₁ e₂ τ v} :
    (b (⇓bool) .false) →
    (e₂ (⇓τ) v) →
    ((if' b then e₁ else e₂) (⇓τ) v)
| fun {e e₁ τ₁ e₂ τ₂ v} :
    (e (⇓τ₁ →' τ₂) .fun τ₁ e₂) →
    (subst e₁ e₂ (⇓τ₂) v) →
    (e.app e₁ (⇓τ₂) v)
| fix {e τ v} :
    (e.app fix(e) (⇓τ) v) →
    (fix(e) (⇓τ) v)

def plus : Tm 0 :=
  .fun .nat <| -- x : nat
  fix(
    .fun (nat →' nat) <| -- f : nat → nat
    .fun nat <| -- y : nat
    if' zero?(#0) then -- y = 0
      #2 -- x
    else
      succ((#1).app pred(#0))) -- f (y - 1)

example : .nil ⊢ plus : nat →' nat →' nat := by
  apply HasType.fun
  apply HasType.fix
  apply HasType.fun
  apply HasType.fun
  apply HasType.if
  · apply HasType.isz
    exact HasType.var
  · exact HasType.var
  · apply HasType.succ
    apply HasType.app
    · exact HasType.var
    · apply HasType.pred
      apply HasType.var

def Diverges (e : Tm 0) (τ : Ty) : Prop := ¬∃ v, e (⇓τ) v

notation:40 e " (⇑" τ ")" => Diverges e τ

def Ω (τ : Ty) : Tm 0 := fix(.fun τ (#0))

end PCF

end P2
