import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Data.PFun
import Mathlib.Data.Part
import Mathlib.Order.Basic
import Mathlib.Order.WithBot

universe u v

/-!
# Domain theory

Fixed point equations such as the ones we considered arise very often in giving denotational semantics to languages with recursive features. Beginning with Dana Scott's
pioneering work in the late 60s, a mathematical theory called domain theory has been
developed to provide a setting in which not only can we always find solutions for the
fixed point equations arising from denotational semantics, but also we can pick out
solutions that are minimal in a suitable sense. Our order on partial functions is a
particularly simple case of such a domain.

As we saw, the key idea is to consider a partial order between the mathematical
objects used as denotations, expressing the fact that one object is approximated by,
or carries more information than, or is more defined than another one below it in the
ordering. Then the minimal solution of a fixed point equation can be constructed as
the limit of an increasing chain of approximations to the solution, and this turns out
to ensure a good match between denotational and operational semantics.

The first part of this course is devoted to develop some of this mathematical background of domain theory. The second will then use it setup to provide denotational
semantics to a simple but representative functional language: Pcf.
-/

/-!
# Part I
# Domain Theory

# 2  Least Fixed Points

This section introduces a mathematical theory, domain theory, which amongst other
things provides a general framework for constructing the least fixed points used in the
denotational semantics of various programming language features. The theory was
introduced by Dana Scott in the 70s.

## 2.1  Posets and monotone functions

Domain theory makes use of partially ordered sets satisfying certain completeness
properties.
-/

section Posets

/-!
**Definition 1 (Partially ordered set)** A partial order on a set 𝐷 is a binary relation
⊑ that is
- reflexive:
-/

variable {D : Type u} [PartialOrder D]

#check (le_refl : ∀ d : D, d ≤ d)

/-!
- transitive:
-/

#check (le_trans : ∀ {d d' d'' : D}, d ≤ d' → d' ≤ d'' → d ≤ d'')

/-!
- antisymmetric:
-/

#check (le_antisymm : ∀ {d d' : D}, d ≤ d' → d' ≤ d → d = d')

/-!
Such a pair (𝐷, ⊑) is called a partially ordered set, or poset. 𝐷 is called the underlying
set of the poset (𝐷, ⊑).

Most of the time we will refer to posets just by naming their underlying sets and
use the same symbol ⊑ to denote the partial order in a variety of different posets.
-/

#print PartialOrder

end Posets

/-!
**Example 1 (Domain of partial functions, 𝑋 ⇀ 𝑌)** The set (𝑋 ⇀ 𝑌) of all partial
functions from a set 𝑋 to a set 𝑌 can be made into a poset, as follows:

Underlying set: partial functions 𝑓 with domain of definition dom(𝑓) ⊆ 𝑋 and taking
values in 𝑌;

Order: 𝑓 ⊑ 𝑔 if dom(𝑓) ⊆ dom(𝑔) and ∀𝑥 ∈ dom(𝑓). 𝑓(𝑥) = 𝑔(𝑥), i.e. if
graph(𝑓) ⊆ graph(𝑔).

It was this domain for the case 𝑋 = 𝑌 = State that we used for the denotation of
commands in Section 1.1.
-/

-- PFun is defined as `α → Part β`, a type alias for a Pi type
-- Even though Part α has PartialOrder and Pi has Pi.partialOrder,
-- type aliases don't automatically inherit instances in Lean 4
-- So we need to define the PartialOrder instance explicitly:

instance {α β : Type*} : PartialOrder (α →. β) where
  le f g := ∀ a b, b ∈ f a → f a = g a
  le_refl f a b h := rfl
  le_trans f g h fg gh a b fa := by
    rw [fg a b fa]
    exact gh a b (fg a b fa ▸ fa)
  le_antisymm f g fg gf := by
    apply PFun.ext
    intro a b
    constructor
    · intro hf
      rw [← fg a b hf]
      exact hf
    · intro hg
      rw [← gf a b hg]
      exact hg

-- Verify it works
#check (inferInstance : PartialOrder (ℕ →. ℕ))

-- Notation for the information order
infixl:50 " ⊑ " => LE.le (α := PFun _ _)

section MonotoneFunctions

/-!
**Definition 2 (Monotone function)** A function 𝑓 : 𝐷 → 𝐸 between posets is monotone if

∀𝑑, 𝑑′∈ 𝐷. 𝑑 ⊑ 𝑑′ ⇒ 𝑓(𝑑) ⊑ 𝑓(𝑑′).
-/

variable {D : Type u} {E : Type v} [PartialOrder D] [PartialOrder E]

#check (Monotone : (D → E) → Prop)
#check (fun (f : D → E) => ∀ {d d' : D}, d ≤ d' → f d ≤ f d' : (D → E) → Prop)

#print OrderHom

example (f : D →o E) : Monotone f := f.monotone'

/-!
**Example 2** Given posets 𝐷 and 𝐸, for each 𝑒 ∈ 𝐸 it is easy to see that the constant
function 𝐷 → 𝐸 with value 𝑒, λ𝑑 ∈ 𝐷 . 𝑒, is monotone.
-/

example (e : E) : Monotone (fun (_ : D) => e) := by
  intro a b _
  rfl

/-!
**Example 3** When 𝐷 is the domain of partial functions (State ⇀ State) (Example 1),
the function 𝐹_𝑏,𝑐: 𝐷 → 𝐷 defined in Section 1.2 in connection with the denotational
semantics of while-loops is a monotone function.

We leave the verification of this as an exercise.
-/

end MonotoneFunctions

/-!
## 2.2  Least elements and pre-fixed points
-/

section LeastElements

/-!
**Definition 3 (Least element)** Suppose that 𝐷 is a poset and that 𝑆 is a subset of 𝐷.
An element 𝑑 ∈ 𝑆 is the least element of 𝑆 if it satisfies

∀𝑥 ∈ 𝑆. 𝑑 ⊑ 𝑥.

If it exists, it is unique (by antisymmetry), and is written ⊥_𝑆, or simply ⊥.
-/

variable {D : Type u} [PartialOrder D] [OrderBot D]

#check (fun d => bot_le (a := d) : ∀ (d : D), ⊥ ≤ d)

#print OrderBot
#print Bot

/-!
Beware: a poset may not have a least element! For example, ℤ with its usual partial
order does not have a least element.
-/

-- Example: ℤ does not have a bottom element (no OrderBot instance)
-- #check (inferInstance : OrderBot ℤ)  -- This would fail!

end LeastElements

/-!
**Definition 4 (Fixed point)** A fixed point for a function 𝑓 : 𝐷 → 𝐷 is an element
𝑑 ∈ 𝐷 satisfying 𝑓(𝑑) = 𝑑.

However, when 𝐷 is a poset, we can consider the weaker notion of pre-fixed point.
-/

section FixedPoints

variable {D : Type u} [PartialOrder D]

-- Fixed points
def IsFixedPoint (f : D → D) (d : D) : Prop :=
  f d = d

/-!
**Definition 5 ((Least) pre-fixed point)** Let 𝐷 be a poset and 𝑓 : 𝐷 → 𝐷 be a
function. An element 𝑑 ∈ 𝐷 is a pre-fixed point of 𝑓 if it satisfies 𝑓(𝑑) ⊑ 𝑑.
-/

def IsPreFixedPoint (f : D → D) (d : D) : Prop :=
  f d ≤ d

#check (IsPreFixedPoint : (D → D) → D → Prop)

/-!
The least pre-fixed point of 𝑓, if it exists, will be written

fix(𝑓)

It is thus (uniquely) specified by the two properties:

𝑓(fix(𝑓)) ⊑ fix(𝑓)                                (lfp-fix)
∀𝑑 ∈ 𝐷. 𝑓(𝑑) ⊑ 𝑑 ⇒ fix(𝑓) ⊑ 𝑑                    (lfp-least)
-/

def IsLeastPreFixedPoint (f : D → D) (d : D) : Prop :=
  IsPreFixedPoint f d ∧ ∀ d', IsPreFixedPoint f d' → d ≤ d'

/-!
**Proposition 1 (Least pre-fixed points are least fixed points)** Suppose 𝐷 is a poset
and 𝑓 : 𝐷 → 𝐷 is a function possessing a least pre-fixed point, fix(𝑓). Provided 𝑓 is
monotone, fix(𝑓) is in particular a fixed point for 𝑓, and hence is the least element of
the set of fixed points for 𝑓, since every fixed point is a pre-fixed point.
-/

theorem least_prefixed_is_fixed (f : D → D)
    (hf : Monotone f) (d : D) (hd : IsLeastPreFixedPoint f d) :
    IsFixedPoint f d := by
  obtain ⟨h_pre, h_least⟩ := hd
  -- By definition, d is a pre-fixed point
  have h1 : f d ≤ d := h_pre
  -- By monotony of f, we can apply f to both sides
  have h2 : f (f d) ≤ f d := hf h1
  -- Then applying property (lfp-least) with d' = f d
  have h3 : d ≤ f d := h_least (f d) h2
  -- Combining with antisymmetry
  exact le_antisymm h1 h3

/-!
Proof. By definition, fix(𝑓) is a pre-fixed point. Thus, by monotony of 𝑓, we can
apply 𝑓 to both sides of (lfp1) to conclude that

𝑓(𝑓(fix(𝑓))) ⊑ 𝑓(fix(𝑓)).

Then applying property (lfp2) with 𝑑 = 𝑓(fix(𝑓)), we get that

fix(𝑓) ⊑ 𝑓(fix(𝑓)).

Combining this with (lfp1) and the anti-symmetry property of the partial order ⊑, we
get 𝑓(fix(𝑓)) = fix(𝑓), as required.

Thus, while being a pre-fixed point is a weaker notion, being the least pre-fixed point
is stronger than being the least fixed point.
-/

end FixedPoints

/-!
## 2.3  Least upper bounds
-/

section LeastUpperBounds

/-!
**Definition 6 (Least upper bound of a chain)** A countable, increasing chain in a poset
𝐷 is a sequence (𝑑ᵢ)ᵢ∈ℕ of elements of 𝐷 satisfying

𝑑₀ ⊑ 𝑑₁ ⊑ 𝑑₂ ⊑ …

An upper bound for the chain is any 𝑑 ∈ 𝐷 satisfying ∀𝑛 ∈ ℕ. 𝑑ₙ ⊑ 𝑑. If it exists, the
least upper bound, or lub, of the chain will be written as ⨆_{n≥0} 𝑑ₙ. Thus, by definition:

• ∀𝑚 ∈ ℕ. 𝑑ₘ ⊑ ⨆_{n≥0} 𝑑ₙ.
• For any 𝑑 ∈ 𝐷, if ∀𝑚 ∈ ℕ. 𝑑ₘ ⊑ 𝑑, then ⨆_{n≥0} 𝑑ₙ ⊑ 𝑑.
-/

variable {D : Type u} [OmegaCompletePartialOrder D]

#check (OmegaCompletePartialOrder.Chain D : Type u)
#check (OmegaCompletePartialOrder.ωSup : OmegaCompletePartialOrder.Chain D → D)

variable (c : OmegaCompletePartialOrder.Chain D)

#check (OmegaCompletePartialOrder.le_ωSup c : ∀ (i : ℕ), c i ≤ OmegaCompletePartialOrder.ωSup c)

variable (x : D)

#check (OmegaCompletePartialOrder.ωSup_le c x :
  (∀ (i : ℕ), c i ≤ x) → OmegaCompletePartialOrder.ωSup c ≤ x)

/-!
**Remark 1**

(i) We will not need to consider uncountable, or decreasing chains in a poset: so a
'chain' will always mean a countable, increasing chain.

(ii) We will also not need to consider least upper bounds of general sets rather than
chains – but most of what we do here generalizes smoothly.

(iii) While the least element of 𝑆 is an element of 𝑆, the lub of a chain is not
necessarily an element of the chain (and, in fact, the interesting case is when it is
not).

(iv) Like the least element of a set, the lub of a chain is unique if it exists. (It does
not have to exist: for example the chain 0 ≤ 1 ≤ 2 ≤ … in ℕ has no upper
bound, hence no lub.)

(v) A least upper bound is sometimes called a supremum. Some other common
notations for ⨆_{n≥0} 𝑑ₙ are:

⨆_{n=0}^∞ 𝑑ₙ    and    ⨆{𝑑ₙ | 𝑛 ≥ 0}.

The latter can be used more generally with any set: ⨆ 𝑆 is the lub of 𝑆.
-/

/-!
We can already spell out some easy properties of lubs.
-/

/-!
**Proposition 2 (Monotonicity of lubs)** For every pair of chains

𝑑₀ ⊑ 𝑑₁ ⊑ … ⊑ 𝑑ₙ ⊑ …    and    𝑒₀ ⊑ 𝑒₁ ⊑ … ⊑ 𝑒ₙ ⊑ …

if 𝑑ₙ ⊑ 𝑒ₙ for all 𝑛 ∈ ℕ then ⨆_n 𝑑ₙ ⊑ ⨆_n 𝑒ₙ, provided they exist.
-/

-- This follows from the universal property of lub
example
    (c₁ c₂ : OmegaCompletePartialOrder.Chain D)
    (h : ∀ n, c₁ n ≤ c₂ n) :
    OmegaCompletePartialOrder.ωSup c₁ ≤ OmegaCompletePartialOrder.ωSup c₂ :=
  OmegaCompletePartialOrder.ωSup_le c₁ (OmegaCompletePartialOrder.ωSup c₂) fun n =>
    le_trans (h n) (OmegaCompletePartialOrder.le_ωSup c₂ n)

/-!
**Proposition 3 (Discarding elements)** If we discard any finite number of elements at
the beginning of a chain, we do not affect its set of upper bounds and hence do not
change its lub. That is, for any 𝑁 ∈ ℕ we have (provided any of the two exists):

⨆_{n≥0} 𝑑ₙ = ⨆_{n≥0} 𝑑_{N+n}.
-/

/-!
**Proposition 4 (Eventually constant chain)** The elements of a chain do not
necessarily have to be distinct. In particular, we say that a chain 𝑑₀ ⊑ 𝑑₁ ⊑ 𝑑₂ ⊑ … is
eventually constant if for some 𝑁 ∈ ℕ it is the case that ∀𝑛 ≥ 𝑁. 𝑑ₙ = 𝑑_N. For such a
chain, we have ⨆_{n≥0} 𝑑ₙ = 𝑑_N.
-/

/-!
**Proposition 5 (Diagonalisation)** Let 𝐷 be a poset. Suppose that the doubly-indexed
family of elements 𝑑_{m,n} ∈ 𝐷 (𝑚, 𝑛 ≥ 0) satisfies

𝑚 ≤ 𝑚′ ∧ 𝑛 ≤ 𝑛′ ⇒ 𝑑_{m,n} ⊑ 𝑑_{m′,n′}.        (†)

Then, assuming they exist, the lubs form two chains

⨆_{n≥0} 𝑑_{0,n} ⊑ ⨆_{n≥0} 𝑑_{1,n} ⊑ ⨆_{n≥0} 𝑑_{2,n} ⊑ …

and

⨆_{m≥0} 𝑑_{m,0} ⊑ ⨆_{m≥0} 𝑑_{m,1} ⊑ ⨆_{m≥0} 𝑑_{m,2} ⊑ …

Moreover, again assuming the lubs of these chains exist,

⨆_{m≥0} (⨆_{n≥0} 𝑑_{m,n}) = ⨆_{k≥0} 𝑑_{k,k} = ⨆_{n≥0} (⨆_{m≥0} 𝑑_{m,n}).
-/

/-!
Proof. First note that if 𝑚 ≤ 𝑚′ then

𝑑_{m,n} ⊑ 𝑑_{m′,n}                   by property (†) of the 𝑑_{m,n}
       ⊑ ⨆_{n′≥0} 𝑑_{m′,n′}           because the lub is an upper bound

for all 𝑛 ≥ 0, hence, by minimality of the lub, ⨆_{n≥0} 𝑑_{m,n} ⊑ ⨆_{n′≥0} 𝑑_{m′,n′}.
Thus, we do indeed get a chain of lubs

⨆_{n≥0} 𝑑_{0,n} ⊑ ⨆_{n≥0} 𝑑_{1,n} ⊑ ⨆_{n≥0} 𝑑_{2,n} ⊑ …

Using the bound property twice we have

𝑑_{k,k} ⊑ ⨆_{n≥0} 𝑑_{k,n} ⊑ ⨆_{m≥0} ⨆_{n≥0} 𝑑_{m,n}

for each 𝑘 ≥ 0, and so by minimality of the lub,

⨆_{k≥0} 𝑑_{k,k} ⊑ ⨆_{m≥0} ⨆_{n≥0} 𝑑_{m,n}.        (4)

Conversely, for each 𝑚, 𝑛 ≥ 0, note that

𝑑_{m,n} ⊑ 𝑑_{max(m,n),max(m,n)}    by property (†)
       ⊑ ⨆_{k≥0} 𝑑_{k,k}            because the lub is an upper bound

and hence applying minimality of the lub twice we have

⨆_{m≥0} ⨆_{n≥0} 𝑑_{m,n} ⊑ ⨆_{k≥0} 𝑑_{k,k}.        (5)

Combining (4) and (5) with the anti-symmetry property of ⊑ yields the desired
equality. We obtain the additional equality by the same argument but interchanging the
roles of 𝑚 and 𝑛.
-/

end LeastUpperBounds

/-!
## 2.4  Complete partial orders and domains

In this course, we will be interested in certain posets, called chain complete posets and
domains, which enjoy completeness properties: every chain has a least upper bound.
-/

section CPOsAndDomains

/-!
**Definition 7 (Cpos)** A chain complete poset, or cpo, is a poset (𝐷, ⊑) where all
chains have a least upper bound.
-/

#print OmegaCompletePartialOrder

/-!
In a cpo, we only need to verify that a sequence of elements forms a chain to know it
has a lub, so e.g. in Proposition 5 above we automatically know that all the lubs exist.
-/

/-!
**Definition 8 (Domain)** A domain is a cpo that possesses a least element.
-/

-- A domain in Lean is a type with both OmegaCompletePartialOrder and OrderBot
class Domain (α : Type*) extends OmegaCompletePartialOrder α, OrderBot α

/-!
It should be noted that the term 'domain' is used rather loosely in the literature
on denotational semantics: there are many kinds of domains, enjoying various extra
order-theoretic properties over and above the rather minimal ones of chain-completeness
and possession of a least element that we need for this course. Still, most of what we
will do here carries over directly to these other settings.
-/

/-!
**Example 4 (Domain of partial functions)** The poset (𝑋 ⇀ 𝑌) of partial functions
from a set 𝑋 to a set 𝑌, as defined in Example 1 can be made into a domain.

Least element: ⊥ is the totally undefined function.

Lub of a chain: 𝑓₀ ⊑ 𝑓₁ ⊑ 𝑓₂ ⊑ … has lub 𝑓 such that

𝑓(𝑥) = { 𝑓ₙ(𝑥)    if 𝑥 ∈ dom(𝑓ₙ) for some 𝑛
       { undefined otherwise

Note that this definition of the lub is well-defined only if the 𝑓ₙ form a chain. Indeed,
this implies that the 𝑓ₙ agree where they are defined, and so the definition is
unambiguous. We leave it as an exercise to check that this 𝑓 is indeed the least upper
bound of 𝑓₀ ⊑ 𝑓₁ ⊑ 𝑓₂ ⊑ … in the poset (𝑋 ⇀ 𝑌, ⊑).

It was this domain for the case 𝑋 = 𝑌 = State that we used for the denotation of
commands in Section 1.1.
-/

/-!
**Example 5 (Finite cpos)** Any poset (𝐷, ⊑) whose underlying set 𝐷 is finite is a cpo.
For in such a poset any chain is eventually constant, and we noted in Proposition 4
that such a chain always possesses a lub. Of course, a finite poset need not have a
least element, and hence need not be a domain—for example, consider the poset with
Hasse diagram

       •
      ↗ ↖
    •     •

(A Hasse diagram for a poset (𝐷, ⊑) is a directed graph 𝐺 with 𝐷 as vertices, such that
𝑥 ⊑ 𝑦 iff there is a path in 𝐺 from 𝑥 to 𝑦. Equivalently, ⊑ is the reflexive, transitive
closure of the (oriented) adjacency relation of 𝐺, where 𝑥 is adjacent to 𝑦 if there is
an edge from 𝑥 to 𝑦.)
-/

/-!
**Example 6 (Flat natural numbers)** The flat natural numbers ℕ_⊥ is the poset given
by the following Hasse diagram:

    0   1   2  ⋯  𝑛  𝑛+1  ⋯
     ↖  ↑  ↗ ⋯  ↑   ↗  ⋯
         ⊥

A partial function 𝑋 ⇀ ℕ is the same as a monotone function from the poset (𝑋, =)
(equality is a trivial pre-order) to (ℕ_⊥, ⊑). Thus, flat natural numbers give us a way to
express partiality, which we will use further in this course.
-/

#print WithBot

example : (WithBot ℕ) := ⊥
example : (WithBot ℕ) := (5 : ℕ)

/-!
**Example 7 (Non-example: natural numbers)** The set of natural numbers ℕ equipped
with the usual partial order, ≤, is not a cpo. For the increasing chain 0 ≤ 1 ≤ 2 ≤ …
has no upper bound in ℕ.
-/

/-!
**Example 8 ('Vertical' extended natural numbers)** The set 𝜔 + 1, given by the
following Hasse diagram, is a domain.

         ω
         ↑
       𝑛 + 1
         ↑
         𝑛
         ⋮
         1
         ↑
         0
-/

#print WithTop

/-!
**Example 9 (Non-example: no least upper bound)** Consider a modified version of
Example 8, in which we adjoin not one but two different upper bounds to ℕ,
corresponding to the following Hasse diagram:

     ω₁      ω₂
      ↖  ⋮  ↗
        𝑛 + 1
          ↑
          𝑛
          ⋮
          1
          ↑
          0

Then the increasing chain 0 ⊑ 1 ⊑ 2 ⊑ … has two upper bounds (ω₁ and ω₂), but no
least one (since ω₁ ⋢ ω₂ and ω₂ ⋢ ω₁). So this poset is not a cpo.
-/

end CPOsAndDomains

/-!
## 2.5  Continuous functions
-/

section ContinuousFunctions

/-!
**Definition 9 (Continuity)** Given two cpos 𝐷 and 𝐸, a function 𝑓 : 𝐷 → 𝐸 is
continuous if
• it is monotone, and
• it preserves lubs of chains, i.e. for all chains 𝑑₀ ⊑ 𝑑₁ ⊑ … in 𝐷, we have

𝑓(⨆_{n≥0} 𝑑ₙ) = ⨆_{n≥0} 𝑓(𝑑ₙ)
-/

variable {D : Type u} {E : Type v} [OmegaCompletePartialOrder D] [OmegaCompletePartialOrder E]
variable (f : D → E) (c : OmegaCompletePartialOrder.Chain D)

#check (fun f : D → E => ∀ c : OmegaCompletePartialOrder.Chain D,
  f (OmegaCompletePartialOrder.ωSup c) = OmegaCompletePartialOrder.ωSup {
    toFun := f ∘ c
    monotone' := by sorry
  })

/-!
**Definition 10 (Strictness)** Let 𝐷 and 𝐸 be two posets with least elements ⊥_𝐷 and
⊥_𝐸. A function 𝑓 is strict if 𝑓(⊥_𝐷) = ⊥_𝐸.
-/

variable {D : Type u} {E : Type v} [Preorder D] [Preorder E] [OrderBot D] [OrderBot E]

def IsStrict (f : D → E) : Prop :=
  f ⊥ = ⊥

/-!
**Remark 2** Note that if 𝑓 : 𝐷 → 𝐸 is monotone and 𝑑₀ ⊑ 𝑑₁ ⊑ 𝑑₂ ⊑ … is a chain in 𝐷,
then applying 𝑓 we get a chain 𝑓(𝑑₀) ⊑ 𝑓(𝑑₁) ⊑ 𝑓(𝑑₂) ⊑ … in 𝐸. Moreover, if 𝑑 is an
upper bound of the first chain, then 𝑓(𝑑) is an upper bound of the second and hence
is greater than its lub. Hence, if 𝑓 : 𝐷 → 𝐸 is a monotone function between cpos, we
always have

⨆_{n≥0} 𝑓(𝑑ₙ) ⊑ 𝑓(⨆_{n≥0} 𝑑ₙ)

Therefore (using the antisymmetry property of ⊑), to check that a monotone function
𝑓 between cpos is continuous, it suffices to check for each chain 𝑑₀ ⊑ 𝑑₁ ⊑ 𝑑₂ ⊑ … in 𝐷
that

𝑓(⨆_{n≥0} 𝑑ₙ) ⊑ ⨆_{n≥0} 𝑓(𝑑ₙ)

holds in 𝐸.
-/

/-!
**Example 10 (Constant functions)** Given cpos 𝐷 and 𝐸, for each 𝑒 ∈ 𝐸 the constant
function 𝐷 → 𝐸 with value 𝑒, λ𝑑 ∈ 𝐷. 𝑒, is continuous.
-/

/-!
**Example 11** When 𝐷 is the domain of partial functions (State ⇀ State), the function
𝐹_{b,c} : 𝐷 → 𝐷 defined in Section 1.2 connection with the denotational semantics of
while-loops is a continuous function. We leave the verification of this as an exercise.
-/

/-!
**Example 12 (Non-example)** Let Ω be the domain of vertical natural numbers, as
defined in Example 8. Then the function 𝑓 : Ω → Ω defined by

{ 𝑓(𝑛) = 0    (𝑛 ∈ ℕ)
{ 𝑓(𝜔) = 𝜔.

is monotone and strict, but it is not continuous because

𝑓(⨆_{n≥0} 𝑛) = 𝑓(𝜔) = 𝜔 ≠ 0 = ⨆_{n≥0} 0 = ⨆_{n≥0} 𝑓(𝑛).
-/

end ContinuousFunctions

/-!
## 2.6  Kleene's fixed point theorem

We now reach the key result about continuous functions on domains which permits
us to give denotational semantics of programs involving recursive features.

Define 𝑓ⁿ(𝑥) as follows:

{ 𝑓⁰(𝑥)    def= 𝑥
{ 𝑓ⁿ⁺¹(𝑥) def= 𝑓(𝑓ⁿ(𝑥)).

Since ∀𝑑 ∈ 𝐷. ⊥ ⊑ 𝑑, one has 𝑓⁰(⊥) = ⊥ ⊑ 𝑓¹(⊥); and by monotonicity of 𝑓

𝑓ⁿ(⊥) ⊑ 𝑓ⁿ⁺¹(⊥) ⇒ 𝑓ⁿ⁺¹(⊥) = 𝑓(𝑓ⁿ(⊥)) ⊑ 𝑓(𝑓ⁿ⁺¹(⊥)) = 𝑓ⁿ⁺²(⊥).

Therefore, by induction on 𝑛 ∈ ℕ, the elements 𝑓ⁿ(⊥) form a chain in 𝐷:

𝑓⁰(⊥) ⊑ 𝑓¹(⊥) ⊑ … ⊑ 𝑓ⁿ(⊥) ⊑ 𝑓ⁿ⁺¹(⊥) ⊑ …

So since 𝐷 is a cpo, this chain has a least upper bound.
-/

/-!
**Theorem 6 (Kleene's fixed point theorem)** Let 𝑓 : 𝐷 → 𝐷 be a continuous function
on a domain 𝐷. Then 𝑓 possesses a least pre-fixed point, given by

fix(𝑓) = ⨆_{n≥0} 𝑓ⁿ(⊥).

By Proposition 1, fix(𝑓) is thus also the least fixed point of 𝑓.

This theorem is sometimes attributed (amongst others) to Tarski. Another, different,
fixed point theorem more often attributed to Tarski (or Knaster-Tarski) gives the
existence of fixed point of monotone functions on complete lattices (posets where every
subset has an upper and lower bound).
-/

/-!
Proof. First note that

𝑓(fix(𝑓)) = 𝑓(⨆_{n≥0} 𝑓ⁿ(⊥))
          = ⨆_{n≥0} 𝑓(𝑓ⁿ(⊥))       by continuity of 𝑓
          = ⨆_{n≥0} 𝑓ⁿ⁺¹(⊥)         by definition of 𝑓ⁿ
          = ⨆_{n≥0} 𝑓ⁿ(⊥)           by Proposition 3
          = fix(𝑓).

So fix(𝑓) is a fixed point for 𝑓, and hence in particular a pre-fixed point. To verify
that it is a least pre-fixed point, suppose that 𝑑 ∈ 𝐷 satisfies 𝑓(𝑑) ⊑ 𝑑. Then since ⊥
is least in 𝐷

𝑓⁰(⊥) = ⊥ ⊑ 𝑑

and assuming 𝑓ⁿ(⊥) ⊑ 𝑑, we have

𝑓ⁿ⁺¹(⊥) = 𝑓(𝑓ⁿ(⊥)) ⊑ 𝑓(𝑑)     monotonicity of 𝑓
                    ⊑ 𝑑        by assumption on 𝑑.

Hence by induction on 𝑛 ∈ ℕ we have ∀𝑛 ∈ ℕ. 𝑓ⁿ(⊥) ⊑ 𝑑. Therefore 𝑑 is an upper
bound for the chain and hence lies above the least such, i.e.

fix(𝑓) = ⨆_{n≥0} 𝑓ⁿ(⊥) ⊑ 𝑑.

Since this is the case for every pre-fixed point, fix(𝑓) is indeed the least pre-fixed
point, as claimed.
-/

