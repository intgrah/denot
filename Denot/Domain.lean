import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Data.PFun

open OmegaCompletePartialOrder

/-! A domain is an ω-complete partial order with a bottom element. -/
class Domain (α : Type*) extends OmegaCompletePartialOrder α, OrderBot α

/-
α →. β is definitionally equal to α → Part β, but typeclass inference
does not unfold most definitions, so we use inferInstanceAs to use
definitional equality instead.
-/

namespace PFun

variable {α β : Type*}

noncomputable instance : OmegaCompletePartialOrder (α →. β) :=
  inferInstanceAs (OmegaCompletePartialOrder (α → Part β))

instance : OrderBot (α →. β) := inferInstanceAs (OrderBot (α → Part β))

noncomputable instance : Domain (α →. β) where

/-!
The ordering on PFun combines:
1. Pi.le_def: (f ≤ g : ∀ a, β a) ↔ ∀ a, f a ≤ g a
2. Part's PartialOrder: (x ≤ y : Part α) ↔ ∀ i, i ∈ x → i ∈ y

So for f g : α →. β:
  f ≤ g ↔ ∀ a, f a ≤ g a
        ↔ ∀ a, ∀ b, b ∈ f a → b ∈ g a
        ↔ ∀ a b, b ∈ f a → b ∈ g a

Since Part α contains at most one element, this means:
  f ≤ g ↔ wherever f is defined, g is defined with the same value
        ↔ dom(f) ⊆ dom(g) and f and g agree on dom(f)
-/
example (f g : α →. β) : f ≤ g ↔ ∀ a b, b ∈ f a → b ∈ g a := by rfl

end PFun

/-!Enable indexed supremum notation `⨆ i, f i` -/
open Classical in
noncomputable instance [Domain α] : SupSet α where
  sSup s := if h : ∃ c : Chain α, Set.range c = s then ωSup (choose h) else ⊥

/-! The indexed supremum of a chain equals ωSup of that chain -/
@[simp]
theorem iSup_chain_eq_ωSup [Domain α] (c : Chain α) : ⨆ i, c i = ωSup c := by
  unfold iSup
  simp only [SupSet.sSup]
  have h : ∃ c' : Chain α, Set.range c' = Set.range c := ⟨c, rfl⟩
  rw [dif_pos h]
  have : IsLUB (Set.range h.choose) (ωSup h.choose) := isLUB_range_ωSup _
  rw [h.choose_spec] at this
  exact this.unique (isLUB_range_ωSup c)

/-!
## Theorems about doubly-indexed chains

For doubly-indexed monotone sequences (which form chains in both dimensions),
we prove commutativity and diagonal properties.
-/

section DoubleChain

variable [Domain α] {d : ℕ → ℕ → α}

/-- Commutativity of lubs -/
theorem ωSup_ωSup_comm
    (h_mono_i : ∀ j, Monotone (fun i => d i j))
    (h_mono_j : ∀ i, Monotone (d i)) :
    ⨆ (i) (j), d i j = ⨆ (j) (i), d i j := by
  -- Build chains for each row and column
  let row_chains : ℕ → Chain α := fun i => ⟨d i, h_mono_j i⟩
  let col_chains : ℕ → Chain α := fun j => ⟨fun i => d i j, h_mono_i j⟩

  -- The chain of row suprema
  have row_mono : Monotone (fun i => ωSup (row_chains i)) := by
    intro i i' hii'
    apply ωSup_le
    intro j
    calc d i j
        ≤ d i' j := h_mono_i j hii'
      _ ≤ ωSup (row_chains i') := le_ωSup (row_chains i') j
  let row_sup_chain : Chain α := ⟨fun i => ωSup (row_chains i), row_mono⟩

  -- The chain of column suprema
  have col_mono : Monotone (fun j => ωSup (col_chains j)) := by
    intro j j' hjj'
    apply ωSup_le
    intro i
    calc d i j
        ≤ d i j' := h_mono_j i hjj'
      _ ≤ ωSup (col_chains j') := le_ωSup (col_chains j') i
  let col_sup_chain : Chain α := ⟨fun j => ωSup (col_chains j), col_mono⟩

  have eq₁ : ⨆ i, ⨆ j, d i j = ωSup row_sup_chain := by
    calc ⨆ i, ⨆ j, d i j
        = ⨆ i, ωSup (row_chains i) := by
          congr 1; funext i; exact iSup_chain_eq_ωSup (row_chains i)
      _ = ωSup row_sup_chain := iSup_chain_eq_ωSup row_sup_chain

  have eq₂ : ⨆ j, ⨆ i, d i j = ωSup col_sup_chain := by
    calc ⨆ j, ⨆ i, d i j
        = ⨆ j, ωSup (col_chains j) := by
          congr 1; funext j; exact iSup_chain_eq_ωSup (col_chains j)
      _ = ωSup col_sup_chain := iSup_chain_eq_ωSup col_sup_chain

  rw [eq₁, eq₂]
  apply le_antisymm
  · show ωSup row_sup_chain ≤ ωSup col_sup_chain
    apply ωSup_le
    intro i
    apply ωSup_le
    intro j
    calc d i j
        ≤ ωSup (col_chains j) := le_ωSup (col_chains j) i
      _ ≤ ωSup col_sup_chain := le_ωSup col_sup_chain j
  · show ωSup col_sup_chain ≤ ωSup row_sup_chain
    apply ωSup_le
    intro j
    apply ωSup_le
    intro i
    calc d i j
        ≤ ωSup (row_chains i) := le_ωSup (row_chains i) j
      _ ≤ ωSup row_sup_chain := le_ωSup row_sup_chain i

/-- Diagonalisation of lubs -/
theorem ωSup_ωSup_eq_ωSup_diag
    (h_mono_i : ∀ j, Monotone (fun i => d i j))
    (h_mono_j : ∀ i, Monotone (d i)) :
    ⨆ (i) (j), d i j = ⨆ i, d i i := by

  let row_chains : ℕ → Chain α := fun i => ⟨d i, h_mono_j i⟩
  have row_mono : Monotone (fun i => ωSup (row_chains i)) := by
    intro i i' hii'
    apply ωSup_le
    intro j
    calc d i j
        ≤ d i' j := h_mono_i j hii'
      _ ≤ ωSup (row_chains i') := le_ωSup (row_chains i') j
  let row_sup_chain : Chain α := ⟨fun i => ωSup (row_chains i), row_mono⟩

  let diag_chain : Chain α := ⟨fun i => d i i, fun i j hij =>
    calc d i i
        ≤ d j i := h_mono_i i hij
      _ ≤ d j j := h_mono_j j hij⟩

  have eq₁ : ⨆ i, ⨆ j, d i j = ωSup row_sup_chain := by
    calc ⨆ i, ⨆ j, d i j
        = ⨆ i, ωSup (row_chains i) := by
          congr 1; funext i; exact iSup_chain_eq_ωSup (row_chains i)
      _ = ωSup row_sup_chain := iSup_chain_eq_ωSup row_sup_chain

  have eq₂ : ⨆ i, d i i = ωSup diag_chain := iSup_chain_eq_ωSup diag_chain

  rw [eq₁, eq₂]
  apply le_antisymm
  · show ωSup row_sup_chain ≤ ωSup diag_chain
    apply ωSup_le
    intro i
    apply ωSup_le
    intro j
    calc d i j
        ≤ d (max i j) j := h_mono_i j (le_max_left i j)
      _ ≤ d (max i j) (max i j) := h_mono_j (max i j) (le_max_right i j)
      _ ≤ ωSup diag_chain := le_ωSup diag_chain (max i j)
  · show ωSup diag_chain ≤ ωSup row_sup_chain
    apply ωSup_le
    intro i
    calc d i i
        ≤ ωSup (row_chains i) := le_ωSup (row_chains i) i
      _ ≤ ωSup row_sup_chain := le_ωSup row_sup_chain i

end DoubleChain
