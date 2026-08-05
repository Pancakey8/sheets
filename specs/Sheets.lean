import Std.Data.TreeMap
import Std.Data.TreeSet
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Prod.Lex

namespace Sheets

abbrev CellId := Nat ×ₗ Nat

deriving instance Repr for CellId
deriving instance DecidableEq for CellId

inductive Error
| divByZero
| typeMismatch
| cyclic
deriving Repr

inductive Atomic
| number : Float -> Atomic
| string : String -> Atomic
| none : Atomic
| error : Error -> Atomic
deriving Repr

inductive Expr
| atom : Atomic -> Expr
| ref : CellId -> Expr
| add : Expr -> Expr -> Expr
| sub : Expr -> Expr -> Expr
| mult : Expr -> Expr -> Expr
| div : Expr -> Expr -> Expr
deriving Repr

instance : Zero Expr where
  zero := .atom (.string "")

structure Grid where
  cells : Std.TreeMap CellId Expr
deriving Repr

def Grid.nil : Grid := ⟨∅⟩

def Grid.set (grid : Grid) (cell : CellId) (ex : Expr) : Grid :=
  ⟨grid.cells.insert cell ex⟩

def Grid.delete (grid : Grid) (cell : CellId) : Grid :=
  ⟨grid.cells.erase cell⟩

def dummy : Grid :=
  Grid.nil
  |>.set ⟨1, 2⟩ (.atom (.number 3.5))
  |>.set ⟨1, 3⟩ (.atom (.number 7))
  |>.set ⟨2, 2⟩ (.add (.ref ⟨1, 2⟩) (.ref ⟨1, 3⟩))
  |>.set ⟨3, 1⟩ (.ref ⟨3, 2⟩)
  |>.set ⟨3, 2⟩ (.ref ⟨3, 3⟩)
  |>.set ⟨3, 3⟩ (.ref ⟨3, 1⟩)

#eval dummy

def Expr.deps : Expr -> Std.TreeSet CellId
| .atom _ => ∅
| .ref id => {id}
| .add x y | .sub x y | .mult x y | .div x y =>
  x.deps ∪ y.deps

def Atomic.numValue : Atomic -> Option Float
| .number x => .some x
| .none => .some 0
| _ => .none

def Atomic.binOp (f : Float -> Float -> Atomic) (a b : Atomic) : Atomic :=
  match a, b with
  | .error e, _ => .error e
  | _, .error e => .error e
  | _, _ =>
    match a.numValue, b.numValue with
    | .some x, .some y => f x y
    | _, _ => .error .typeMismatch

def Atomic.add (a b : Atomic) : Atomic := a.binOp (fun x y => .number (x + y)) b

def Atomic.sub (a b : Atomic) : Atomic := a.binOp (fun x y => .number (x - y)) b

def Atomic.mult (a b : Atomic) : Atomic := a.binOp (fun x y => .number (x * y)) b

def Atomic.div (a b : Atomic) : Atomic :=
  a.binOp (fun x y => if y == 0 then .error .divByZero else .number (x / y)) b

structure Context where
  vals : Std.TreeMap CellId Atomic
deriving Repr

def Expr.evalWith (ctx : Context) : Expr -> Atomic
| .atom a => a
| .ref id => ctx.vals.getD id (.error .cyclic)
| .add x y => (x.evalWith ctx).add (y.evalWith ctx)
| .sub x y => (x.evalWith ctx).sub (y.evalWith ctx)
| .mult x y => (x.evalWith ctx).mult (y.evalWith ctx)
| .div x y => (x.evalWith ctx).div (y.evalWith ctx)

def foo : Expr := .add (.ref ⟨2, 1⟩) (.mult (.ref ⟨2, 2⟩) (.atom $ .number 3.5))

def Expr.isFree (ex : Expr) (ctx : Context) : Bool :=
  ex.deps.all λ id => id ∈ ctx.vals

structure Evaluation where
  ctx : Context
  remain : Std.TreeMap CellId Expr
deriving Repr

def Evaluation.findFree? (ev : Evaluation) : Option CellId :=
  (ev.remain.filter λ _ ex => ex.isFree ev.ctx).minKey?

theorem Evaluation.findFree?_mem_some
    {ev : Evaluation} {c : CellId}
    (h : ev.findFree? = .some c) :
    c ∈ ev.remain := by
  simp [Evaluation.findFree?] at h
  have h_mem :
      c ∈ (Std.TreeMap.filter
        (λ x ex => ex.isFree ev.ctx) ev.remain) :=
    Std.TreeMap.contains_minKey? h
  exact Std.TreeMap.mem_of_mem_filter h_mem

#eval Evaluation.mk ⟨∅⟩ dummy.cells |>.findFree?

def Evaluation.computeOne (ev : Evaluation) : Option (CellId × Atomic) :=
  match h : ev.findFree? with
  | .some id =>
    .some (
      id,
      (ev.remain.get id (Evaluation.findFree?_mem_some h)).evalWith ev.ctx
    )
  | .none =>
    match ev.remain.minKey? with
    | .some id => .some (id, .error .cyclic)
    | .none => .none

#check Std.TreeMap.equiv_iff_toList_eq
#check Std.TreeMap.equiv_of_beq

theorem Evaluation.computeOne_mem_some
    {ev : Evaluation} {c : CellId × Atomic}
    (h : ev.computeOne = .some c) : c.1 ∈ ev.remain := by
  simp [Evaluation.computeOne] at h
  split at h
  . rename_i id h_id
    injection h with h_eq
    rw [← h_eq]
    exact Evaluation.findFree?_mem_some h_id
  . rename_i h_none
    split at h
    . rename_i x id h_id
      injection h with h_eq
      rw [← h_eq]
      exact Std.TreeMap.contains_minKey? h_id
    . contradiction

def Evaluation.step (ev : Evaluation) (comp : CellId × Atomic) : Evaluation :=
  ⟨⟨ev.ctx.vals.insert comp.1 comp.2⟩, ev.remain.erase comp.1⟩

def Evaluation.DomainHas (ev : Evaluation) (c : CellId) : Prop :=
  c ∈ ev.ctx.vals ∨ c ∈ ev.remain

theorem Evaluation.domain_step
    {ev : Evaluation} {c : CellId × Atomic}
    (h_mem : c.1 ∈ ev.remain) :
    ∀ x, ev.DomainHas x ↔ (ev.step c).DomainHas x := by
  intro x
  dsimp [Evaluation.DomainHas, Evaluation.step]
  rw [Std.TreeMap.mem_insert, Std.TreeMap.mem_erase]
  by_cases hx : x = c.1
  . subst hx
    simp [h_mem]
  . have : compare c.1 x ≠ Ordering.eq := by
      intro h_eq
      have h_eq' : c.1 = x := compare_eq_iff_eq.mp h_eq
      exact hx h_eq'.symm
    simp [this]

def Evaluation.DisjointKeys (ev : Evaluation) : Prop :=
  ∀ x, ¬(x ∈ ev.ctx.vals ∧ x ∈ ev.remain)

theorem Evaluation.disjoint_step
    {ev : Evaluation} {c : CellId × Atomic}
    (h_disj : ev.DisjointKeys) :
    (ev.step c).DisjointKeys := by
  intro x ⟨h_ctx, h_rem⟩
  dsimp [Evaluation.step] at h_ctx h_rem
  rw [Std.TreeMap.mem_insert] at h_ctx
  rw [Std.TreeMap.mem_erase] at h_rem
  rcases h_ctx with h_eq | hx_mem
  . rw [ne_eq] at h_rem
    exact h_rem.1 h_eq
  . have := (h_disj x)
    simp [hx_mem] at this
    exact this h_rem.2

theorem size_gt_zero_if_mem
    {inst : Ord α} [Std.TransCmp inst.compare]
    (map : Std.TreeMap α β) :
    x ∈ map → 0 < map.size := by
  intro h_mem
  by_contra h_zero
  simp at h_zero
  have h_empty : map.isEmpty = true := by
    rw [Std.TreeMap.isEmpty_eq_size_eq_zero]
    simp [h_zero]
  have h_not_mem : ¬x ∈ map := Std.TreeMap.not_mem_of_isEmpty h_empty
  exact absurd h_mem h_not_mem

theorem empty_iff_isEmpty
    {inst : Ord α} [Std.TransCmp inst.compare]
    (map : Std.TreeMap α β) :
    map = ∅ ↔ map.isEmpty = true := by
  constructor
  · rintro rfl
    rfl
  · intro h
    rcases map with ⟨⟨tree, _⟩⟩
    cases tree with
    | leaf => rfl
    | inner => contradiction

def Evaluation.resolveAll (ev : Evaluation) : Evaluation :=
  match h : ev.computeOne with
  | none => ev
  | some c =>
    ev.step c |>.resolveAll
termination_by ev.remain.size
decreasing_by
  dsimp [Evaluation.step]
  have h_mem := Evaluation.computeOne_mem_some h
  rw [Std.TreeMap.size_erase]
  simp [h_mem]
  have h_pos := size_gt_zero_if_mem ev.remain h_mem
  exact Nat.sub_one_lt_of_lt h_pos

theorem Evaluation.domain_resolveAll (ev : Evaluation) :
    ∀ x, ev.DomainHas x ↔ ev.resolveAll.DomainHas x := by
  intro x
  unfold Evaluation.resolveAll
  cases hc : ev.computeOne with
  | none => rfl
  | some c =>
    have h_mem := Evaluation.computeOne_mem_some hc
    have h_step := Evaluation.domain_step h_mem x
    have h_ih := Evaluation.domain_resolveAll (ev.step c) x
    exact h_step.trans h_ih
termination_by ev.remain.size
decreasing_by
  dsimp [Evaluation.step]
  have h_mem := Evaluation.computeOne_mem_some hc
  rw [Std.TreeMap.size_erase]
  simp [h_mem]
  have h_pos := size_gt_zero_if_mem ev.remain h_mem
  exact Nat.sub_one_lt_of_lt h_pos

theorem Evaluation.disjoint_resolveAll
    (ev : Evaluation) (h_disj : ev.DisjointKeys) :
    ev.resolveAll.DisjointKeys := by
  unfold Evaluation.resolveAll
  cases hc : ev.computeOne with
  | some c =>
    have h_ih := Evaluation.disjoint_resolveAll (ev.step c) (ev.disjoint_step h_disj)
    simp [h_ih]
  | none => simp [h_disj]
termination_by ev.remain.size
decreasing_by
  dsimp [Evaluation.step]
  have h_mem := Evaluation.computeOne_mem_some hc
  rw [Std.TreeMap.size_erase]
  simp [h_mem]
  have h_pos := size_gt_zero_if_mem ev.remain h_mem
  exact Nat.sub_one_lt_of_lt h_pos

theorem Evaluation.resolveAll_remain_empty (ev : Evaluation) :
    ev.resolveAll.remain = ∅ := by
  unfold Evaluation.resolveAll
  cases hc : ev.computeOne with
  | none =>
    dsimp [Evaluation.computeOne] at hc
    split at hc
    · contradiction
    · rename_i h_none
      split at hc
      · contradiction
      · rename_i h_min
        have h_empty := Std.TreeMap.minKey?_eq_none_iff.mp h_min
        simp [empty_iff_isEmpty, h_empty]
  | some c =>
    have h_ih := Evaluation.resolveAll_remain_empty (ev.step c)
    exact h_ih
termination_by ev.remain.size
decreasing_by
  dsimp [Evaluation.step]
  have h_mem := Evaluation.computeOne_mem_some hc
  rw [Std.TreeMap.size_erase]
  simp [h_mem]
  have h_pos := size_gt_zero_if_mem ev.remain h_mem
  exact Nat.sub_one_lt_of_lt h_pos

def Grid.evaluate (grid : Grid) : Grid :=
  Evaluation.mk ⟨∅⟩ grid.cells
  |>.resolveAll
  |>.ctx.vals
  |>.map (λ _ a => Expr.atom a)
  |> Grid.mk

theorem Grid.evaluate_keys (grid : Grid) :
    ∀ x, x ∈ grid.cells ↔ x ∈ grid.evaluate.cells := by
  intro x

  let ev0 : Evaluation := ⟨⟨∅⟩, grid.cells⟩
  have h_disj0 : ev0.DisjointKeys := by
    intro y ⟨h_ctx, _⟩
    dsimp [ev0] at h_ctx
    contradiction

  have h_dom := Evaluation.domain_resolveAll ev0 x
  simp [ev0, Evaluation.DomainHas] at h_dom

  have h_empty := Evaluation.resolveAll_remain_empty ev0
  have h_not_mem_rem : ¬x ∈ ev0.resolveAll.remain := by
    rw [h_empty]
    exact Std.TreeMap.not_mem_emptyc

  simp [h_not_mem_rem, ev0] at h_dom

  dsimp [Grid.evaluate]
  rw [Std.TreeMap.mem_map]
  exact h_dom

#eval Grid.evaluate dummy
