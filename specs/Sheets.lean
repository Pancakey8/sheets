import Std.Data.TreeMap
import Std.Data.TreeSet
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Prod.Lex

namespace Sheets

abbrev CellId := Nat ×ₗ Nat

deriving instance Repr for CellId
deriving instance DecidableEq for CellId

instance : Std.LawfulEqCmp (α := CellId) compare where
  eq_of_compare := by
    intro a b h
    exact compare_eq_iff_eq.mp h

inductive Error
| divByZero
| typeMismatch
| cyclic
| invalidNumber
deriving Repr, BEq

inductive Atomic
| number : Float -> Atomic
| string : String -> Atomic
| none : Atomic
| error : Error -> Atomic
deriving Repr, BEq

inductive Expr
| atom : Atomic -> Expr
| ref : CellId -> Expr
| add : Expr -> Expr -> Expr
| sub : Expr -> Expr -> Expr
| mult : Expr -> Expr -> Expr
| div : Expr -> Expr -> Expr
deriving Repr, BEq

instance : Zero Expr where
  zero := .atom (.string "")

@[ext]
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

def Atomic.canon : Atomic -> Atomic
| .number x =>
  if x.isNaN then
    .error .invalidNumber
  else
    .number x
| a => a

def Atomic.binOp (f : Float -> Float -> Atomic) (a b : Atomic) : Atomic :=
  match a, b with
  | .error e, _ => .error e
  | _, .error e => .error e
  | _, _ =>
    match a.canon.numValue, b.canon.numValue with
    | .some x, .some y =>
      f x y
    | _, _ => .error .typeMismatch

def Atomic.add (a b : Atomic) : Atomic := a.binOp (λ x y => .number (x + y)) b

def Atomic.sub (a b : Atomic) : Atomic := a.binOp (λ x y => .number (x - y)) b

def Atomic.mult (a b : Atomic) : Atomic := a.binOp (λ x y => .number (x * y)) b

def Atomic.div (a b : Atomic) : Atomic :=
  a.binOp (λ x y => if y == 0 then .error .divByZero else .number (x / y)) b

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
  ex.deps.foldl (init := True) λ acc id => acc ∧ id ∈ ctx.vals

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
      ((ev.remain.get id (Evaluation.findFree?_mem_some h)).evalWith ev.ctx).canon
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

theorem Atomic.canon_idempotent (a : Atomic) : a.canon.canon = a.canon := by
  cases a
  . dsimp [Atomic.canon]
    rename_i x
    cases h : x.isNaN
    . simp [h]
    . rfl
  . rfl
  . rfl
  . rfl

theorem Expr.evalWith_atom (ctx : Context) (a : Atomic) :
    (Expr.atom a).evalWith ctx = a := rfl

theorem Expr.isFree_atom (a : Atomic) (ctx : Context) :
    (Expr.atom a).isFree ctx = true := by
  dsimp [Expr.isFree, Expr.deps]
  rfl

theorem Grid.ext_get? {g1 g2 : Grid} 
    (h : ∀ id, g1.cells.get? id = g2.cells.get? id) : g1 = g2 := by sorry

theorem Grid.evaluate_cells (grid : Grid) (id : CellId) (h_mem : id ∈ grid.cells) :
    ∃ a, grid.evaluate.cells[id]? = Expr.atom a := by
  have h_mem' := (Grid.evaluate_keys ..).mp h_mem
  simp [h_mem']
  dsimp [Grid.evaluate]
  simp [Std.TreeMap.getElem_map (h' := h_mem')]

theorem Evaluation.computeOne_snd_canon
    {ev : Evaluation} {c : CellId × Atomic}
    (hc : ev.computeOne = some c) : c.2 = c.2.canon := by
  dsimp [Evaluation.computeOne] at hc
  split at hc
  · rename_i id h_id
    injection hc with h_eq
    rw [← h_eq]
    dsimp
    exact (Atomic.canon_idempotent _).symm
  · rename_i h_none
    split at hc
    · rename_i x id h_id
      injection hc with h_eq
      rw [← h_eq]
      rfl
    · contradiction

theorem Evaluation.resolveAll_vals_canon
    (ev : Evaluation)
    (h_canon : ∀ id a, ev.ctx.vals.get? id = some a → a = a.canon) :
    ∀ id a, ev.resolveAll.ctx.vals.get? id = some a → a = a.canon := by
  unfold Evaluation.resolveAll
  cases hc : ev.computeOne with
  | none =>
    intro id a ha
    exact h_canon id a ha
  | some c =>
    have h_mem := Evaluation.computeOne_mem_some hc
    have h_canon' :
        ∀ id a, (ev.step c).ctx.vals.get? id = some a → a = a.canon := by
      intro id a ha
      dsimp [Evaluation.step] at ha
      rw [Std.TreeMap.getElem?_insert] at ha
      by_cases h : id = c.1
      . subst h
        simp at ha
        subst ha -- Here
        exact Evaluation.computeOne_snd_canon hc
      . have h' : ¬compare c.1 id = Ordering.eq := by
           simp
           exact mt Eq.symm h
        simp [h'] at ha
        exact h_canon id a ha

    exact Evaluation.resolveAll_vals_canon (ev.step c) h_canon'
termination_by ev.remain.size
decreasing_by
  dsimp [Evaluation.step]
  rw [Std.TreeMap.size_erase]
  simp [h_mem]
  have h_pos := size_gt_zero_if_mem ev.remain h_mem
  exact Nat.sub_one_lt_of_lt h_pos

theorem Evaluation.resolveAll_ctx_get?
    (ev : Evaluation) (id : CellId) (v : Atomic)
    (h_not_rem : id ∉ ev.remain)
    (h_ctx : ev.ctx.vals.get? id = some v) :
    ev.resolveAll.ctx.vals.get? id = some v := by
  unfold Evaluation.resolveAll
  cases hc : ev.computeOne with
  | none => exact h_ctx
  | some c =>
    have h_mem := Evaluation.computeOne_mem_some hc
    have h_ne : c.1 ≠ id := by
      rintro rfl
      exact h_not_rem h_mem
    have h_not_rem' : id ∉ (ev.step c).remain := by
      dsimp [Evaluation.step]
      rw [Std.TreeMap.mem_erase]
      intro h
      exact h_not_rem h.2
    have h_ctx' : (ev.step c).ctx.vals.get? id = some v := by
      dsimp [Evaluation.step]
      rw [Std.TreeMap.getElem?_insert]
      have h_cmp : compare c.1 id ≠ Ordering.eq := by
        intro h_eq
        exact h_ne (compare_eq_iff_eq.mp h_eq)
      simp [h_cmp]
      exact h_ctx
    exact Evaluation.resolveAll_ctx_get? (ev.step c) id v h_not_rem' h_ctx'
termination_by ev.remain.size
decreasing_by
  dsimp [Evaluation.step]
  have h_mem := Evaluation.computeOne_mem_some hc
  rw [Std.TreeMap.size_erase]
  simp [h_mem]
  have h_pos := size_gt_zero_if_mem ev.remain h_mem
  exact Nat.sub_one_lt_of_lt h_pos

theorem Evaluation.resolveAll_ctx_vals_get?
    (ev : Evaluation) (h_disj : ev.DisjointKeys) (id : CellId) (a : Atomic)
    (h_ctx : ev.ctx.vals.get? id = some a) :
    ev.resolveAll.ctx.vals.get? id = some a := by
  unfold Evaluation.resolveAll
  cases hc : ev.computeOne with
  | none => exact h_ctx
  | some c =>
    have h_mem := Evaluation.computeOne_mem_some hc
    have h_step : (ev.step c).ctx.vals.get? id = some a := by
      dsimp [Evaluation.step]
      rw [Std.TreeMap.getElem?_insert]
      by_cases h : id = c.1
      · subst h
        simp
        obtain ⟨h_ctx_mem, h_eq⟩ := Std.TreeMap.getElem?_eq_some_iff.mp h_ctx
        have h_absurd := h_disj c.1 ⟨h_ctx_mem, h_mem⟩
        contradiction
      · have h_cmp : compare c.1 id ≠ Ordering.eq := by
          simp_all only [Std.TreeMap.get?_eq_getElem?, ne_eq, Std.LawfulEqCmp.compare_eq_iff_eq]
          obtain ⟨fst, snd⟩ := c
          simp_all only
          apply Aesop.BuiltinRules.not_intro
          intro a_1
          subst a_1
          simp_all only [not_true_eq_false]
        simp [h_cmp]
        exact h_ctx
    exact Evaluation.resolveAll_ctx_vals_get? (ev.step c) (ev.disjoint_step h_disj) id a h_step
termination_by ev.remain.size
decreasing_by
  dsimp [Evaluation.step]
  have h_mem := Evaluation.computeOne_mem_some hc
  rw [Std.TreeMap.size_erase]
  simp [h_mem]
  have h_pos := size_gt_zero_if_mem ev.remain h_mem
  exact Nat.sub_one_lt_of_lt h_pos

theorem Evaluation.resolveAll_get?_atom
    (ev : Evaluation) (h_disj : DisjointKeys ev) (id : CellId) (a : Atomic)
    (h_rem : ev.remain.get? id = some (Expr.atom a)) :
    ev.resolveAll.ctx.vals.get? id = some a.canon := by
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
        obtain ⟨h_mem, _⟩ := Std.TreeMap.getElem?_eq_some_iff.mp h_rem
        have h_not := Std.TreeMap.not_mem_of_isEmpty (a := id) h_empty
        exact absurd h_mem h_not
  | some c =>
    by_cases h_eq : c.1 = id
    · subst h_eq
      have h_c2 : c.2 = a.canon := by
        dsimp [Evaluation.computeOne] at hc
        split at hc
        · rename_i id_free h_free
          injection hc with h_tuple
          rw [← h_tuple]
          dsimp
          have : id_free = c.1 := by
            subst h_tuple
            rfl
          subst this
          obtain ⟨h_mem, h_elem⟩ := Std.TreeMap.getElem?_eq_some_iff.mp h_rem
          rw [h_elem, Expr.evalWith_atom]
        · rename_i h_none
          split at hc
          · rename_i x id_min h_min
            injection hc with h_tuple
            rw [← h_tuple]
            dsimp
            have : id_min = c.1 := by
              subst h_tuple
              rfl
            subst this
            obtain ⟨h_mem, h_elem⟩ := Std.TreeMap.getElem?_eq_some_iff.mp h_rem
            exfalso
            have h_free : (Expr.atom a).isFree ev.ctx = true := Expr.isFree_atom a ev.ctx
            have h_filt_mem : c.1 ∈ Std.TreeMap.filter (λ _ ex => ex.isFree ev.ctx) ev.remain := by
              rw [Std.TreeMap.mem_filter]
              refine ⟨h_mem, ?_⟩
              rw [h_elem]
              exact h_free
            have h_min_ne : (Std.TreeMap.filter (λ _ ex => ex.isFree ev.ctx) ev.remain).minKey? ≠ none := by
              intro h_empty_min
              have h_empty := Std.TreeMap.minKey?_eq_none_iff.mp h_empty_min
              have h_not := Std.TreeMap.not_mem_of_isEmpty (a := c.1) h_empty
              exact h_not h_filt_mem
            dsimp [Evaluation.findFree?] at h_none
            exact absurd h_none h_min_ne
          · contradiction
      simp [← h_c2]
      have h_step_inserted : (ev.step c).ctx.vals.get? c.1 = some c.2 := by
        dsimp [Evaluation.step]
        rw [Std.TreeMap.getElem?_insert]
        simp
      exact Evaluation.resolveAll_ctx_vals_get? (ev.step c) (ev.disjoint_step h_disj) c.1 c.2 h_step_inserted
    · have h_rem' : (ev.step c).remain.get? id = some (Expr.atom a) := by
        dsimp [Evaluation.step]
        rw [Std.TreeMap.getElem?_erase]
        have h_cmp : compare c.1 id ≠ Ordering.eq := by
          intro h_c
          exact h_eq (compare_eq_iff_eq.mp h_c)
        simp [h_cmp]
        exact h_rem
      exact Evaluation.resolveAll_get?_atom (ev.step c) (ev.disjoint_step h_disj) id a h_rem'
termination_by ev.remain.size
decreasing_by
  dsimp [Evaluation.step]
  have h_mem := Evaluation.computeOne_mem_some hc
  rw [Std.TreeMap.size_erase]
  simp [h_mem]
  have h_pos := size_gt_zero_if_mem ev.remain h_mem
  exact Nat.sub_one_lt_of_lt h_pos

theorem Grid.evaluate_get?_eq_canon
    (grid : Grid) (id : CellId) (a : Atomic)
    (ha : grid.cells.get? id = some (Expr.atom a)) :
    grid.evaluate.cells.get? id = some (Expr.atom a.canon) := by
  let ev0 : Evaluation := ⟨⟨∅⟩, grid.cells⟩
  have disj : ev0.DisjointKeys := by
    intro x ⟨h_ctx, _⟩
    dsimp [ev0] at h_ctx
    contradiction
  have h_res := Evaluation.resolveAll_get?_atom ev0 disj id a ha
  dsimp [Grid.evaluate]
  rw [Std.TreeMap.getElem?_map]
  simp
  exact h_res

theorem Grid.evaluate_cell_is_canon (grid : Grid) (id : CellId) (a : Atomic)
    (ha : grid.evaluate.cells.get? id = some (Expr.atom a)) : 
    a = a.canon := by
  have hcanon :
      ∀ id a,
        (Evaluation.mk ⟨∅⟩ grid.cells).resolveAll.ctx.vals.get? id = some a →
          a = a.canon := by
    apply Evaluation.resolveAll_vals_canon
    intro id a h
    simp at h

  dsimp [Grid.evaluate] at ha
  rw [Std.TreeMap.getElem?_map] at ha
  have hval :
      (Evaluation.mk ⟨∅⟩ grid.cells).resolveAll.ctx.vals[id]? =
        some a := by
    simpa using ha
  exact hcanon id a hval

theorem Grid.evaluate_idempotent (grid : Grid) :
    grid.evaluate.evaluate = grid.evaluate := by
  apply Grid.ext_get?
  intro id
  by_cases h_mem : id ∈ grid.cells
  ·
    have h_mem1 := (Grid.evaluate_keys ..).mp h_mem
    rcases Grid.evaluate_cells grid id h_mem with ⟨a, ha⟩
    have h_eval2 := Grid.evaluate_get?_eq_canon grid.evaluate id a ha
    have ha_canon : a = a.canon := Grid.evaluate_cell_is_canon grid id a ha
    rw [← ha_canon] at h_eval2
    simp [ha]
    exact h_eval2
  ·
    have h_not1 : id ∉ grid.evaluate.cells := mt (Grid.evaluate_keys ..).mpr h_mem
    have h_not2 : id ∉ grid.evaluate.evaluate.cells := mt (Grid.evaluate_keys ..).mpr h_not1
    simp [Std.TreeMap.getElem?_eq_none h_not1, Std.TreeMap.getElem?_eq_none h_not2]

deriving instance Repr for ByteArray

structure ByteCursor where
  data : ByteArray
  pos  : Nat := 0
deriving Repr

abbrev Parser := StateT ByteCursor Option

def readByte : Parser UInt8 := do
  let c ← get
  if h : c.pos < c.data.size then
    set { c with pos := c.pos + 1 }
    return c.data.get c.pos h
  else
    failure

def readNat32 : Parser Nat := do
  let bs ← Vector.replicate 4 0 |>.mapM (λ _ => readByte)
  return bs[0].toNat 
           ||| (bs[1].toNat <<< 8) 
           ||| (bs[2].toNat <<< 16) 
           ||| (bs[3].toNat <<< 24)

example : (readNat32.run ⟨ByteArray.mk #[8, 2, 0, 0], 0⟩).map (·.1) = some 520 :=
  by native_decide

def readFloat64 : Parser Float := do
  let bs ← Vector.replicate 8 0 |>.mapM (λ _ => readByte)
  let u : UInt64 := bs[0].toUInt64
                      ||| (bs[1].toUInt64 <<< 8)
                      ||| (bs[2].toUInt64 <<< 16)
                      ||| (bs[3].toUInt64 <<< 24)
                      ||| (bs[4].toUInt64 <<< 32)
                      ||| (bs[5].toUInt64 <<< 40)
                      ||| (bs[6].toUInt64 <<< 48)
                      ||| (bs[7].toUInt64 <<< 56)
  return Float.ofBits u

example : (readFloat64.run ⟨ByteArray.mk #[0, 0, 0, 0, 0, 0, 9, 64], 0⟩).map (·.1) = some 3.125 :=
  by native_decide

partial
def parseExpr : Parser Expr := do
  let tag ← readByte
  match Fin.ofNat 9 tag.toNat with
  | 1 =>
    let val ← readFloat64
    return .atom (.number val)
  | 2 =>
    return .atom (.string "Hello")
  | 3 =>
    return .atom .none
  | 4 =>
    let r ← readNat32
    let c ← readNat32
    return .ref ⟨r, c⟩
  | 5 =>
    let e1 ← parseExpr
    let e2 ← parseExpr
    return .add e1 e2
  | 6 =>
    let e1 ← parseExpr
    let e2 ← parseExpr
    return .sub e1 e2
  | 7 =>
    let e1 ← parseExpr
    let e2 ← parseExpr
    return .mult e1 e2
  | 8 =>
    let r ← readNat32
    let c ← readNat32
    return .ref ⟨r % 64, c % 64⟩
  | 0 =>
    let e1 ← parseExpr
    let e2 ← parseExpr
    return .div e1 e2

partial
def parseAndRun (grid : Grid) : Parser Grid := do
  let c ← get
  if c.pos ≥ c.data.size then
    return grid
  else
    let op ← readByte
    match Fin.ofNat 5 op.toNat with
    | 1 =>
      let r ← readNat32
      let c ← readNat32
      let ex ← parseExpr
      -- dbg_trace s!"ins {r},{c}={repr ex}"
      parseAndRun (grid.set ⟨r, c⟩ ex)
    | 2 =>
      let r ← readNat32
      let c ← readNat32
      -- dbg_trace s!"del {r},{c}"
      parseAndRun (grid.delete ⟨r, c⟩)
    | 3 =>
      let r ← readNat32
      let c ← readNat32
      let ex ← parseExpr
      -- dbg_trace s!"ins' {r % 64},{c % 64}={repr ex}"
      parseAndRun (grid.set ⟨r % 64, c % 64⟩ ex)
    | 4 =>
      let r ← readNat32
      let c ← readNat32
      -- dbg_trace s!"del' {r % 64},{c % 64}"
      parseAndRun (grid.delete ⟨r % 64, c % 64⟩)
    | 0 =>
      -- dbg_trace s!"eval"
      parseAndRun grid.evaluate

example : (
  (parseAndRun Grid.nil).run
  ⟨
    ByteArray.mk
      #[
        1, -- Set ⟨2, 1⟩ (atom (number 3.125))
        2, 0, 0, 0,
        1, 0, 0, 0,
        1, 0, 0, 0, 0, 0, 0, 9, 64,

        1, -- Set ⟨2, 2⟩ (atom (number 8.0))
        2, 0, 0, 0,
        2, 0, 0, 0,
        1, 0, 0, 0, 0, 0, 0, 32, 64,

        1, -- Set ⟨3, 1⟩ (add (ref ⟨2, 1⟩) (ref ⟨2, 2⟩))
        3, 0, 0, 0,
        1, 0, 0, 0,
        7, 4, 2, 0, 0, 0, 1, 0, 0, 0,
           4, 2, 0, 0, 0, 2, 0, 0, 0,

        5 -- Evaluate
      ],
    0
  ⟩ |>.map (·.1)
    |>.getD Grid.nil
    |>.cells.getD ⟨3, 1⟩ 0) == .atom (.number 25) :=
  by native_decide

def atomRepr : Atomic -> String
| .number n => s!"N:{Float.toBits n}"
| .string s => s!"S:{repr s}"
| .none => "Z"
| .error .divByZero => "E:div0"
| .error .typeMismatch => "E:type"
| .error .cyclic => "E:cycle"
| .error .invalidNumber => "E:invNum"

def atomGridRepr (m : Std.TreeMap CellId Atomic) : String :=
  String.intercalate ";" $
  m.toList.map λ (k, v) => s!"{k.1},{k.2}={atomRepr v}"

@[export run_lean_intrin]
def runInput (inp : ByteArray) : String :=
  match (parseAndRun Grid.nil).run ⟨inp, 0⟩ with
  | .some x =>
    Evaluation.mk ⟨∅⟩ x.1.cells
    |>.resolveAll.ctx.vals
    |> atomGridRepr
  | .none => "ERROR"

#eval Evaluation.mk ⟨∅⟩ dummy.cells |>.resolveAll.ctx.vals |> atomGridRepr

def test (n : Nat) :=
  ByteArray.mk #[n.toUInt8]

def test2 (x : Int) :=
  s!"hello, {x}"

#eval (parseAndRun Grid.nil).run ⟨ByteArray.mk #[
  0x01, 0x02, 0x00, 0x00, 0x01, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9,
  0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9,
  0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9,
  0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xe9,
  0xe9, 0xe9, 0xe9, 0xe9, 0xe9, 0xff, 0xff, 0xff, 0x02, 0x00, 0x01, 0x00,
  0xff, 0xff, 0xff, 0xff, 0xff, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b,
  0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b,
  0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b, 0x9b,
  0x9b, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x5d
], 0⟩ |>.getD (Grid.nil, ByteCursor.mk ByteArray.empty 0) |>.1.evaluate
