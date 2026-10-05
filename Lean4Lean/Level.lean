import Lean
import Lean4Lean.List

namespace Lean.Level

def forEach [Monad m] (l : Level) (f : Level → m Bool) : m Unit := do
  if !(← f l) then return
  match l with
  | .succ l => l.forEach f
  | .max l₁ l₂ | .imax l₁ l₂ => l₁.forEach f; l₂.forEach f
  | .zero | .param .. | .mvar .. => pure ()

def getUndefParam (l : Level) (ps : List Name) : Option Name := Id.run do
  (·.2) <$> StateT.run (s := none) do
    l.forEach fun l => do
      if !l.hasParam || (← get).isSome then
        return false
      if let .param n := l then
        if n ∉ ps then
          set (some n)
      return true

/-!
## Level normalization

Based on Yoan Géran, "A Canonical Form for Universe Levels in Impredicative Type Theory"
<https://lmf.cnrs.fr/downloads/Perso/long.pdf>.
-/

namespace Normalize

local instance : Ord Name := ⟨Name.cmp⟩

/-- represents v+n -/
structure VarNode where
  var : Name
  offset : Nat
  deriving BEq, Ord, Repr

/-- An key-value pair `vs => { path, const, var }` in NormLevel represents
the max of `C(vs, const)` and `V(vs, v, n)` for each `v+n ∈ var`, using the `C` and `V` sublevel
functions from <https://lmf.cnrs.fr/downloads/Perso/long.pdf>.
The `path` assists in ensuring the invariant that for each suffix `vs' <:+ path`,
`vs'` is also in the `NormLevel` map. -/
structure Node where
  path : List Name := []
  const : Nat := 0
  var : List VarNode := []
  deriving Repr, Inhabited

instance : BEq Node where
  beq n₁ n₂ := n₁.const == n₂.const && n₁.var == n₂.var
instance : Ord Node where
  compare n₁ n₂ := compare n₁.const n₂.const |>.then <| compare n₁.var n₂.var

def subset (cmp : α → α → Ordering) : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys =>
    match cmp x y with
    | .lt => false
    | .eq => subset cmp xs ys
    | .gt => subset cmp (x :: xs) ys

def orderedInsert (cmp : α → α → Ordering) (a : α) : List α → Option (List α)
  | [] => some [a]
  | b :: l =>
    match cmp a b with
    | .lt => some (a :: b :: l)
    | .eq => none
    | .gt => (orderedInsert cmp a l).map (b :: ·)

def NormLevel := Std.TreeMap (List Name) Node compare
  deriving Repr

instance : BEq NormLevel where
  beq l₁ l₂ :=
    (l₁.all fun p n => l₂.get? p == some n) &&
    (l₂.all fun p n => l₁.get? p == some n)

def VarNode.addVar (v : Name) (k : Nat) : List VarNode → List VarNode
  | [] => [⟨v, k⟩]
  | v' :: l =>
    match Name.cmp v v'.var with
    | .lt => ⟨v, k⟩ :: v' :: l
    | .eq => ⟨v, v'.offset.max k⟩ :: l
    | .gt => v' :: addVar v k l

def NormLevel.addVar (v : Name) (k : Nat) (path' : List Name) (s : NormLevel) : NormLevel :=
  s.modify path' fun n => { n with var := VarNode.addVar v k n.var }

def NormLevel.addNode (v : Name) (k : Nat) (path' : List Name) (s : NormLevel) : NormLevel :=
  s.alter path' fun
    | none => some { var := [⟨v, k⟩] }
    | some n => some { n with var := VarNode.addVar v k n.var }

def NormLevel.addConst (k : Nat) (path : List Name) (acc : NormLevel) : NormLevel :=
  if k = 0 || k = 1 && !path.isEmpty then acc else
  acc.modify path fun n => { n with const := k.max n.const }

def normalizeAux (l : Level) (path : List Name) (k : Nat) (acc : NormLevel) : NormLevel :=
  match l with
  | .zero | .imax _ .zero => acc.addConst k path
  | .succ u => normalizeAux u path (k+1) acc
  | .max u v => normalizeAux u path k acc |> normalizeAux v path k
  | .imax u (.succ v) => normalizeAux u path k acc |> normalizeAux v path (k+1)
  | .imax u (.max v w) => normalizeAux (.imax u v) path k acc |> normalizeAux (.imax u w) path k
  | .imax u (.imax v w) => normalizeAux (.imax u w) path k acc |> normalizeAux (.imax v w) path k
  | .imax u (.param v) =>
    match orderedInsert Name.cmp v path with
    | some path' => acc.addConst k path |>.addNode v k path' |> normalizeAux u path' k
    | none =>
      let acc := if k = 0 then acc else acc.addVar v k path
      normalizeAux u path k acc
  | .mvar _ | .imax _ (.mvar _) => acc -- unreachable
  | .param v =>
    match orderedInsert Name.cmp v path with
    | some path' => acc.addConst k path |>.addNode v k path'
    | none => if k = 0 then acc else acc.addVar v k path

def subsumeVars : List VarNode → List VarNode → List VarNode
  | [], _ => []
  | xs, [] => xs
  | x :: xs, y :: ys =>
    match Name.cmp x.var y.var with
    | .lt => x :: subsumeVars xs (y :: ys)
    | .eq => if x.offset ≤ y.offset then subsumeVars xs ys else x :: subsumeVars xs ys
    | .gt => subsumeVars (x :: xs) ys

def findParent (f : List Name → Bool) : (l₁ l₂ : List Name) → List Name
  | _, [] => []
  | l₁, a :: l₂ => if f (l₁.reverseAux l₂) then [a] else findParent f (a :: l₁) l₂

def NormLevel.subsumption (acc : NormLevel) (paths := false) : NormLevel :=
  acc.foldl (init := acc) fun acc p₁ n₁ =>
    let n₁ := acc.foldl (init := n₁) fun n₁ p₂ n₂ =>
      if !subset compare p₂ p₁ then n₁ else
      let same := p₁.length == p₂.length
      let n₁ :=
        if n₁.const = 0 ||
          (same || n₁.const > n₂.const) &&
          (n₂.var.isEmpty || n₁.const > n₁.var.foldl (·.max ·.offset) 0 + 1)
        then n₁ else { n₁ with const := 0 }
      if same || n₂.var.isEmpty then n₁ else { n₁ with var := subsumeVars n₁.var n₂.var }
    let n₁ := if paths then
      let path := findParent acc.contains [] p₁
      let var := if let [v] := path then subsumeVars n₁.var [⟨v, 0⟩] else n₁.var
      { n₁ with path, var }
    else n₁
    acc.insert p₁ n₁

def normalize (l : Level) (paths := false) : NormLevel :=
  Normalize.normalizeAux l [] 0 (.insert {} [] default) |>.subsumption paths

def leVars : List VarNode → List VarNode → Bool
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys =>
    match Name.cmp x.var y.var with
    | .lt => false
    | .eq => x.offset ≤ y.offset && leVars xs ys
    | .gt => leVars (x :: xs) ys

def NormLevel.le (l₁ l₂ : NormLevel) : Bool :=
  l₁.all fun p₁ n₁ =>
    if n₁.const = 0 && n₁.var.isEmpty then true else
    l₂.any fun p₂ n₂ =>
      (!n₂.var.isEmpty || n₁.var.isEmpty) &&
      subset compare p₂ p₁ &&
      (n₁.const ≤ n₂.const || n₂.var.any (n₁.const ≤ ·.offset + 1)) &&
      leVars n₁.var n₂.var

def NormLevel.buildPaths : StateM NormLevel Unit := do
  (← get).foldlM (init := ()) fun _ p _ => do
    let n := (← get).get! p
    if let [v] := n.path then
      let l ← getPath (p.erase v) p.length
      setPath p (v :: l)
where
  setPath (p path : List Name) : StateM NormLevel Unit :=
    modify (·.modify p ({ · with path }))

  getPath (p : List Name) (depth : Nat) : StateM NormLevel (List Name) := do
    let n := (← get).get! p
    if let [v] := n.path then
      if let depth + 1 := depth then
        let l ← getPath (p.erase v) depth
        setPath p (v :: l)
        return v :: l
    return n.path

structure Tree where
  const : Nat
  var : List VarNode
  child : List (Name × Tree)
  deriving Inhabited

def modifyAt [Inhabited α] (f : α → α) (n : Name) : List (Name × α) → List (Name × α)
  | [] => [(n, f default)]
  | (x, v) :: l =>
    match Name.cmp n x with
    | .lt => (n, f default) :: (x, v) :: l
    | .eq => (x, f v) :: l
    | .gt => (x, v) :: modifyAt f n l

def Tree.modify (path : List Name) (f : Tree → Tree) (t : Tree) : Tree :=
  match path with
  | [] => f t
  | a :: p => modify p (t := t) fun t => { t with child := modifyAt f a t.child }

def NormLevel.toTree (acc : NormLevel) : Tree :=
  (buildPaths.run acc).run.2.foldl (init := ⟨0, [], []⟩) fun t _ n =>
    t.modify n.path fun t => { t with const := n.const, var := n.var }

def treeVarDedup : List VarNode → List (Name × Tree) → List VarNode
  | [], _ => []
  | xs, [] => xs
  | x :: xs, y :: ys =>
    match Name.cmp x.1 y.1 with
    | .lt => x :: treeVarDedup xs (y :: ys)
    | .eq => if x.2 = 0 then treeVarDedup xs ys else x :: treeVarDedup xs ys
    | .gt => treeVarDedup (x :: xs) ys

def Tree.reify : Tree → Level
  | { const, var, child } =>
    let l := child.foldr mkChild none
    let l := (treeVarDedup var child).foldr (init := l) fun n r =>
      some (mkMax (addOffset (.param n.var) n.offset) r)
    match l with
    | none => ofNat const
    | some l => if const = 0 then l else max (ofNat const) l
where
  mkMax (l : Level) : Option Level → Level
  | none => l
  | some u => max l u
  mkChild
  | (n, t), r =>
    match reify t with
    | .zero => mkMax (.param n) r
    | t => mkMax (imax t (.param n)) r

end Normalize

/-- The local `imax` simplifications in the original level normalizer. -/
def normalizeIMax (u v : Level) : Level :=
  if v == .zero then v
  else if u == .zero then v
  else if u == .succ .zero then v
  else if u == v then u
  else .imax u v

namespace NormalizeCore

def maxArgs : Level → List Level
  | .max u v => maxArgs u ++ maxArgs v
  | u => [u]

def accMax (result u : Level) : Level :=
  match result with
  | .zero => u
  | _ => .max result u

/-- Merge consecutive terms with the same base. Taking the larger offset explicitly
makes preservation independent of the sorting invariant. -/
def mergeMax : List Level → Level → Level → Level
  | [], prev, result => accMax result prev
  | u :: us, prev, result =>
    if u.getLevelOffset == prev.getLevelOffset then
      mergeMax us (if prev.getOffset ≤ u.getOffset then u else prev) result
    else mergeMax us u (accMax result prev)

def subsumed (us : List Level) (u : Level) : Bool :=
  u.getLevelOffset.isZero && us.any fun v =>
    !v.getLevelOffset.isZero && u.getOffset ≤ v.getOffset

/-- Flatten, sort, remove subsumed explicit levels, and merge repeated bases,
as in the original normalizer. Merge sort provides a total, transparent sort. -/
def max (u v : Level) : Level :=
  let us := maxArgs u ++ maxArgs v
  match (us.filter fun u => !subsumed us u).mergeSort normLt with
  | [] => .zero
  | u :: us => mergeMax us u .zero

def addOffset : Level → Nat → Level
  | .max u v, k => .max (addOffset u k) (addOffset v k)
  | u, k => u.addOffset k

def normalize : Level → Nat → Level
  | .zero, k => Level.zero.addOffset k
  | .succ u, k => normalize u (k + 1)
  | .max u v, k => max (addOffset (normalize u 0) k) (addOffset (normalize v 0) k)
  | .imax u v, k =>
    if v.isNeverZero then (max (normalize u 0) (normalize v 0)).addOffset k
    else (normalizeIMax (normalize u 0) (normalize v 0)).addOffset k
  | .param n, k => (Level.param n).addOffset k
  | .mvar n, k => (Level.mvar n).addOffset k

end NormalizeCore

/-- A total version of the original normalizer's flatten/sort/subsume algorithm. -/
def normalizeCore (u : Level) : Level := NormalizeCore.normalize u 0

def normalize' (l : Level) : Level := normalizeCore l

/-- The recursive comparison core of `Lean.Level.geq`, exposed for verification. -/
def geqCore (u v : Level) : Bool :=
  u == v ||
  match u, v with
  | _, .zero => true
  | u, .max v₁ v₂ => geqCore u v₁ && geqCore u v₂
  | .max u₁ u₂, .imax v₁ v₂ =>
    geqCore u₁ (.imax v₁ v₂) || geqCore u₂ (.imax v₁ v₂) ||
      (geqCore (.max u₁ u₂) v₁ && geqCore (.max u₁ u₂) v₂)
  | .max u₁ u₂, v =>
    let v' := v.getLevelOffset
    geqCore u₁ v || geqCore u₂ v ||
      (((Level.max u₁ u₂).getLevelOffset == v' || v'.isZero) &&
        (Level.max u₁ u₂).getOffset ≥ v.getOffset)
  | .imax _ u₂, v => geqCore u₂ v
  | .succ u, .succ v => geqCore u v
  | u, .imax v₁ v₂ => geqCore u v₁ && geqCore u v₂
  | u, v =>
    let v' := v.getLevelOffset
    (u.getLevelOffset == v' || v'.isZero) && u.getOffset ≥ v.getOffset
termination_by (u, v)

def geq' (u v : Level) : Bool := geqCore (normalizeCore u) (normalizeCore v)

def isEquiv' (u v : Level) : Bool := u == v || normalizeCore u == normalizeCore v

def isEquivList : List Level → List Level → Bool := List.all2 isEquiv'

-- local elab "normalize " l:level : command => do
--   Elab.Command.runTermElabM fun _ => do
--     logInfo m!"{normalize' (← Elab.Term.elabLevel l)}"
--     -- logInfo m!"{repr <| Normalize.normalize (← Elab.Term.elabLevel l) }"

-- local elab "normalize " l:level " ≤ " l':level : command => do
--   Elab.Command.runTermElabM fun _ => do
--     logInfo m!"{geq' (← Elab.Term.elabLevel l') (← Elab.Term.elabLevel l)}"
--     -- logInfo m!"{repr <| Normalize.normalize (← Elab.Term.elabLevel l)}"
--     -- logInfo m!"{repr <| Normalize.normalize (← Elab.Term.elabLevel l')}"

-- universe u v w
-- /-- info: max 1 u -/
-- #guard_msgs in normalize max u 1
-- /-- info: u -/
-- #guard_msgs in normalize imax 1 u
-- /-- info: max 1 (imax (u+1) u) -/
-- #guard_msgs in normalize u+1
-- /-- info: imax 2 u -/
-- #guard_msgs in normalize imax 2 u
-- /-- info: max v (imax (imax u v) w) -/
-- #guard_msgs in normalize max w (imax (imax u w) v)
-- /-- info: max v (imax (imax u v) w) -/
-- #guard_msgs in normalize max (imax (imax u v) w) (imax (imax u w) v)
-- /-- info: u -/
-- #guard_msgs in normalize imax u u
-- /-- info: max 1 (imax (u+1) u) -/
-- #guard_msgs in normalize imax u (u+1)
-- /-- info: max 1 (imax (max (v+1) (imax (u+1) u)) v) -/
-- #guard_msgs in normalize imax u v + 1
