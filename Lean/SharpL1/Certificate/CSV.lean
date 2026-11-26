module

public import SharpL1.Certificate.Checker
public meta import SharpL1.Certificate.Checker
public import Lean.Elab.Term

public section

/-!
# Import the integer CSV for kernel checking

The term elaborator quotes selected CSV rows as ordinary Lean literals. Parsing
is outside the kernel. The emitted row values are the ones passed to the
checker, and the checker proofs have no oracle for arithmetic validity.
-/

namespace SharpL1.Certificate

private meta def certificateText : String := include_str "../../../certificates/brackets.csv"

private meta def bracketPairs : List ℤ → List (ℤ × ℤ)
  | lo :: hi :: rest => (lo, hi) :: bracketPairs rest
  | _ => []

private meta def parseFields (row : String) : Except String (ℕ × Row) := do
  let fields ← (row.splitOn ",").mapM fun field =>
    match field.trimAscii.toString.toInt? with
    | some value => .ok value
    | none => .error s!"invalid integer {field}"
  match fields with
  | n :: t :: entries =>
    if 3 ≤ n && n ≤ 19 && entries.length = 2 * (n.toNat + 1) then
      return (n.toNat, ⟨t, bracketPairs entries⟩)
    else throw "invalid order or row length"
  | _ => throw "expected order and parameter"

private meta def selectRows (order : ℕ) : Except String (List Row) := do
  let all ← (certificateText.splitOn "\n").filterMapM fun line => do
    if line.trimAscii.isEmpty then return none
    let (n, row) ← parseFields line
    return if n = order then some row else none
  if all.isEmpty then throw s!"missing order {order}" else pure all

/-- The first row carries the origin check. Each chunk continues from the
preceding row and contributes its own small kernel proof. -/
structure ImportedOrder where
  first : Row
  chunks : List (List Row)

/-- The CSV rows in the original order, with chunk boundaries erased. -/
@[expose] def ImportedOrder.rows (order : ImportedOrder) : List Row :=
  order.first :: order.chunks.flatten

private meta def rowChunks (order : ℕ) (rows : List Row) : List (List Row) :=
  let size := if 16 ≤ order then 2 else 8
  (List.range ((rows.length + size - 1) / size)).map fun i => (rows.drop (size * i)).take size

open Lean Elab Term in
elab "certificate_order% " n:num : term => do
  let rows ← ofExcept (selectRows n.getNat)
  let first :: rest := rows | throwError "empty certificate order"
  let quoteRow := fun (row : Row) =>
    mkApp2 (mkConst ``Row.mk) (toExpr row.t) (toExpr row.brackets)
  let quoteList := fun (chunk : List Row) => Meta.mkListLit (mkConst ``Row) (chunk.map quoteRow)
  let chunks ← (rowChunks n.getNat rest).mapM (m := MetaM) quoteList
  let groups ← Meta.mkListLit (mkApp (mkConst ``List [.zero]) (mkConst ``Row)) chunks
  return mkApp2 (mkConst ``ImportedOrder.mk) (quoteRow first) groups

theorem ImportedOrder.check (n : ℕ) (order : ImportedOrder)
    (hfirst : checkStart n order.first = true)
    (htail : CheckedChunks n order.first order.chunks) : checkOrder n order.rows = true :=
  checkOrder_of_chunks n order.first order.chunks hfirst htail

open Lean Elab Command in
/-- Import an order and certify its chunks using kernel arithmetic. The named
theorem refers to the generated `nameData` declaration. -/
elab "certify_order " n:num " as " name:ident : command => do
  let data := mkIdentFrom name (name.getId.appendAfter "Data")
  elabCommand (← `(command|
    set_option maxRecDepth 131072 in
    @[expose] def $data : ImportedOrder := certificate_order% $n))
  elabCommand (← `(command|
    set_option maxRecDepth 131072 in
    set_option maxHeartbeats 0 in
    theorem $name : checkOrder $n ($data).rows = true := by
      refine ImportedOrder.check $n $data (by decide +kernel) ?_
      repeat first
        | exact CheckedChunks.last (by decide +kernel)
        | refine CheckedChunks.next (by decide +kernel) ?_))

end SharpL1.Certificate
