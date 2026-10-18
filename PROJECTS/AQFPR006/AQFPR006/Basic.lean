def divisors (n : Nat) : List Nat :=
  ((List.range n).map (· + 1)).filter (fun d => n % d == 0)

def listGcd : List Nat → Nat
| [] => 0
| x :: xs => xs.foldl Nat.gcd x

def blockWeight (block : List Nat) : Nat :=
  (divisors (listGcd block)).foldl (fun acc d => acc + d ^ (block.length - 1)) 0

def rgs (r : Nat) : List (List Nat) :=
  match r with
  | 0 => [[]]
  | r+1 =>
    (rgs r).foldl (fun acc cur =>
      let mx := cur.foldl Nat.max 0
      let nextMax := if cur.isEmpty then 0 else mx + 1
      (List.range (nextMax + 1)).foldl (fun acc2 l => acc2 ++ [cur ++ [l]]) acc
    ) []

def partitionsFromRGS (code : List Nat) : List (List Nat) :=
  if code.isEmpty then []
  else
    let mx := code.foldl Nat.max 0
    (List.range (mx+1)).map fun l =>
      (List.range code.length).filter fun i => code[i]! == l

def partitions (r : Nat) : List (List (List Nat)) :=
  (rgs r).map partitionsFromRGS

def weightedBell (ct : List Nat) : Nat :=
  (partitions ct.length).foldl (fun total part =>
    total + part.foldl (fun prod block =>
      prod * blockWeight (block.map fun i => ct[i]!)
    ) 1
  ) 0

theorem anchor_112 : weightedBell [1,1,2] = 7 := by native_decide
theorem anchor_22 : weightedBell [2,2] = 7 := by native_decide
theorem anchor_222 : weightedBell [2,2,2] = 31 := by native_decide
theorem anchor_24 : weightedBell [2,4] = 9 := by native_decide
theorem anchor_33 : weightedBell [3,3] = 8 := by native_decide
