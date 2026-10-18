import Lean

namespace PB006Audit

def divisors (n : Nat) : List Nat :=
  ((List.range n).map (fun i => i + 1)).filter
    (fun d => n % d == 0)

def listGcd : List Nat → Nat
  | [] => 0
  | x :: xs => xs.foldl Nat.gcd x

def blockWeight (block : List Nat) : Nat :=
  (divisors (listGcd block)).foldl
    (fun acc d => acc + d ^ (block.length - 1)) 0

def insertIntoBlocks (x : Nat) :
    List (List Nat) → List (List (List Nat))
  | [] => []
  | b :: bs =>
      ((x :: b) :: bs) ::
        ((insertIntoBlocks x bs).map (fun rest => b :: rest))

-- Positions are distinguished by recursive insertion.
-- Repeated cycle lengths can produce equal-looking list entries;
-- their multiplicity must be retained, not deduplicated.
def cyclePartitions :
    List Nat → List (List (List Nat))
  | [] => [[]]
  | x :: xs =>
      (cyclePartitions xs).foldl
        (fun acc part =>
          acc ++ (([x] :: part) :: insertIntoBlocks x part))
        []

def weightedBell (ct : List Nat) : Nat :=
  (cyclePartitions ct).foldl
    (fun total part =>
      total + part.foldl
        (fun prod block => prod * blockWeight block) 1)
    0

end PB006Audit
