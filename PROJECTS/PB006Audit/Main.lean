import PB006Audit.Basic

def main (args : List String) : IO Unit := do
  let count :=
    match args with
    | [] => 6
    | x :: _ => x.toNat!
  let answer :=
    PB006Audit.weightedBell (List.replicate count 2)
  IO.println answer
