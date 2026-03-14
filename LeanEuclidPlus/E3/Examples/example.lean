import E3
import Qq

open Qq Lean

def prediction : Expr :=
  q(∀ (a b c : Point) (BC : Line), distinctPointsOnLine c b BC ∧ b ≠ a → ∃ (l : Point), |(l─a)| = |(c─b)|)

def ground_truth : Expr :=
  q(∀ (a b c : Point) (BC : Line), distinctPointsOnLine b c BC ∧ a ≠ b  → ∃ (l : Point), |(a─l)| = |(b─c)|)

def main (args : List String) : IO Unit := do
    runE3fromIO (ground := ground_truth) (test := prediction) (← parseArgs args)

#eval main ["test", "precheck+separate", "1", "5", "5", "false"]
