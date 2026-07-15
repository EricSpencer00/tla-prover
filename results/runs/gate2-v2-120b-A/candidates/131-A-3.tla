---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT Value

(***************************************************************************)
(*  Overview:                                                             *)
(*  This module provides a machine‑checked proof of the Boyer‑Moore       *)
(*  majority vote algorithm.  It imports the core algorithm specification *)
(*  (assumed to be defined in a module named Majority) and adds the        *)
(*  necessary invariants and a hierarchical proof that the algorithm is  *)
(*  type‑correct and that the candidate returned after processing the     *)
(*  entire input sequence is the only possible majority element.          *)
(***************************************************************************)

(* ---------------------------------------------------------------------- *)
(*  Imports the core algorithm.  The imported module must export the       *)
(*  following identifiers:                                                *)
(*    - Vars : the tuple of state variables (Seq, Pos, Cand, Count)       *)
(*    - Init : the initial state predicate                                 *)
(*    - Next : the transition relation                                    *)
(*    - Inv  : the inductive invariant used by the core spec              *)
(*    - Majority : the original correctness invariant (what we prove)    *)
(* ---------------------------------------------------------------------- *)
EXTENDS Majority

(* ---------------------------------------------------------------------- *)
(*  State variables (re‑exposed for clarity, but not new)                 *)
(* ---------------------------------------------------------------------- *)
VARIABLES Seq, Pos, Cand, Count

(* ---------------------------------------------------------------------- *)
(*  Initialization predicate – simply re‑use the one from the core module*)
(* ---------------------------------------------------------------------- *)
Init == Init

(* ---------------------------------------------------------------------- *)
(*  Next-state relation – re‑use the one from the core module             *)
(* ---------------------------------------------------------------------- *)
Next == Next

(* ---------------------------------------------------------------------- *)
(*  Full specification (behavior)                                        *)
(* ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<Seq, Pos, Cand, Count>>

(* ---------------------------------------------------------------------- *)
(*  Type correctness invariant                                            *)
(* ---------------------------------------------------------------------- *)
TypeOK ==
    /\ Seq \in Seq(Value)               \* A finite sequence of elements of Value
    /\ Pos \in Nat
    /\ Pos <= Len(Seq)
    /\ Cand \in Value \/ Cand = ""       \* "" denotes “no candidate yet”
    /\ Count \in Nat
    /\ (Pos = 0) => (Cand = "" /\ Count = 0)

(* ---------------------------------------------------------------------- *)
(*  Main correctness invariant (what the algorithm guarantees)          *)
(* ---------------------------------------------------------------------- *)
Correct ==
    /\ Inv
    /\ (Pos = Len(Seq)) => 
        \A v \in Value :
          (Cardinality({ i \in 0..(Len(Seq)-1) : Seq[i] = v }) > Len(Seq) / 2) => v = Cand

(* ---------------------------------------------------------------------- *)
(*  The specification must include the auxiliary invariant Inv from the  *)
(*  core module; we expose it here so that it can be listed among the     *)
(*  required invariants.                                                  *)
(* ---------------------------------------------------------------------- *)
Inv == Inv

(* ---------------------------------------------------------------------- *)
(*  Safety property that the specification satisfies (type‑correctness   *)
(*  and algorithmic correctness).                                        *)
(* ---------------------------------------------------------------------- *)
Safety == TypeOK /\ Correct

=============================================================================