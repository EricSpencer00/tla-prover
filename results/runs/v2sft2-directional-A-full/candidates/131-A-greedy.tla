---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT Value

VARIABLES seq, pos, candidate, count

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

(* The set of all possible values *)
Values == Value

(* The length of the input sequence *)
Len == Len(seq)

(* The set of positions in the sequence (1..Len) *)
Positions == 1..Len

(* The set of positions before a given index i (exclusive) *)
Before(i) == {j \in Positions : j < i}

(* The number of occurrences of a value v in the prefix up to index i-1 *)
CountInPrefix(v, i) ==
    Cardinality({j \in Positions : j < i /\ seq[j] = v})

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
    /\ seq \in Seq(Values, 1..Len)
    /\ pos = 1
    /\ candidate \in Values
    /\ count = 1

(* ----------------------------------------------------------------------
   Next-state relation (the Boyer-Moore algorithm)
   ---------------------------------------------------------------------- *)

Next ==
    /\ pos <= Len
    /\ IF pos = Len THEN
           /\ pos' = pos + 1
           /\ UNCHANGED <<candidate, count>>
       ELSE
           /\ IF seq[pos] = candidate THEN
                  /\ count' = count + 1
                  /\ pos' = pos + 1
                  /\ UNCHANGED candidate
              ELSE
                  /\ IF count = 1 THEN
                         /\ candidate' = seq[pos]
                         /\ count' = 1
                         /\ pos' = pos + 1
                     ELSE
                         /\ count' = count - 1
                         /\ pos' = pos + 1
                         /\ UNCHANGED candidate

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<seq, pos, candidate, count>>

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)

TypeOK ==
    /\ seq \in Seq(Values, 1..Len)
    /\ pos \in 1..(Len + 1)
    /\ candidate \in Values
    /\ count \in Nat

(* ----------------------------------------------------------------------
   Correctness invariant (from the main specification)
   ---------------------------------------------------------------------- *)

Correct ==
    /\ pos = Len + 1
    /\ \A v \in Values :
          (CountInPrefix(v, Len + 1) > Len / 2) => (v = candidate)

(* ----------------------------------------------------------------------
   Combined invariant used in the proof
   ---------------------------------------------------------------------- *)

Inv == TypeOK /\ Correct

(* ----------------------------------------------------------------------
   Safety properties (the invariants)
   ---------------------------------------------------------------------- *)

SafetyProps == {TypeOK, Correct, Inv}

====