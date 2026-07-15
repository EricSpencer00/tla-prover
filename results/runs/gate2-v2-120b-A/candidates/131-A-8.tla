---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Value

VARIABLES i, cand, count, seq

(* ------------------------------------------------------------------------ *)
(* Type definitions                                                          *)
(* ------------------------------------------------------------------------ *)

Values == Value

(* ------------------------------------------------------------------------ *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------ *)

Positions == 1 .. Len(seq)

Before(i) == { j \in Positions : j < i }

Occurrences(v, S) == { j \in S : seq[j] = v }

(* ------------------------------------------------------------------------ *)
(* Initial state                                                            *)
(* ------------------------------------------------------------------------ *)

Init ==
  /\ i = 1
  /\ cand \in Values
  /\ count \in 0 .. 1
  /\ seq \in [1 .. Len(seq) -> Values]           \* seq is a finite sequence of values
  /\ count = 0 \/ (count = 1 /\ cand = seq[1])

(* ------------------------------------------------------------------------ *)
(* Transition relation                                                      *)
(* ------------------------------------------------------------------------ *)

Next ==
  \/ /\ i < Len(seq)
     /\ i' = i + 1
     /\ IF count = 0
          THEN /\ cand' = seq[i']
               /\ count' = 1
          ELSE IF cand = seq[i']
               THEN /\ cand' = cand
                    /\ count' = count + 1
               ELSE /\ cand' = cand
                    /\ count' = count - 1
  \/ /\ i = Len(seq)
     /\ UNCHANGED <<cand, count, seq>>

(* ------------------------------------------------------------------------ *)
(* Specification                                                            *)
(* ------------------------------------------------------------------------ *)

Spec == Init /\ [][Next]_<<i, cand, count, seq>>

(* ------------------------------------------------------------------------ *)
(* Invariants                                                               *)
(* ------------------------------------------------------------------------ *)

(* Type correctness invariant *)
TypeOK ==
  /\ i \in Positions
  /\ cand \in Values
  /\ count \in Nat
  /\ seq \in [1 .. Len(seq) -> Values]

(* Main correctness invariant *)
Inv ==
  \A v \in Values :
    ( Cardinality(Occurrences(v, Positions)) >
      Cardinality(Positions) / 2 ) => v = cand

Correct == Inv

=============================================================================