---- MODULE MCMajority ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\* Constants (to be assigned in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS A, B, C, bound, Seq

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
Values == {A, B, C}
BoundedSeq == { s \in Seq : Len(s) <= bound }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, i, cand, count

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Len(s) == IF s = {} THEN 0 ELSE
          IF s = <<>> THEN 0 ELSE
          Len( s[1 .. Len(s) - 1] ) + 1

\* ----------------------------------------------------------------------
\* Initial predicate (inherited from the main specification)
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in Values
    /\ count = 0

\* ----------------------------------------------------------------------
\* Action definitions (the three‑case logic of the Boyer‑Moore algorithm)
\* ----------------------------------------------------------------------
ScanComplete == i > Len(seq)

SameAsCand == i <= Len(seq) /\ seq[i] = cand
DifferentFromCand == i <= Len(seq) /\ seq[i] # cand

AdoptNewCand ==
    /\ i <= Len(seq)
    /\ count = 0
    /\ cand' = seq[i]
    /\ count' = 1
    /\ i' = i + 1
    /\ UNCHANGED seq

Increment ==
    /\ SameAsCand
    /\ count' = count + 1
    /\ i' = i + 1
    /\ UNCHANGED <<seq, cand>>

Decrement ==
    /\ DifferentFromCand
    /\ count > 0
    /\ count' = count - 1
    /\ i' = i + 1
    /\ UNCHANGED <<seq, cand>>

Next ==
    \/ ScanComplete
    \/ AdoptNewCand
    \/ Increment
    \/ Decrement

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, count>>

\* ----------------------------------------------------------------------
\* Safety invariants (inherited from the main specification)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in Values
    /\ count \in Nat

Correct ==
    /\ i > Len(seq)
    /\ ( \E v \in Values :
           \A j \in 1..Len(seq) : (seq[j] = v) => (v = cand) )
    => cand = Seq Majority(seq)

Inv ==
    (* The standard Boyer‑Moore invariant: if a value occurs more than half
       the scanned prefix, it must be the current candidate. *)
    \A v \in Values :
        ( \A j \in 1..(i-1) : seq[j] = v ) => v = cand

\* ----------------------------------------------------------------------
\* Liveness property (scanning eventually completes)
\* ----------------------------------------------------------------------
Termination == <> ScanComplete

====