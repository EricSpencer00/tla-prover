---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANT Value

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
\* The set of all possible input sequences (finite sequences of Value)
Seq == [i \in Nat |-> Value]

(*-----------------------------------------------------------------
  Variables (inherited from the main specification; we redeclare them
  here to keep the module self-contained)
-----------------------------------------------------------------*)
VARIABLES seq,      \* the input sequence (function Nat -> Value)
          i,        \* current index (position processed so far)
          cand,     \* current candidate for majority
          count,    \* counter associated with the candidate
          done      \* flag indicating the scan is finished

(*-----------------------------------------------------------------
  Types
-----------------------------------------------------------------*)
TypeOK == 
    /\ seq \in [Nat -> Value]
    /\ i \in Nat
    /\ cand \in Value
    /\ count \in Nat
    /\ done \in BOOLEAN

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ i = 0
    /\ count = 0
    /\ cand \in Value      \* any value is a permissible initial candidate
    /\ done = FALSE
    /\ seq \in [Nat -> Value]  \* the concrete sequence will be supplied as a constant in the .cfg

(*-----------------------------------------------------------------
  NEXT action (the Boyer-Moore scan)
-----------------------------------------------------------------*)
Next ==
    \/ /\ ~done
       /\ i' = i + 1
       /\ IF count = 0 THEN
            /\ cand' = seq[i]
            /\ count' = 1
          ELSE
            IF seq[i] = cand THEN
                /\ cand' = cand
                /\ count' = count + 1
            ELSE
                /\ cand' = cand
                /\ count' = count - 1
       /\ done' = FALSE
    \/ /\ done
       /\ UNCHANGED <<seq, i, cand, count, done>>

Spec == Init /\ [][Next]_<<seq, i, cand, count, done>>

(*-----------------------------------------------------------------
  The standard inductive invariant from the main specification.
  For every position j < i, the candidate cand is the majority of the
  processed prefix when such a majority exists.
-----------------------------------------------------------------*)
Inv ==
    \A j \in 0..(i-1) :
        (Cardinality({ k \in 0..(i-1) : seq[k] = cand }) >
         Cardinality({ k \in 0..(i-1) : seq[k] # cand }) ) =>
        cand = seq[j]

(*-----------------------------------------------------------------
  Safety property: after the whole sequence has been processed,
  any value that appears in more than half of the positions must be
  the final candidate.
-----------------------------------------------------------------*)
Correct ==
    /\ done
    /\ \A v \in Value :
          ( Cardinality({ k \in 0..(i-1) : seq[k] = v }) >
            Cardinality({ k \in 0..(i-1) : seq[k] # v }) ) =>
          v = cand

=============================================================================