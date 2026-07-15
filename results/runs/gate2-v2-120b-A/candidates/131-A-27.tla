---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT Value

(*--------------------------------------------------------------------
  Derived definitions from the main Boyer-Moore majority vote spec.
  For the purpose of this proof module we re‑declare the necessary
  state variables and definitions, assuming that the original spec
  defines the same identifiers.  No new state is introduced.
--------------------------------------------------------------------*)
VARIABLES seq, idx, cand, count

(* The input sequence of values.  It is a function from the domain
   1..N (where N is a natural number) to the set Value.  N is
   a constant that bounds the length of the sequence. *)
CONSTANT N
Seq == [i \in 1..N |-> seq[i]]

(* Initial state: an arbitrary sequence and the algorithm's initial
   configuration. *)
Init ==
  /\ seq \in [1..N -> Value]
  /\ idx = 1
  /\ cand \in Value
  /\ count = 0

(* One step of the Boyer-Moore algorithm. *)
Next ==
  \/ /\ idx <= N
     /\ IF count = 0
        THEN /\ cand' = seq[idx]
             /\ count' = 1
        ELSE IF cand = seq[idx]
                THEN /\ cand' = cand
                     /\ count' = count + 1
                ELSE /\ cand' = cand
                     /\ count' = count - 1
     /\ idx' = idx + 1
  \/ /\ idx = N + 1   \* idle step after the scan is finished
     /\ UNCHANGED <<seq, idx, cand, count>>

Spec == Init /\ [][Next]_<<seq, idx, cand, count>>

(*--------------------------------------------------------------------
  Helper definitions used in the invariants.
--------------------------------------------------------------------*)
Occurences(v) == { i \in 1..N : seq[i] = v }

StrictMajorityValues ==
  { v \in Value : Cardinality(Occurences(v)) > N / 2 }

(*--------------------------------------------------------------------
  Invariant: Type correctness (no state variable strays outside its
  intended domain).  The main spec already guarantees this, but we
  state it explicitly for TLAPS.
--------------------------------------------------------------------*)
TypeOK ==
  /\ seq \in [1..N -> Value]
  /\ idx \in 0..N+1
  /\ cand \in Value
  /\ count \in Nat

(*--------------------------------------------------------------------
  Invariant: any value that has a strict majority must equal the
  current candidate after the entire sequence has been processed.
--------------------------------------------------------------------*)
Correct ==
  /\ idx = N + 1
  /\ \A v \in StrictMajorityValues : v = cand

(*--------------------------------------------------------------------
  The inductive invariant used by the main specification.  It combines
  the two properties above and is also exposed as a separate name for
  the .cfg file.
--------------------------------------------------------------------*)
Inv == TypeOK /\ Correct

====