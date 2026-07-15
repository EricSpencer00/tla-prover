---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANT Value

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Values == {v \in Value : TRUE}

(*-----------------------------------------------------------------
  Derived from the main Boyer-Moore majority vote specification.
  We re‑declare the state variables and the transition relation
  here to make the module self‑contained while preserving the
  required identifiers.
-----------------------------------------------------------------*)
VARIABLES index, candidate, count, seq

(* seq is a finite sequence of elements from the set Value.
   The length of the sequence is called Len. *)
Len == Len(seq)

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ index = 0
    /\ candidate \in Values
    /\ count = 0
    /\ seq \in Seq(Values)
    /\ Len > 0            \* non‑empty sequence for the algorithm to be meaningful

(*-----------------------------------------------------------------
  Transition relation (Next)
-----------------------------------------------------------------*)
Next ==
    \/ /\ index < Len
       /\ LET x == seq[index + 1] IN
          IF count = 0 THEN
              /\ candidate' = x
              /\ count' = 1
          ELSE IF candidate = x THEN
              /\ candidate' = candidate
              /\ count' = count + 1
          ELSE
              /\ candidate' = candidate
              /\ count' = count - 1
       /\ index' = index + 1
       /\ UNCHANGED seq
    \/ /\ index = Len
       /\ UNCHANGED <<index, candidate, count, seq>>

Spec == Init /\ [][Next]_<<index, candidate, count, seq>>

(*-----------------------------------------------------------------
  Type correctness invariant (TypeOK)
-----------------------------------------------------------------*)
TypeOK ==
    /\ index \in Nat
    /\ index <= Len
    /\ candidate \in Values
    /\ count \in Nat
    /\ seq \in Seq(Values)

(*-----------------------------------------------------------------
  Occurrence counting function
-----------------------------------------------------------------*)
Occur(v) == Cardinality({ i \in 1..Len : seq[i] = v })

(*-----------------------------------------------------------------
  Majority predicate
-----------------------------------------------------------------*)
Majority(v) == Occur(v) > Len / 2

(*-----------------------------------------------------------------
  Correctness invariant (Correct)
  After the whole sequence has been processed (index = Len),
  any element that appears in a strict majority must be the
  current candidate.
-----------------------------------------------------------------*)
Correct == 
    (index = Len) => \A v \in Values : Majority(v) => v = candidate

(*-----------------------------------------------------------------
  Inductive invariant (Inv) – the invariant used by the original
  Boyer‑Moore algorithm.  It relates the current candidate and count
  to the existence of a majority element in the processed prefix.
-----------------------------------------------------------------*)
Inv ==
    /\ (count = 0) => (\E v \in Values : candidate = v)
    /\ (count > 0) => 
          (\E v \in Values :
                /\ candidate = v
                /\ \A u \in Values :
                       (Occur(u) > index / 2) => u = v)

=============================================================================