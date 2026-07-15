---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT Value

VARIABLES s, cand, count

(* ----------------------------------------------------------------------
   Imported main specification (simplified here for completeness)
   ---------------------------------------------------------------------- *)

(* The input sequence is represented by the immutable scalar 's'.
   For the purposes of this module we assume it is a total function
   from the set {1, 2, ..., N} to Value, where N is the length of the
   sequence.  The length N is taken implicitly as the maximum index
   in the domain of s. *)

(* Candidate and counter variables are introduced in the main spec.
   'cand' holds the current candidate value (an element of Value) or
   a special NONE value indicating no candidate yet.  'count' is an
   integer counter representing the net votes for the current candidate. *)

\* NONE is used to denote the absence of a candidate
\* In the main spec, NONE is typically represented as a special element
\* of Value, but we model it explicitly here for clarity.
CONST NONE

(* Initial state: no candidate and zero count, sequence is fixed *)
Init ==
    /\ s \in [1..Len(s) -> Value]
    /\ cand = NONE
    /\ count = 0

(* Action: Process the next element (index i) of the sequence *)
Next ==
    /\ \E i \in 1..Len(s) : i = IF count = 0 THEN 1 ELSE i + 1
    /\ IF count = 0 THEN
           /\ cand' = s[i]
           /\ count' = 1
       ELSE
           IF s[i] = cand THEN
               /\ count' = count + 1
               /\ cand' = cand
           ELSE
               /\ count' = count - 1
               /\ cand' = cand

Spec == Init /\ [][Next]_<<cand, count, s>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)

(* TypeOK: All variables maintain their declared types. *)
TypeOK ==
    /\ s \in [1..Len(s) -> Value]
    /\ cand \in Value \cup {NONE}
    /\ count \in Integers

(* Correct: If after processing the entire sequence a value occurs
   in a strict majority, then it must be equal to the final candidate. *)
Correct ==
    \E majorityVal \in Value :
        /\ OccursInMajority(majorityVal, s)
        /\ cand = majorityVal

(* Auxiliary function: count occurrences of a value in the sequence. *)
CountOccurrences(v) ==
    Len(Subset({i \in 1..Len(s) : s[i] = v}))

(* Helper predicate: does value v occur in a strict majority? *)
OccursInMajority(v, seq) ==
    CountOccurrences(v) > Len(seq) / 2

(* Inv: The invariant maintained by the main specification. *)
Inv ==
    TypeOK /\ Correct

(* ----------------------------------------------------------------------
   TLAPS proof obligations (sketch)
   ---------------------------------------------------------------------- *)

THEOREM TypeOKInit ==
    Init => TypeOK

THEOREM TypeOKPreserved ==
    \A i \in {cand, count, s} : [i]_<<cand, count, s>> => TypeOK

THEOREM CorrectInit ==
    Init => Correct

THEOREM CorrectPreserved ==
    Correct /\ Next => Correct

Spec == Init /\ [][Next]_<<cand, count, s>>
====