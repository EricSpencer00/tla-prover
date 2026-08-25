---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

VARIABLES seq, pos, cand, cnt

ValueSet == {A, B, C}

(* Finite set of sequences over ValueSet whose length does not exceed the bound *)
(* A sequence is represented as a function whose domain is a subset of 1..bound.
   The length of the sequence is defined by Len (from Sequences), which works
   correctly for such functions. *)
BoundedSeq(b) ==
    { s \in [i \in 1..b -> ValueSet] : TRUE }

(* Initial state *)
Init ==
    /\ seq \in BoundedSeq(bound)
    /\ pos = 1
    /\ cnt = 0
    /\ cand \in ValueSet

(* Scan the next element of the sequence *)
Scan ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
       IF cnt = 0 THEN
          /\ cand' = x
          /\ cnt' = 1
          /\ pos' = pos + 1
       ELSE IF x = cand THEN
          /\ cand' = cand
          /\ cnt' = cnt + 1
          /\ pos' = pos + 1
       ELSE
          /\ cand' = cand
          /\ cnt' = cnt - 1
          /\ pos' = pos + 1
    /\ UNCHANGED seq

(* Stutter after the whole sequence has been scanned *)
Done ==
    /\ pos = Len(seq) + 1
    /\ UNCHANGED <<seq, cand, cnt, pos>>

Next == Scan \/ Done

Spec == Init /\ [][Next]_<<seq, cand, cnt, pos>>

(* Type correctness invariant *)
TypeOK ==
    /\ seq \in BoundedSeq(bound)
    /\ pos \in Nat
    /\ cnt \in Nat
    /\ cand \in ValueSet

(* Number of occurrences of element e in the current sequence *)
Count(e) ==
    Cardinality({ i \in DOMAIN seq : seq[i] = e })

(* Correctness: after a complete scan, any majority element equals the candidate *)
Correct ==
    (pos = Len(seq) + 1) =>
        \A e \in ValueSet :
            (Count(e) > Len(seq) \div 2) => cand = e

(* Simple inductive invariant *)
Inv ==
    /\ cnt \in Nat
    /\ pos \in 1..(Len(seq) + 1)
    /\ cand \in ValueSet

====