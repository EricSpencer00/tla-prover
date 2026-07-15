---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound, Seq

(* The finite set of possible element values. *)
Values == {A, B, C}

(* The domain used for indexed sequences. *)
Domain == 1 .. bound

(* BoundedSeq is the set of all finite sequences (functions from a prefix of 1..bound) 
   over Values whose length does not exceed 'bound'. *)
BoundedSeq == { s \in [Domain -> Values] :
                  \A i \in 1 .. bound :
                     (i \in DOMAIN s) => s[i] \in Values }

VARIABLES seq, pos, cand, cnt

(* Initial state: choose any bounded sequence, start scanning at position 1,
   choose an initial candidate nondeterministically, and set the counter to 0. *)
Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

(* Helper: true equality for Values (sets are disjoint). *)
CandEq(x) == cand = x

(* Action to process the next element of the sequence, if any. *)
Next ==
    \/ /\ pos <= Len(seq)
       /\ LET cur == seq[pos] IN
          /\ IF cnt = 0 THEN
                /\ cand' = cur
                /\ cnt' = 1
             ELSE IF CandEq(cur) THEN
                /\ cnt' = cnt + 1
                /\ UNCHANGED cand
             ELSE
                /\ cnt' = cnt - 1
                /\ UNCHANGED cand
          /\ pos' = pos + 1
          /\ UNCHANGED seq
    \/ /\ pos > Len(seq)            \* scan already complete
       /\ UNCHANGED <<seq, pos, cand, cnt>>

(* The overall behavior of the system. *)
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

(* Type correctness invariant. *)
TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

(* Main correctness property:
   If there exists a strict majority element in the full sequence,
   then after the scan finishes the candidate equals that element. *)
Correct ==
    \A v \in Values :
        (2 * Cardinality({ i \in 1 .. Len(seq) : seq[i] = v }) > Len(seq))
        => (pos > Len(seq) /\ cand = v)

(* Inductive invariant that is useful for model checking. *)
Inv ==
    /\ TypeOK
    /\ (pos > Len(seq) => \E v \in Values :
            (2 * Cardinality({ i \in 1 .. Len(seq) : seq[i] = v }) > Len(seq))
            /\ cand = v)

=============================================================================