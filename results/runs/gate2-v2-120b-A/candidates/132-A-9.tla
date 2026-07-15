---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound, Seq

(* The set of possible element values *)
Values == {A, B, C}

(* ----------------------------------------------------------------------
   State variables (inherited from the main majority vote specification)
   ---------------------------------------------------------------------- *)
VARIABLES seq, n, pos, cand, cnt

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

(* BoundedSeq constructs the set of all finite sequences over Values
   whose length is between 0 and bound, inclusive. *)
BoundedSeq == { s \in Seq : 
                 Len(s) \in 0..bound 
                 /\ DOMAIN s = 1..Len(s) 
                 /\ \A i \in DOMAIN s : s[i] \in Values }

(* ----------------------------------------------------------------------
   Initial predicate
   ---------------------------------------------------------------------- *)
Init ==
    /\ seq \in BoundedSeq
    /\ n = Len(seq)
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

(* ----------------------------------------------------------------------
   State transition (NEXT)
   ---------------------------------------------------------------------- *)
Next ==
    \/ /\ pos <= n
       /\ LET x == seq[pos] IN
          IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt' = 1
          ELSE IF cand = x THEN
              /\ cnt' = cnt + 1
          ELSE 
              /\ cnt' = cnt - 1
    /\ pos' = pos + 1
    /\ UNCHANGED <<seq, n>>
    \/ /\ pos > n
       /\ UNCHANGED <<seq, n, pos, cand, cnt>>

(* ----------------------------------------------------------------------
   Specification (temporal formula)
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<seq, n, pos, cand, cnt>>

(* ----------------------------------------------------------------------
   Invariant definitions (as required by the .cfg)
   ---------------------------------------------------------------------- *)

(* Type correctness: all variables stay within their intended domains *)
TypeOK ==
    /\ seq \in BoundedSeq
    /\ n = Len(seq)
    /\ pos \in 0..(n+1)
    /\ cand \in Values
    /\ cnt \in 0..n

(* Correctness property: if an element appears more than n/2 times in seq,
   then after the scan completes (pos > n) that element must equal cand. *)
Correct ==
    ( \E x \in Values : 
        ( Cardinality({ i \in 1..n : seq[i] = x }) > n/2 )
      ) => 
    ( pos > n => cand = 
        CHOOSE x \in Values :
            Cardinality({ i \in 1..n : seq[i] = x }) > n/2 )

(* Inductive invariant used by the original specification *)
Inv ==
    /\ cnt >= 0
    /\ cnt <= n
    /\ (cnt = 0 => cand \in Values)

(* ----------------------------------------------------------------------
   Liveness property (optional, not listed as an invariant)
   ---------------------------------------------------------------------- *)
ScanCompleted == <> (pos > n)

=============================================================================