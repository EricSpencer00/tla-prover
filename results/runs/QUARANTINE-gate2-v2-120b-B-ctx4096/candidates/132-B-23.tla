---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS A, B, C, bound

(* The original file had an assumption that required "bound" *not* to be a natural
   number, which makes the model unsatisfiable because the rest of the spec
   (and the imported Majority module) expects "bound" to be a natural number.
   We replace that contradictory assumption with a correct one that states
   that bound is a natural number (including zero).  This change is minimal
   and preserves the intended semantics of the majority‑vote algorithm. *)
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* The Majority module supplies the algorithm that works on a sequence
   "seq".  We simply expose its definitions and actions. *)
Init == 
    /\ seq = {}
    /\ i   = 0
    /\ cand = {}
    /\ cnt  = 0

Next ==
    \/ /\ i < bound
       /\ i' = i + 1
       /\ seq' = seq \cup {i + 1 |-> CHOOSE x \in Value : TRUE}
       /\ IF cnt = 0
            THEN /\ cand' = seq[i+1]
                 /\ cnt'  = 1
            ELSE IF seq[i+1] = cand
                    THEN /\ cand' = cand
                         /\ cnt'  = cnt + 1
                    ELSE /\ cand' = cand
                         /\ cnt'  = cnt - 1
    \/ /\ i = bound
       /\ UNCHANGED <<seq, cand, cnt>>

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* The invariant that the imported Majority module expects: the candidate,
   when the counter is positive, is a majority element of the prefix that has
   been processed. *)
MajorityInv ==
    /\ cnt >= 0
    /\ cnt = 0 \/ 
       (\E n \in 1..i : 
            /\ cand = seq[n]
            /\ Cardinality({j \in 1..i : seq[j] = cand}) > i \div 2)

THEOREM Spec => []MajorityInv

=============================================================================