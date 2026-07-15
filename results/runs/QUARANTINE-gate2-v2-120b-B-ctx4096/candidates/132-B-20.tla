---- MODULE MCMajority ----
EXTENDS Integers

CONSTANTS A, B, C, bound

(* The bound must be a natural number (including 0). *)
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* The Majority module is assumed to provide the actions Init and Next. *)
INSTANCE Majority

Init == /\ seq = {}
        /\ i   = 0
        /\ cand = {}
        /\ cnt  = 0

Next == \/ /\ i < bound
           /\ i'   = i + 1
           /\ seq' = [seq EXCEPT ![i'] = Choose x \in Value : TRUE]
           /\ cand' = IF cnt = 0 THEN seq'[i'] ELSE cand
           /\ cnt'  = IF cnt = 0 THEN 1
                     ELSE IF seq'[i'] = cand THEN cnt + 1
                     ELSE cnt - 1
        \/ /\ i = bound
           /\ UNCHANGED <<seq, i, cand, cnt>>

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* Invariant: if the counter is zero, there is no current candidate. *)
CandZeroInv == (cnt = 0) => (cand = {})

=============================================================================