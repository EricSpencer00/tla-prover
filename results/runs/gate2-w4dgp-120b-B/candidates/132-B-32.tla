---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \in Nat

Value == {A,B,C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

INSTANCE Majority

vars == <<seq, i, cand, cnt>>
Init == /\ seq = <<>>
        /\ i = 0
        /\ cand = A
        /\ cnt = 0
Next == \/ \E x \in Value : seq' = [seq EXCEPT ![i+1] = x]
                    /\ i' = i + 1 /\ cand' = cand /\ cnt' = cnt
             \/ \E c \in Value : cand' = c
                    /\ i' = i /\ seq' = seq /\ cnt' = cnt
             \/ \E n \in 1 .. i : cnt' = IF seq[n] = cand THEN cnt + 1 ELSE cnt
                    /\ i' = i /\ seq' = seq /\ cand' = cand
Spec == Init /\ [][Next]_vars

\* Any majority vote in the prefix is exactly the maintained candidate.
MajorityMatchesCandidate ==
  \A n \in 1 .. bound : (\A c \in Value : (2 * Cardinality({i \in 1 .. n : seq[i] = c}) > n) => cand = c)

====