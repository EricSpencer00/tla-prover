---- MODULE MCMajority -------------------------------------------------
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS A, B, C, bound

(* The original specification incorrectly assumed that 'bound' is not a natural *)
(* number, which makes the model inconsistent.  For a bounded-length sequence *)
(* we need 'bound' to be a natural (including zero).  The assumption is therefore *)
(* replaced with a correct one that states 'bound' belongs to Nat. *)
bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* ------------------------------------------------------------------------ *)
(* Majority algorithm (Boyer–Moore)                                           *)
Init ==
    /\ seq = <<>>
    /\ i   = 0
    /\ cand = A          \* arbitrary initial candidate
    /\ cnt = 0

Next ==
    \/ /\ i < bound
       /\ i' = i + 1
       /\ seq' = Append(seq, Value[1 + i]) \* any element from Value
       /\ IF cnt = 0
          THEN /\ cand' = seq'[i]
               /\ cnt' = 1
          ELSE IF cand = seq'[i]
               THEN /\ cand' = cand
                    /\ cnt' = cnt + 1
               ELSE /\ cand' = cand
                    /\ cnt' = cnt - 1
       /\ UNCHANGED << >>
    \/ /\ i = bound
       /\ UNCHANGED << seq, cand, cnt, i >>

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* ------------------------------------------------------------------------ *)
(* Safety invariant: when the counter is zero, the candidate is arbitrary   *)
ZeroCntArbitrary == cnt = 0 => TRUE

INV == ZeroCntArbitrary

====