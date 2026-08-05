---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

(* Model-checking configuration for the Boyer-Moore majority vote algorithm.  The  *)
(* three constant values below are the distinct elements that sequences may  *)
(* contain; bound is the maximum sequence length.  Sequences are taken from a   *)
(* FINITE bounded set rather than the full infinite Sequences domain, so the  *)
(* model stays small enough for exhaustive checking (the configuration     *)
(* replaces the standard Seq operator with this bounded version).           *)

CONSTANTS A, B, C, bound

Values == {A, B, C}

VARIABLES seq, pos, cand, cnt

TypeOK ==
  /\ seq \in BoundedSeq(Values, bound)
  /\ pos \in 1..(Len(seq) + 1)
  /\ cand \in Values
  /\ cnt \in 0..3

Init ==
  /\ \E s \in BoundedSeq(Values, bound) : seq = s
  /\ pos = 1
  /\ \E x \in Values : cand = x
  /\ cnt = 0

\* Boyer-Moore scan: the counter is only ever incremented up to its bound, so the
\* state space stays finite even though the scan repeats for every new element.
Step ==
  \/ pos <= Len(seq)
       /\ cnt' = IF cnt < 3 THEN cnt + 1 ELSE cnt
       /\ cand' = seq[pos]
       /\ pos' = pos + 1
  \/ pos <= Len(seq)
       /\ seq[pos] = cand
       /\ cnt' = IF cnt < 3 THEN cnt + 1 ELSE cnt
       /\ cand' = cand
       /\ pos' = pos + 1
  \/ pos <= Len(seq)
       /\ seq[pos] # cand
       /\ cnt > 0
       /\ cnt' = cnt - 1
       /\ cand' = cand
       /\ pos' = pos + 1

Next == Step

\* The true majority, if any, must be the value the scan ends up holding.
Correct ==
  \A x \in Values : (2 * (Cardinality({ i \in 1..Len(seq) : seq[i] = x })) > Len(seq))
                      => x = cand

Inv ==
  \A x \in Values : (2 * (Cardinality({ i \in 1..Len(seq) : seq[i] = x })) > Len(seq))
                      => x = cand

Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>> /\ WF_vars(Step)

ScanCompletes == <>(pos = Len(seq) + 1)

\* Sequences of exactly length n: the usual approach with a UNION over the length
\* bound, so the model checker can enumerate them concretely.
BoundedSeq(S, n) == UNION { (S) ^ (n) : n \in 0..n }

====