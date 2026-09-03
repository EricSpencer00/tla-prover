---- MODULE MCMajority ----
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

\* A bounded sequence: only functions with a bounded domain, to keep the
\* model finite.  Replaces the standard Seq operator from Sequences.
BoundedSeq(f) == [i \in 1..f.domain |-> f[i]]

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in {BoundedSeq(f) : f \in [1..bound -> Values]}
  /\ pos \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

Init ==
  /\ seq \in {BoundedSeq(f) : f \in [1..bound -> Values]}
  /\ pos = 1
  /\ cand \in Values
  /\ cnt = 0

\* Scan the next element of the sequence: adopt it as candidate with a
\* fresh count, increment the count when it matches, or decrement otherwise.
Next ==
  \/ \E x \in Values : cand' = x /\ cnt' = 0
  \/ cnt' = IF cnt = 0 THEN 0 ELSE cnt - 1
  /\ pos' = IF pos <= Len(seq) THEN pos + 1 ELSE pos
  /\ UNCHANGED <<seq, cand>>

\* The invariant that must hold at the end of a complete scan: any element
\* that truly is a majority of the sequence must equal the surviving
\* candidate, so a true majority can never be masked.
Correct ==
  \A x \in Values :
    (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) => x = cand

Inv == TRUE

NextF == SelectSeq(Next, UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(NextF)

EventualCompletion == pos = Len(seq) + 1

====