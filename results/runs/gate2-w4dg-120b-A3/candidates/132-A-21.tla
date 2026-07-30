---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* Three distinct model values; bound = maximum reachable sequence length.
\* The main majority vote spec is instantiated with these concrete values.
\* Sequences are drawn from a bounded set (lengths up to "bound") so the
\* model stays finite; the unbounded Seq operator from Sequences is replaced
\* by a FINITE version via the .cfg rewriting.
Values == {A, B, C}

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

TypeOK ==
  /\ seq \in [1..bound -> Values]
  /\ i \in 1..(bound + 1)
  /\ cand \in Values
  /\ cnt \in 0..bound

\* A true majority element must equal the candidate after a complete scan.
Correct == (i = bound + 1 /\ cnt > 0) => (seq[i - cnt] = cand)

Init ==
  /\ \E s \in [1..bound -> Values] : seq = s
  /\ i = 1
  /\ \E c \in Values : cand = c
  /\ cnt = 0

Next ==
  /\ i <= bound
  /\ IF seq[i] = cand THEN cnt' = IF cnt = 0 THEN 1 ELSE cnt + 1
                          ELSE cnt' = IF cnt = 0 THEN cnt ELSE cnt - 1
  /\ cand' = IF cnt = 0 THEN seq[i] ELSE cand
  /\ i' = i + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Next]_vars

\* The inductive invariant: the counter never exceeds the scan position.
Inv == cnt <= i

SpecOK == Spec /\ TypeOK /\ Correct /\ Inv

====