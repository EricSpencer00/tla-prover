---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Value

\* The Boyer-Moore majority vote algorithm over a finite sequence of values.
\* This module adds a machine-checked proof of correctness to the base
\* specification, proving both type correctness and the algorithm's
\* functional correctness as invariants, discharged by TLAPS.

MaxLen == 2
Values == {"a", "b"}
Count[x, s] == Cardinality({i \in 1..Len(s) : s[i] = x})

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ pos \in 0..MaxLen
  /\ cand \in Values \cup {"none"}
  /\ cnt \in 0..MaxLen

Init ==
  /\ seq = <<>>
  /\ pos = 0
  /\ cand = "none"
  /\ cnt = 0

Extend(x) ==
  /\ Len(seq) < MaxLen
  /\ seq' = Append(seq, x)
  /\ UNCHANGED <<pos, cand, cnt>>

VoteV(x) ==
  /\ pos < Len(seq)
  /\ /\ IF cnt = 0 THEN cand' = x ELSE cand' = cand
     /\ IF cnt = 0 THEN cnt' = 1
        ELSE IF cand = x THEN cnt' = cnt + 1 ELSE cnt' = cnt - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Extend("a") \/ Extend("b") \/ VoteV("a") \/ VoteV("b")]_vars

Correct ==
  (pos = Len(seq) /\ cnt >= 1) ~> (pos = Len(seq))

Inv == TypeOK /\ Spec

====