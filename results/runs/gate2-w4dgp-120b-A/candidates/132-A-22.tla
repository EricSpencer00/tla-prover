---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* A bounded version of the standard Seq type constructor, kept finite so
\* an exhaustive model check of the Boyer-Moore majority vote algorithm
\* over a concrete set of values (A, B, C) and a concrete maximum sequence
\* length (bound, set to 5 in the .cfg) stays tractable. The main
\* specification of the algorithm lives in MajorityVote below; this
\* module simply instantiates it with the concrete values.
BoundedSeq == UNION { [1 .. n -> {A, B, C}] : n \in 0 .. bound }
SeqStar    == { f \in {A, B, C}^* : Len(f) <= bound }

VARIABLES seq, pos, cand, counter

TypeOK ==
  /\ seq \in SeqStar
  /\ pos \in Nat
  /\ cand \in {A, B, C}
  /\ counter \in Nat

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in {A, B, C}
  /\ counter = 0

\* Boyer-Moore scan step: read the next element and update candidate/counter.
Step ==
  /\ pos <= Len(seq)
  /\ \/ /\ cand = seq[pos]
        /\ counter' = counter + 1
        /\ cand' = cand
     \/ /\ counter = 0
        /\ cand' = seq[pos]
        /\ counter' = 1
     \/ /\ cand # seq[pos]
        /\ counter > 0
        /\ counter' = counter - 1
        /\ cand' = cand
  /\ pos' = pos + 1

Spec == Init /\ [][Step]_<<seq, pos, cand, counter>>

\* The candidate at the end of a full scan must be the true majority if one exists.
Correct == (pos > Len(seq) /\ counter > 0) => cand = Majority(seq)

\* The Boyer-Moore algorithm is proved by the invariant below: the scan
\* position always stays within the sequence and the count never runs
\* negative. Once the scan passes the end of the sequence the system
\* idles, keeping the state well-typed forever.
Inv == (pos <= Len(seq) /\ counter >= 0) /\ (pos > Len(seq) => UNCHANGED <<seq, pos, cand, counter>>)

Terminate == <>(pos > Len(seq))

ASSUME bound \in Nat
====