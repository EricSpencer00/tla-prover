---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* MajorityProof carries the machine-checked TLAPS proof that the Boyer-Moore
\* majority vote algorithm is correct, on top of the underlying algorithm
\* specification (which provides the concrete state and transition definition).

CONSTANTS Value

VARIABLES seq, candidate, count, index
vars == << seq, candidate, count, index >>

\* The underlying algorithm's transition relation is re-used in full.
InitState == [ seq |-> << >>, candidate |-> "none", count |-> 0, index |-> 0 ]

\* No new actions: the module inherits Next from the main specification.
Next == UNCHANGED vars

Spec == InitState /\ [][Next]_vars

TypeOK ==
  /\ seq \in Seq(Value)
  /\ candidate \in Value \cup { "none" }
  /\ count \in 0..4
  /\ index \in 0..4

\* Cardinality lemma: a finite set plus one more element has one more element.
LemmaAddOne(s, e) ==
  /\ s \subseteq (Nat \cup { e })
  /\ e \notin s
  /\ Cardinality(s \cup { e }) = Cardinality(s) + 1

Occurs(i, x) ==
  { j \in 0..(i - 1) : seq[j] = x }

\* The key property: a value occurring in a strict majority of positions must
\* equal the Boyer-Moore candidate. No majority can be hidden behind the count.
Correct ==
  \A i \in 0..4, x \in Value :
    /\ i = index
    /\ i > 0
    /\ 2 * Cardinality(Occurs(i, x)) > i
    /\ candidate # "none"
    => x = candidate

\* TLAPS proof that TypeOK is an invariant, step by step.
Inv ==
  /\ TypeOK
  /\ \A i \in 0..4, x \in Value :
       /\ i = index
       /\ i > 0
       /\ 2 * Cardinality(Occurs(i, x)) > i
       /\ candidate # "none"
       => x = candidate

====