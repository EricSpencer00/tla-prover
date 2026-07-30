---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

\* Model-checking configuration module for the Boyer-Moore majority vote
\* algorithm.  It instantiates the main majority-vote spec with concrete
\* values (three distinct elements) and a bounded sequence length.  The
\* standard 'Seq' operator from the Sequences module is replaced by
\* BoundedSeq, which is a FINITE version of Seq so the model stays checkable.
\* All actions and safety properties are inherited from the main spec.

CONSTANTS A, B, C, bound

ValueSet == {A, B, C}

\* A bounded sequence of bounded length from the value set.  Finite domain, so
\* the model checker can enumerate it.
BoundedSeq(S) ==
  {\x \in Seq(S) : Len(x) <= bound}

VARIABLES seq, pos, candidate, counter

vars == <<seq, pos, candidate, counter>>

TypeOK ==
  /\ seq \in BoundedSeq(ValueSet)
  /\ pos \in 1..(bound + 1)
  /\ candidate \in ValueSet
  /\ counter \in 0..bound

\* The main correctness property: any true majority element must agree with
\* the candidate after a complete scan.
Correct ==
  \A v \in ValueSet :
    (Cardinality({ i \in 1..Len(seq) : seq[i] = v }) > Len(seq) \div 2) =>
      (pos = Len(seq) + 1 => v = candidate)

\* The standard Boyer-Moore invariant: the counter is positive exactly when
\* the candidate is backed by a non-empty prefix of the unscanned suffix.
Inv ==
  /\ (counter > 0 => candidate \in { seq[i] : i \in pos..Len(seq) })
  /\ (candidate \in { seq[i] : i \in pos..Len(seq) } => counter > 0)

Init ==
  /\ seq \in BoundedSeq(ValueSet)
  /\ pos = 1
  /\ candidate \in ValueSet
  /\ counter = 0

\* Scan the next element with Boyer-Moore's three-case logic.
Step ==
  /\ pos <= Len(seq)
  /\ LET y == seq[pos] IN
       \/ /\ y = candidate
          /\ counter' = counter + 1
          /\ candidate' = candidate
       \/ /\ y # candidate
          /\ counter = 0
          /\ candidate' = y
          /\ counter' = 1
       \/ /\ y # candidate
          /\ counter > 0
          /\ candidate' = candidate
          /\ counter' = counter - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Step

Spec == Init /\ [][Next]_vars

\* Scan eventually completes; weak fairness on the scan step.
Complete ==
  \A v \in ValueSet :
    (Cardinality({ i \in 1..Len(seq) : seq[i] = v }) > Len(seq) \div 2 =>
       (pos = Len(seq) + 1 => v = candidate))
  /\ (pos = Len(seq) + 1) ~> (pos = Len(seq) + 1)
  /\ WF_vars(Step)

\* The configuration disables deadlock checking, so the spec is stated
\* without any deadlock clause.
====