---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

\* The Boyer-Moore majority vote model checking configuration: three concrete model
\* values, a bounded sequence length, and the main spec instantiated with them.
\* The .cfg expects this module to define EXACTLY the identifiers listed below.
CONSTANTS A, B, C, bound

SeqValues == {A, B, C}

VARIABLES seq, pos, cand, counter

vars == <<seq, pos, cand, counter>>

\* Sequences in this model are drawn from a bounded construction: each length from
\* zero up to the bound, so the state space stays finite for model checking.
BoundedSeq(n) == CHOOSE f \in [1..n -> SeqValues] : TRUE

TypeOK ==
  /\ seq \in UNION {BoundedSeq(n) : n \in 0..bound}
  /\ pos \in 1..(Len(seq) + 1)
  /\ cand \in SeqValues
  /\ counter \in 0..bound

Init ==
  /\ \E f \in UNION {BoundedSeq(n) : n \in 0..bound} :
       /\ seq' = f
       /\ pos' = 1
       /\ \E e \in SeqValues : cand' = e
  /\ counter' = 0

\* Boyer-Moore's three-case scan step: adopt a new candidate, or increment, or
\* decrement the counter, depending on the current element.
Step ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF counter = 0 THEN
         /\ cand' = x
         /\ counter' = 1
       ELSE IF x = cand THEN
         /\ counter' = counter + 1
       ELSE
         /\ counter' = counter - 1
  /\ pos' = pos + 1

Next == Step

Spec == Init /\ [][Next]_vars

\* Every true majority element must equal the candidate once the scan completes.
Correct ==
  \A v \in SeqValues : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq))
                        => (v = cand)

Inv ==
  /\ counter >= 0 /\ counter <= bound
  /\ pos >= 1 /\ pos <= Len(seq) + 1

\* The scan always eventually completes; weak fairness on the single step.
Complete ==
  WF_vars(Step)
  /\ (pos = Len(seq) + 1)

====