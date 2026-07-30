---- MODULE MCMajority ----
EXTENDS Naturals

CONSTANTS A, B, C, bound, Seq

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

\* A bounded sequence is a function from 1..n to the value set, with n in 0..bound;
\* this keeps the state space finite for model checking.
SeqBounded == {s \in [1..bound -> {A, B, C}] : TRUE}

TypeOK ==
  /\ seq \in SeqBounded
  /\ i \in 1..(bound + 1)
  /\ cand \in {A, B, C}
  /\ cnt \in 0..bound

Init ==
  /\ seq \in SeqBounded
  /\ i = 1
  /\ cand \in {A, B, C}
  /\ cnt = 0

Next ==
  \/ (\E c \in {A, B, C} :
        /\ i <= bound
        /\ cand' = c
        /\ i' = i + 1
        /\ cnt' = IF cnt = 0 THEN 1 ELSE cnt + 1
        /\ UNCHANGED seq)
  \/ (\E c \in {A, B, C} :
        /\ i <= bound
        /\ cnt > 0
        /\ seq[i] = cand
        /\ cand' = c
        /\ i' = i + 1
        /\ cnt' = IF cnt = 0 THEN 1 ELSE cnt + 1
        /\ UNCHANGED seq)
  \/ (\E c \in {A, B, C} :
        /\ i <= bound
        /\ cnt > 0
        /\ seq[i] # cand
        /\ cand' = c
        /\ i' = i + 1
        /\ cnt' = cnt - 1
        /\ UNCHANGED seq)

Spec == Init /\ [][Next]_vars
        /\ \A c \in {A, B, C} : WF_vars(Next)

Correct ==
  \A c \in {A, B, C} :
    /\ (\A j \in 1..bound : seq[j] = c)
    => (i > bound => cand = c)

Inv ==
  \A c \in {A, B, C} :
    /\ (cand = c /\ i > bound) => (\A j \in 1..bound : seq[j] = c)

\* The scan always eventually completes, under weak fairness.
Complete == <>(i > bound)

SpecIFICATION == Spec
INVARIANTS == TypeOK, Correct, Inv
PROPERTIES == Complete

\* The bound is a natural number; this is the only additional assumption.
\* Deadlock checking is disabled in the model configuration.
BoundConsistent == bound \in Nat

====