---- MODULE MCMajority ----
EXTENDS Integers, Functions, Sequences

CONSTANTS A, B, C, bound

\* A bounded sequence constructor: sequences of length up to bound over the
\* fixed three-element value set.  This replaces the infinite Seq from the
\* standard Sequences module so the model stays finite and checkable.
BoundedSeq == { f \in [1..n -> {A, B, C}] : n \in 0..bound }

VARIABLES seq, pos, cand, ct

vars == <<seq, pos, cand, ct>>

TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in 1..(bound + 1)
    /\ cand \in {A, B, C}
    /\ ct \in 0..bound

Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cand \in {A, B, C}
    /\ ct = 0

\* Three-way step of the Boyer-Moore scan: adopt a fresh candidate, increment,
\* or decrement the counter.
Next ==
    \/ \E s \in BoundedSeq :
        /\ seq' = s
        /\ pos' = 1
        /\ cand' = A
        /\ ct' = 0
    \/ \E v \in {A, B, C} :
        /\ pos <= Len(seq)
        /\ cand' = IF ct = 0 THEN v ELSE cand
        /\ ct' = IF seq[pos] = cand THEN ct + 1 ELSE (IF ct > 0 THEN ct - 1 ELSE 0)
        /\ pos' = pos + 1
        /\ seq' = seq

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Stronger claim: any true majority element must equal the candidate at the
\* end of a complete scan.  The weaker bound-equivalence converse is not true.
Correct == \A e \in {A, B, C} : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = e}) > Len(seq)) => e = cand

Inv == ct >= 0 /\ pos >= 1

EventuallyComplete == <>(pos > Len(seq))

\* The model checker is allowed to replace the standard Seq with BoundedSeq;
\* keep EXTENDS Sequences and do NOT declare Seq here.
====