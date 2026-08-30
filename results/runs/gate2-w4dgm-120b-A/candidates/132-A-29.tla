---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

ASSUME bound \in Nat

SeqValues == {A, B, C}
AllSeqs == UNION { [1..n -> SeqValues] : n \in 0..bound }

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
    /\ seq \in AllSeqs
    /\ pos \in 0..bound
    /\ cand \in SeqValues \cup {"none"}
    /\ count \in 0..bound

Init ==
    /\ seq \in AllSeqs
    /\ pos = 1
    /\ cand \in SeqValues \cup {"none"}
    /\ count = 0

Process ==
    /\ pos <= Len(seq)
    /\ IF cand = "none" THEN
        /\ cand' = seq[pos]
        /\ count' = 1
    ELSE IF seq[pos] = cand THEN
        /\ count' = count + 1
    ELSE
        /\ count' = count - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Done ==
    /\ pos > Len(seq)
    /\ UNCHANGED <<seq, pos, cand, count>>

Next == Process \/ Done

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Process)

\* The candidate a true majority beats to must be the majority itself.
Correct ==
    \A e \in SeqValues :
        /\ Cardinality({i \in 1..Len(seq): seq[i] = e}) * 2 > Len(seq)
        /\ cand = e

\* A majority vote counter that never reaches consensus on a minority must end
\* up at zero, so no losing candidate can be left carrying votes.
Inv ==
    \/ (count = 0 /\ cand = "none")
    \/ (count > 0 /\ cand \in SeqValues)

BoundedSeq(T) == T

====