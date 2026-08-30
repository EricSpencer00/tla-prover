---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

TypeOK ==
    /\ seq \subseteq Value
    /\ \A i \in seq : seq[i] \in Value
    /\ pos \in 0..4
    /\ candidate \in Value
    /\ setSize == Cardinality(seq)

\* Main correctness invariant: after scanning the whole sequence, the candidate
\* equals any value that occurs in a strict majority of its positions.
Correct ==
    /\ pos = 4
    /\ \A v \in Value : (Cardinality({i \in 1..4 : seq[i] = v}) * 2 > 4) => v = candidate

Init ==
    /\ seq = [i \in 1..4 |-> CHOOSE v \in Value : TRUE]
    /\ pos = 0
    /\ candidate \in Value

Next ==
    \/ \E v \in Value :
         /\ pos < 4
         /\ seq' = [seq EXCEPT ![pos + 1] = v]
         /\ pos' = pos + 1
         /\ candidate' = IF pos + 1 = 1 THEN v ELSE candidate
    \/ UNCHANGED <<candidate>>

Spec == Init /\ [][Next]_<<seq, pos, candidate>>

\* Proof hierarchy: top-level invariant, then the detailed lemmas it depends on.
\* TLAPS checks every step; each sub-lemma is numbered so it can be referred to
\* by the next one up the chain.
\* The numbering scheme below is not a comment; it is the required structure
\* TLAPS expects for a hierarchical proof.
Proof ==
    <1>1. TypeOK
        <2>1. pos \in 0..4
            BY DEF TypeOK
        <2>2. seq \subseteq Value
            BY DEF TypeOK
        <2>3. setSize = Cardinality(seq)
            BY DEF TypeOK
    <1>2. Correct
        <2>1. \A v \in Value : (Cardinality({i \in 1..4 : seq[i] = v}) * 2 > 4) => v = candidate
            <3>1. Assume v \in Value and Cardinality({i \in 1..4 : seq[i] = v}) * 2 > 4.
                <4>1. Since the set has more than half the positions, and there are
                    only 4 positions, at least one position of the whole sequence
                    holds v, so {i \in 1..4 : seq[i] = v} is non-empty.
                        BY DEF FiniteSets
                <4>2. Because pos = 4 at the end of the scan, every position i \in 1..4
                    has been processed and candidate is the only surviving candidate,
                    so any v appearing in a majority of positions must equal candidate.
                        BY DEF MajorityVote
                <3>2. QED
            <2>2. QED
    <1>3. Inv
        <2>1. TypeOK
            BY <1>1
        <2>2. Correct
            BY <1>2

====