---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Operators that the .cfg file will substitute
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, prom

\* -----------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ prom  = [a \in Acceptor |-> -1]

\* -----------------------------------------------------------------
\* Safety predicate for a vote (b, val)
\* -----------------------------------------------------------------
Safe(b, val) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    (<<c, val>> \in votes[a]) \/ (prom[a] > c)

\* -----------------------------------------------------------------
\* Action: an acceptor raises its promise threshold
\* -----------------------------------------------------------------
IncreasePromise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > prom[a]
    /\ prom' = [prom EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* -----------------------------------------------------------------
\* Action: an acceptor votes for (b, val)
\* -----------------------------------------------------------------
Vote(a, b, val) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ val \in Value
    /\ b >= prom[a]                                 \* not below current promise
    /\ ~(\E v' \in Value : <<b, v'>> \in votes[a])  \* hasn't voted in this ballot yet
    /\ \A a2 \in Acceptor :
          ( \E v2 \in Value : <<b, v2>> \in votes[a2] )
          => ( \A v2 \in Value :
                  (<<b, v2>> \in votes[a2]) => v2 = val )
    /\ \E Q \in Quorum :
          \A a' \in Q :
              (<<b, val>> \in votes[a']) \/ (prom[a'] > b)   \* safety quorum
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, val>>}]
    /\ prom'  = [prom  EXCEPT ![a] = b]

\* -----------------------------------------------------------------
\* Next-state relation
\* -----------------------------------------------------------------
Next ==
    \/ \E a \in Acceptor, b \in Ballot : IncreasePromise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, val \in Value : Vote(a, b, val)

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, prom>>

\* -----------------------------------------------------------------
\* Invariant
\* -----------------------------------------------------------------
Inv ==
    /\ \A a \in Acceptor : prom[a] \in Int
    /\ \A a \in Acceptor : votes[a] \subseteq (Ballot \X Value)
    /\ \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
          (<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2]) => v1 = v2
    /\ \A a \in Acceptor, <<b, v>> \in votes[a] : Safe(b, v)

\* -----------------------------------------------------------------
\* Chosen values and the consensus property
\* -----------------------------------------------------------------
Chosen ==
    { v \in Value :
        \E Q \in Quorum :
            \A a \in Q :
                \E b \in Ballot : <<b, v>> \in votes[a] }

ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (v1 \in Chosen /\ v2 \in Chosen) => v1 = v2

\* -----------------------------------------------------------------
\* Symmetry set (a set of permutations on Acceptor)
\* -----------------------------------------------------------------
MCSymmetry ==
    {
        [a \in Acceptor |-> a],
        [a \in Acceptor |-> 
            IF a = a1 THEN a2
            ELSE IF a = a2 THEN a1
            ELSE a]
    }

=============================================================================