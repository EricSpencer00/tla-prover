---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

\* ---------- Constants ----------
CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Concrete definitions (may be overridden by .cfg)
Acceptor == {a1, a2, a3}
Value    == {v1, v2}
\* Example quorums with the required overlap property
Quorum   == { {a1, a2}, {a2, a3}, {a1, a3} }
\* Ballot numbers are natural numbers (the model checker can restrict this)
Ballot   == Nat

\* ---------- MC (model‑checking) wrappers ----------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ---------- State ----------
VARIABLES votes, threshold

\* votes[a] is the set of <<b, v>> pairs that acceptor a has cast
\* threshold[a] is the smallest ballot number in which a will vote
\* we use -1 to denote “no promise made yet”
InitThresh == -1

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> InitThresh]

\* ---------- Safety predicate ----------
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    (<<c, v>> \in votes[a]) \/ (c < threshold[a])

\* ---------- Actions ----------
IncreasePromise ==
    \E a \in Acceptor, b \in Ballot :
        /\ b > threshold[a]
        /\ votes' = votes
        /\ threshold' = [threshold EXCEPT ![a] = b]

Vote ==
    \E a \in Acceptor, b \in Ballot, v \in Value :
        /\ b >= threshold[a]                                    \* respects current promise
        /\ ~(\E pair \in votes[a] : pair[1] = b)                \* hasn't voted in this ballot yet
        /\ \A a2 \in Acceptor :
               a2 # a =>
               \A pair \in votes[a2] :
                   IF pair[1] = b THEN pair[2] = v ELSE TRUE   \* no different value in same ballot
        /\ Safe(v, b)                                           \* value is safe at b
        /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
        /\ threshold' = [threshold EXCEPT ![a] = b]

Next == \/ IncreasePromise
        \/ Vote

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<votes, threshold>>

\* ---------- Invariant ----------
Inv ==
    /\ \A a \in Acceptor : votes[a] \subseteq Ballot \X Value
    /\ \A a \in Acceptor : threshold[a] \in Ballot \cup {-1}
    /\ \A a \in Acceptor, pair \in votes[a] :
           LET b == pair[1] IN
           LET v == pair[2] IN
               Safe(v, b)
    /\ \A b \in Ballot :
        \A a1, a2 \in Acceptor :
            ( (\E v1 : <<b, v1>> \in votes[a1]) /\ (\E v2 : <<b, v2>> \in votes[a2]) )
            => (\A v1, v2 :
                    (<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2])
                    => v1 = v2)

\* ---------- Consensus property ----------
ConsensusSpecBar ==
    \A b1, b2 \in Ballot,
       Q1, Q2 \in Quorum,
       v1, v2 \in Value :
        ( (\A a \in Q1 : <<b1, v1>> \in votes[a]) /\ (\A a \in Q2 : <<b2, v2>> \in votes[a]) )
        => v1 = v2

\* ---------- Symmetry ----------
\* Identity permutation (satisfies the required type)
MCSymmetry == { [a \in Acceptor |-> a] }

====