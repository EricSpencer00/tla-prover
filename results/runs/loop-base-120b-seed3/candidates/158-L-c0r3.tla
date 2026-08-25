---- MODULE Voting ----
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* Operators used by the .cfg file (substituted for the corresponding constants)
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* Basic definitions
\* ----------------------------------------------------------------------
Vote == [ballot : Ballot, value : Value]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES votes, threshold

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Safety predicate for a value at a given ballot
\* ----------------------------------------------------------------------
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( (\E w \in votes[a] : w.ballot = c /\ w.value = v)
                      \/ threshold[a] > c )

\* ----------------------------------------------------------------------
\* Action: increase promise threshold without voting
\* ----------------------------------------------------------------------
PromiseIncrease ==
    \E a \in Acceptor, b \in Ballot :
        /\ b > threshold[a]
        /\ threshold' = [threshold EXCEPT ![a] = b]
        /\ votes' = votes

\* ----------------------------------------------------------------------
\* Action: cast a vote
\* ----------------------------------------------------------------------
CastVote ==
    \E a \in Acceptor, b \in Ballot, v \in Value :
        /\ b >= threshold[a]                     \* respects current promise
        /\ \A w \in votes[a] : w.ballot # b       \* not already voted in b
        /\ \A a_ \in Acceptor :
               \A w2 \in votes[a_] :
                   (w2.ballot = b) => w2.value = v   \* no conflicting vote
        /\ Safe(v, b)                            \* value is safe at b
        /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
        /\ threshold' = [threshold EXCEPT ![a] = b]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == \/ PromiseIncrease
        \/ CastVote

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, threshold>>

\* ----------------------------------------------------------------------
\* Invariant: type correctness, safety of every vote, and at most one
\* value per ballot
\* ----------------------------------------------------------------------
OneValuePerBallot ==
    \A b \in Ballot :
        \A aA, aB \in Acceptor :
            \A w1 \in votes[aA], w2 \in votes[aB] :
                (w1.ballot = b /\ w2.ballot = b) => w1.value = w2.value

Inv ==
    /\ \A a \in Acceptor : threshold[a] >= -1
    /\ \A a \in Acceptor :
          \A w \in votes[a] :
              /\ w \in Vote
              /\ Safe(w.value, w.ballot)
    /\ OneValuePerBallot

\* ----------------------------------------------------------------------
\* Consistency property (no two different values can be chosen)
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
    ~(\E Q1, Q2 \in Quorum, vv1, vv2 \in Value, b1, b2 \in Ballot :
          /\ vv1 # vv2
          /\ (\A a \in Q1 :
                \E w \in votes[a] : w.ballot = b1 /\ w.value = vv1)
          /\ (\A a \in Q2 :
                \E w \in votes[a] : w.ballot = b2 /\ w.value = vv2))

\* ----------------------------------------------------------------------
\* Symmetry set (identity permutation)
\* ----------------------------------------------------------------------
Identity == [a \in Acceptor |-> a]
MCSymmetry == { Identity }

=============================================================================