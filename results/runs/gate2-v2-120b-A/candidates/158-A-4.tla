---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    a1,          \* a distinguished acceptor (used only as a placeholder constant)
    Acceptor,    \* the set of all acceptors
    Value,       \* the set of all values that may be chosen
    Quorum,      \* the collection of quorum sets, each a subset of Acceptor
    Ballot       \* the set of ballot numbers (natural numbers, bounded in the .cfg)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    votes,        \* [a \in Acceptor |-> SUBSET ({[b \in Ballot |-> v \in Value]})]
    threshold     \* [a \in Acceptor |-> Nat]   -- the minimal ballot the acceptor will consider

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Vote == [b : Ballot, v : Value]

\* ``votes[a]`` is the set of votes already cast by acceptor *a*.
VoteSet == [a \in Acceptor |-> SUBSET Vote]

\* ``threshold[a]`` is the current promise threshold of acceptor *a*.
Thresh == [a \in Acceptor |-> Nat]

\* A quorum is any element of the constant collection *Quorum*.
Quorums == Quorum

\* Overlap property required by the description (not used directly in actions,
\* but useful for invariants).
Overlap == \A q1, q2 \in Quorums : q1 \cap q2 # {}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------

\* 1. An acceptor may raise its promise threshold without voting.
RaisePromise ==
    \E a \in Acceptor :
        \E newT \in Ballot :
            /\ newT > threshold[a]
            /\ threshold' = [threshold EXCEPT ![a] = newT]
            /\ UNCHANGED votes

\* 2. An acceptor may cast a vote for a value in a ballot, subject to conditions.
VoteAction ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                LET newVote == [b |-> v] IN
                /\ b >= threshold[a]                 \* ballot not below current promise
                /\ \A w \in votes[a] : w.b # b      \* acceptor has not voted in this ballot
                /\ \A a2 \in Acceptor :
                       \A w \in votes[a2] :
                           (w.b = b) => w.v = v   \* no other acceptor voted for a different value in same ballot
                /\ SafeAt(b, v)                     \* the value is safe at ballot b
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {newVote}]
                /\ threshold' = [threshold EXCEPT ![a] = b]

\* Safety condition for a value at a ballot.
SafeAt(b, v) ==
    \A c \in Ballot :
        (c < b) =>
            \E q \in Quorums :
                \A a \in q :
                    (\E w \in votes[a] : w = [c |-> v]) \/ (c < threshold[a])

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ RaisePromise
    \/ VoteAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, threshold>>

\* ----------------------------------------------------------------------
\* Invariant required by the .cfg
\* ----------------------------------------------------------------------
Inv == 
    /\ \A a \in Acceptor : threshold[a] \in Nat
    /\ \A a \in Acceptor : votes[a] \subseteq { [b |-> v] : b \in Ballot, v \in Value }
    /\ \A b \in Ballot :
        \E v \in Value :
            (\A a \in Acceptor : 
                (\E w \in votes[a] : w = [b |-> v]) \/ (b < threshold[a]))
    /\ \A a1, a2 \in Acceptor :
        \A v1, v2 \in Value :
            \A b \in Ballot :
                (\E w1 \in votes[a1] : w1 = [b |-> v1]) /\ 
                (\E w2 \in votes[a2] : w2 = [b |-> v2]) => v1 = v2

\* ----------------------------------------------------------------------
\* Property (consensus) required by the .cfg
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
    \A b1, b2 \in Ballot :
        \A v1, v2 \in Value :
            (\E q1 \in Quorums :
                \A a \in q1 : \E w \in votes[a] : w = [b1 |-> v1]) /\
            (\E q2 \in Quorums :
                \A a \in q2 : \E w \in votes[a] : w = [b2 |-> v2])
            => v1 = v2

====