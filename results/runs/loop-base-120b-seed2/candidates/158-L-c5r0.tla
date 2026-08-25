---- MODULE Voting ----
EXTENDS Integers, FiniteSets, TLC

\*=============================
\* Constants (to be instantiated in the .cfg)
\*=============================
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\*=============================
\* Operators substituting constants for model checking
\*=============================
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\*=============================
\* State variables
\*=============================
VARIABLES votes, promise

\*=============================
\* Types
\*=============================
Vote == [ballot : Ballot, value : Value]

\*=============================
\* Initial state
\*=============================
Init ==
    /\ votes   = [a \in Acceptor |-> {}]            \* each acceptor starts with no votes
    /\ promise = [a \in Acceptor |-> -1]            \* initial promise threshold

\*=============================
\* Safety of a value at a ballot
\*=============================
Safe(v, b) ==
    \A c \in 0..(b-1) :
        \E Q \in Quorum :
            \A a \in Q :
                ( \E vt \in votes[a] : vt.ballot = c /\ vt.value = v )
                \/ promise[a] > c

\*=============================
\* Action: increase promise without voting
\*=============================
IncreasePromise ==
    \E a \in Acceptor :
        \E nb \in Ballot :
            /\ nb > promise[a]                         \* only increase
            /\ promise' = [promise EXCEPT ![a] = nb]
            /\ votes'   = votes

\*=============================
\* Action: cast a vote
\*=============================
CastVote ==
    \E a \in Acceptor :
        \E v \in Value :
            \E b \in Ballot :
                /\ b >= promise[a]                     \* not below current promise
                /\ \A vt \in votes[a] : vt.ballot # b   \* haven't voted in this ballot yet
                /\ \A a2 \in Acceptor :
                       \A vt2 \in votes[a2] :
                          (vt2.ballot = b) => (vt2.value = v)   \* no conflicting vote
                /\ Safe(v, b)                           \* value is safe at this ballot
                /\ votes'   = [votes EXCEPT ![a] = votes[a] \cup {{ballot |-> b, value |-> v}}]
                /\ promise' = [promise EXCEPT ![a] = b]

\*=============================
\* Next-state relation
\*=============================
Next == \/ IncreasePromise \/ CastVote

\*=============================
\* Specification
\*=============================
Spec == Init /\ [][Next]_<<votes, promise>>

\*=============================
\* Helper definitions for invariants
\*=============================
AllVotesSafe ==
    \A a \in Acceptor :
        \A vt \in votes[a] :
            Safe(vt.value, vt.ballot)

AtMostOneValuePerBallot ==
    \A b \in Ballot :
        \E v \in Value :
            \A a \in Acceptor :
                \A vt \in votes[a] :
                    vt.ballot = b => vt.value = v

TypeOk ==
    /\ votes \in [Acceptor -> SUBSET Vote]
    /\ promise \in [Acceptor -> Int]

\*=============================
\* Invariant
\*=============================
Inv == AllVotesSafe /\ AtMostOneValuePerBallot /\ TypeOk

\*=============================
\* Definition of chosen values
\*=============================
Chosen(v) ==
    \E b \in Ballot :
        \E Q \in Quorum :
            \A a \in Q :
                \E vt \in votes[a] :
                    vt.ballot = b /\ vt.value = v

\*=============================
\* Consensus safety property
\*=============================
ConsensusSpecBar ==
    \A v1_, v2_ \in Value :
        (Chosen(v1_) /\ Chosen(v2_)) => v1_ = v2_

\*=============================
\* Symmetry set (permutations of acceptors)
\*=============================
IsPermutation(p) ==
    /\ DOMAIN p = Acceptor
    /\ RANGE p = Acceptor
    /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2

MCSymmetry == { p \in [Acceptor -> Acceptor] : IsPermutation(p) }

====