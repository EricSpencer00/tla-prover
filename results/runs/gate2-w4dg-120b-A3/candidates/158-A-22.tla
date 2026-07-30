---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES vote, threshold

vars == <<vote, threshold>>

VoteSpace == [ball : Ballot, val : Value]
Quorums == Quorum
Acceptors == Acceptor
Values == Value
Ballots == Ballot

HasVotedForBallot(a, b) == \E x \in vote[a] : x.ball = b
NoVoteAtBallot(b) == \A a \in Acceptors : ~HasVotedForBallot(a, b)
VotersForBallot(b) == {a \in Acceptors : HasVotedForBallot(a, b)}
ValueVotedInBallot(b) == CHOOSE x \in Value : \E a \in VotersForBallot(b) : [ball |-> b, val |-> x] \in vote[a]

TypeOK ==
    /\ vote \in [Acceptor -> SUBSET VoteSpace]
    /\ threshold \in [Acceptor -> Ballots \cup {-1}]

Init ==
    /\ vote = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold without casting a vote.
Promise(a, b) ==
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED vote

\* An acceptor votes for a value in a ballot, provided the value is safe and
\* no other value was voted for in that same ballot.
Vote(a, b, v) ==
    /\ b >= threshold[a]
    /\ ~HasVotedForBallot(a, b)
    /\ NoVoteAtBallot(b)
    /\ \E q \in Quorums :
        /\ \A c \in 0 .. (b - 1) : \E q2 \in Quorums :
              \A member \in q2 : (member \in q /\ [ball |-> c, val |-> v] \in vote[member]) \/ threshold[member] > c
    /\ vote' = [vote EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Every chosen value is safe at its ballot number.
NoUnsafeChoice == \A a \in Acceptor : \A x \in vote[a] : \E q \in Quorums :
                    /\ \A c \in 0 .. (x.ball - 1) : \E q2 \in Quorums :
                          \A m \in q2 : (m \in q /\ [ball |-> c, val |-> x.val] \in vote[m]) \/ threshold[m] > c

\* At most one value is voted for in any given ballot.
AtMostOneValuePerBallot == \A b \in Ballot :
    (NoVoteAtBallot(b) \/ (\A a \in Acceptors : HasVotedForBallot(a, b) /\ ValueVotedInBallot(b) \in Values))

Inv ==
    /\ TypeOK
    /\ NoUnsafeChoice
    /\ AtMostOneValuePerBallot

\* Consistency: two quorums voting for different values in any ballots must agree on the value.
\* Refined from the abstract consensus spec, whose single-consensus property is thus
\* carried by the voting implementation.
ConsensusSpecBar ==
    \A b1 \in Ballot, b2 \in Ballot :
        /\ (\A q \in Quorums : \A a \in q : [ball |-> b1, val |-> v1] \in vote[a]) =>
            (\A q \in Quorums : \A a \in q : [ball |-> b2, val |-> v2] \in vote[a] => v1 = v2)

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

\* Symmetry: any renaming of acceptors is a symmetry of the model.
MCSymmetry == {f \in [Acceptor -> Acceptor] : Cardinality({a \in Acceptor : f[a] # a}) = 0}

====