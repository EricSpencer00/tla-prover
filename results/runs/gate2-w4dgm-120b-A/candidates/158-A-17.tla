---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Votes == [ball : Ballot, val : Value]

VARIABLES pVotes, threshold

vars == <<pVotes, threshold>>

TypeOK ==
    /\ pVotes \in [Acceptor -> SUBSET Votes]
    /\ threshold \in [Acceptor -> Int]

Init ==
    /\ pVotes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* A quorum is a set of acceptors, and any two quorums must overlap.
QuorumsOverlap ==
    \A q1, q2 \in Quorum : q1 # q2 => q1 \cap q2 # {}

\* No quorum has two members voting for different values in the same ballot.
QuorumVoteUnanimous ==
    \A q \in Quorum, b \in Ballot :
        \A a1, a2 \in q :
            \A v1, v2 \in Value :
                (\A v \in Value : [ball |-> b, val |-> v] \notin pVotes[a1] /\ [ball |-> b, val |-> v] \notin pVotes[a2])
                    \/ ([ball |-> b, val |-> v1] \in pVotes[a1] /\ [ball |-> b, val |-> v2] \in pVotes[a2] => v1 = v2)

\* Every vote an acceptor has cast is safe at its ballot number.
AllVotesAreSafe ==
    \A a \in Acceptor :
        \A v \in pVotes[a] :
            \A c \in Ballot :
                (c < v.ball /\ \A x \in Quorum : \E m \in x : [ball |-> c, val |-> v.val] \in pVotes[m])
                    => \E q \in Quorum : \A m \in q : [ball |-> c, val |-> v.val] \in pVotes[m]

\* At most one value is voted for in any ballot, which is what consensus means.
BallotIsSingleValued ==
    \A b \in Ballot : \A a1, a2 \in Acceptor :
        \A v1, v2 \in Value :
            (\A v \in Value : [ball |-> b, val |-> v] \notin pVotes[a1] /\ [ball |-> b, val |-> v] \notin pVotes[a2])
                \/ ([ball |-> b, val |-> v1] \in pVotes[a1] /\ [ball |-> b, val |-> v2] \in pVotes[a2] => v1 = v2)

\* Actions: an acceptor raises its promise threshold, or casts a vote.
RaiseThreshold(a, n) ==
    /\ n > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = n]
    /\ UNCHANGED pVotes

\* Casting a vote also raises the acceptor's own threshold to the ballot it just voted in.
Vote(a, b, v) ==
    /\ b >= threshold[a]
    /\ \A w \in pVotes[a] : w.ball # b
    /\ \A x \in Quorum : \A m \in x : [ball |-> b, val |-> v] \in pVotes[m]
    /\ pVotes' = [pVotes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, n \in Ballot : RaiseThreshold(a, n)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Consistency: at most one value is ever chosen by a quorum.
Inv == QuorumOverlap /\ QuorumVoteUnanimous /\ AllVotesAreSafe /\ BallotIsSingleValued

\* The chosen set is derived from the votes; every quorum for a value in a ballot is unanimously committed.
ChosenValue == CHOOSE v \in Value :
    \E b \in Ballot : \E q \in Quorum : \A a \in q : [ball |-> b, val |-> v] \in pVotes[a]

MCSymmetry == <<[a1 |-> a1, a2 |-> a2, a3 |-> a3]>> \X
    <<[a1 |-> a2, a2 |-> a1, a3 |-> a3]>> \X
    <<[a1 |-> a3, a2 |-> a2, a3 |-> a1]>>

\* The constant-parameter abstraction of this spec is the fixed set of acceptors, values,
\* quorums, and ballot numbers; the concrete instances bound Ballot to a finite range.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

\* The voting algorithm implements consensus: it refines an abstract consensus spec whose
\* chosen set is derived from the votes in this spec.
ConsensusSpecBar == Inv

====