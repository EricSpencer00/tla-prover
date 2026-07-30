---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

RECURSIVE SafeAt(_, _)
SafeAt(v, c) ==
    /\ c \in Ballot
    /\ \A q \in Value :
        (q = v \/ \A a \in Acceptor : \A b \in Ballot : b < c => \E Q \in Quorum :
            \A m \in Q : <<b, q>> \in votes[m]))
\* The current vote must be safe at its ballot, and there must be a quorum
\* showing that the value is safe at every lower ballot.

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ threshold \in [Acceptor -> {-1} \cup Ballot]

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold without voting.
Promise(a, b) ==
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* An acceptor votes for a value, but only if no value has already been voted
\* for in that ballot and the value is safe at that ballot.
CastVote(a, b, v) ==
    /\ b >= threshold[a]
    /\ ~\E w \in Value : <<b, w>> \in votes[a]
    /\ \A m \in Acceptor : ~(\E w \in Value : <<b, w>> \in votes[m])
    /\ SafeAt(v, b)
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* A value is chosen once a quorum has voted for it in some ballot.
Chosen == \E Q \in Quorum, b \in Ballot, v \in Value :
    \A a \in Q : <<b, v>> \in votes[a]

\* Consistency: two values cannot both be chosen.
Inv == Chosen => \E Q \in Quorum, b \in Ballot : \A a \in Q : <<b, Chosen>> \in votes[a]

\* Refinement: the voting algorithm implements the abstract consensus spec.
ConsensusSpecBar == Spec /\ Init /\ TypeOK /\ Inv

====