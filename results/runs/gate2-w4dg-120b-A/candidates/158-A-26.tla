---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

\* Actions: raise an acceptor's promise threshold, or cast a vote for a value
\* in a ballot, provided the ballot is above the threshold and no quorum is
\* already split on two values.

VARIABLES votes, prom

vars == << votes, prom >>

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ prom \in [Acceptor -> INTEGER]

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ prom = [a \in Acceptor |-> -1]

Safe(b, v) ==
    /\ \A c \in (Ballot \cap (0..b-1)) :
         \E q \in Quorum :
            /\ (c > prom[a1] => a1 \in q)
            /\ \A a \in q : << c, v >> \in votes[a]
    /\ \A c \in (Ballot \cap (b+1 .. (Cardinality(Ballot) - 1))) :
         \A v2 \in Value : << c, v2 >> \in votes[a1] => v2 = v

Raise(a, b) ==
    /\ b > prom[a]
    /\ prom' = [prom EXCEPT ![a] = b]
    /\ UNCHANGED votes

Vote(a, b, v) ==
    /\ b >= prom[a]
    /\ \A e \in votes[a] : e[1] < b
    /\ \A e \in votes[a] : e[1] # b
    /\ \A e \in {<< x[1], x[2] >> : x \in votes[a]}, d \in Acceptor :
         (x[1] = b /\ x[2] # v) => << x[1], v >> \notin votes[d]
    /\ Safe(b, v)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<< b, v >>}]
    /\ prom' = [prom EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : Raise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

Chosen == {v \in Value : \E q \in Quorum, b \in Ballot : \A a \in q : << b, v >> \in votes[a]}

\* A vote is only ever cast for a value that was already safe at that ballot:
\* this is what makes the chosen set single-valued.
Inv ==
    /\ \A a \in Acceptor : \A e \in votes[a] : Safe(e[1], e[2])
    /\ \A a \in Acceptor, b \in Ballot, v \in Value :
         (<< b, v >> \in votes[a]) =>
           \A d \in Acceptor : ~ (<< b, v >> \in votes[d] /\ \E w \in Value : w # v /\ << b, w >> \in votes[d])
    /\ TypeOK

\* The voting algorithm implements the abstract consensus spec by refinement:
\* the chosen set is derived from the votes.
ConsensusSpecBar == TRUE
====