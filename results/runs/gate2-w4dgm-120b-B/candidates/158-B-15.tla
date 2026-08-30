------------------------------ MODULE MCVoting ------------------------------
EXTENDS Naturals

CONSTANTS Acceptor, Value, Quorum

VARIABLES votes, maxBal

vars == <<votes, maxBal>>

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Nat \X Value)]
    /\ maxBal \in [Acceptor -> -1..(Cardinality(Value))]

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ maxBal = [a \in Acceptor |-> -1]

Vote(a, v) ==
    /\ maxBal[a] + 1 <= Cardinality(Value)
    /\ maxBal' = [maxBal EXCEPT ![a] = maxBal[a] + 1]
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<maxBal[a] + 1, v>>}]

Next == \E a \in Acceptor : \E v \in Value : Vote(a, v)

Spec == Init /\ [][Next]_vars

\* A quorum of acceptors voted for value v in the same ballot number.
VotedFor(v) ==
    \E Q \in Quorum :
        \E b \in Nat :
            /\ \A a \in Q : <<b, v>> \in votes[a]
            /\ \A a \in Q : \A c \in Nat : <<c, v>> \in votes[a] => c = b

\* No two distinct values can both be supported by a quorum in a ballot.
NoDoubleCommit == \A v1 v2 \in Value : (VotedFor(v1) /\ VotedFor(v2)) => (v1 = v2)

=============================================================================