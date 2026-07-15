---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC, Integers

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

(* Record type for a vote *)
Vote == [b: Nat, v: Value]

VARIABLES votes, thresholds

(* Initial state: no votes, thresholds set to -1 *)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresholds = [a \in Acceptor |-> -1]

(* Predicate: a vote (b,v) is safe at ballot b *)
Safe(v, b) ==
    \A c \in Ballot : c < b =>
        \E q \in Quorum :
            \A a \in q :
                \E vote \in votes[a] : vote.b = c /\ vote.v = v
                \/ thresholds[a] > c

(* Action: raise promise threshold for an acceptor *)
Promise(a, t) ==
    /\ a \in Acceptor
    /\ t \in Ballot
    /\ t > thresholds[a]
    /\ votes' = votes
    /\ thresholds' = [thresholds EXCEPT ![a] = t]

(* Action: cast a vote for a value in a ballot *)
VoteAction(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= thresholds[a]
    /\ \A vote \in votes[a] : vote.b # b
    /\ \A a2 \in Acceptor \ {a} :
          \A vote2 \in votes[a2] : vote2.b # b \/ vote2.v = v
    /\ Safe(v, b)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [b |-> b, v |-> v] }]
    /\ thresholds' = [thresholds EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, t \in Ballot : Promise(a, t)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : VoteAction(a, b, v)

Spec == Init /\ [][Next]_<<votes, thresholds>>

(* Invariant: type correctness *)
TypeOK ==
    /\ votes \in [Acceptor -> SUBSET Vote]
    /\ thresholds \in [Acceptor -> Int]

(* Invariant: all votes are safe, at most one value per ballot *)
AllVotesSafe ==
    \A a \in Acceptor :
        \A vote \in votes[a] :
            Safe(vote.v, vote.b)

OneValuePerBallot ==
    \A b \in Ballot :
        \A v1 \in Value, v2 \in Value :
            (\E a \in Acceptor : [b |-> b, v |-> v1] \in votes[a]) /\
            (\E a \in Acceptor : [b |-> b, v |-> v2] \in votes[a]) =>
                v1 = v2

Inv == TypeOK /\ AllVotesSafe /\ OneValuePerBallot

(* Property: at most one value is chosen per ballot *)
ChosenValuesAtMostOne ==
    \A b \in Ballot :
        \A v1 \in Value, v2 \in Value :
            (\E q \in Quorum :
                \A a \in q : [b |-> b, v |-> v1] \in votes[a]) /\
            (\E q2 \in Quorum :
                \A a \in q2 : [b |-> b, v |-> v2] \in votes[a]) =>
                v1 = v2

ConsensusSpecBar == ChosenValuesAtMostOne

====