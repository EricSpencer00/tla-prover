---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

Quorums == {Q \in Quorum : Q # {}}

NoPromise == IF a1 \in Nat THEN a1 - 1 ELSE 0 - 1

TypeOK ==
    /\ votes \subseteq [actor: Acceptor, ballot: Ballot, val: Value]
    /\ threshold \in [Acceptor -> Ballot \cup {NoPromise}]

Init ==
    /\ votes = {}
    /\ threshold = [a \in Acceptor |-> NoPromise]

Promises ==
    {<<a, b, v>> \in votes : a = p /\ b = n}
    
SafeAt(v, b) ==
    /\ \A c \in Ballot :
           (c < b /\ \E Q \in Quorums :
              \A a \in Q :
                  (<<a, c, v>> \in votes \/ (b \notin Ballot)))
    /\ \A q \in votes : q.ballot = b /\ q.val # v => q.actor = p

RaiseThreshold(a, n) ==
    /\ n \in Ballot
    /\ n > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = n]
    /\ UNCHANGED votes

CastVote(a, n, v) ==
    /\ n \in Ballot
    /\ n >= threshold[a]
    /\ \A q \in votes : q.actor = a /\ q.ballot = n => FALSE
    /\ \A b \in Ballot : b = n => \A w \in Value : w # v => \A q \in votes :
           q.ballot = b /\ q.val = w => FALSE
    /\ \E Q \in Quorums : \A a2 \in Q : SafeAt(v, n)
    /\ votes' = votes \cup {<<a, n, v>>}
    /\ threshold' = [threshold EXCEPT ![a] = n]

Next ==
    \/ \E a \in Acceptor, n \in Ballot : RaiseThreshold(a, n)
    \/ \E a \in Acceptor, n \in Ballot, v \in Value : CastVote(a, n, v)

Spec == Init /\ [][Next]_vars

Inv ==
    \A q \in votes :
        /\ SafeAt(q.val, q.ballot)
        /\ \A q2 \in votes :
              (q.ballot = q2.ballot /\ q.val # q2.val) => q.actor = q2.actor
        /\ threshold[q.actor] # NoPromise
        /\ q.ballot \in Ballot
        /\ q.val \in Value

ConsensusSpecBar ==
    \A v \in Value :
        \A b \in Ballot :
            (\A Q \in Quorums :
                 \A a \in Q : <<a, b, v>> \in votes)
                => \A w \in Value :
                       (\A Q \in Quorums :
                            \A a \in Q : <<a, b, w>> \in votes) => w = v
====