---- MODULE Voting ----
EXTENDS Naturals, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(*--- Constant constraints ---*)
ASSUME a1 /= a2 /\ a1 /= a3 /\ a2 /= a3
ASSUME v1 /= v2
ASSUME Acceptor = {a1, a2, a3}
ASSUME Value     = {v1, v2}
ASSUME Quorum    = {{a1, a2}, {a1, a3}, {a2, a3}}
ASSUME Ballot    = Nat

(*--- Operators overridden for model checking ---*)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, prom

(*--- Initial state ---*)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ prom  = [a \in Acceptor |-> -1]

(*--- Safety of a value at a ballot ---*)
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) => 
            \E Q \in Quorum :
                \A a \in Q :
                    (<<c, v>> \in votes[a]) \/ (prom[a] > c)

(*--- Next-state relation ---*)
Next ==
    \/ \E a \in Acceptor, b \in Ballot :
          /\ b > prom[a]                \* promise increase
          /\ prom' = [prom EXCEPT ![a] = b]
          /\ UNCHANGED votes
    \/ \E a \in Acceptor, v \in Value, b \in Ballot :
          /\ b >= prom[a]                              \* cannot vote below promise
          /\ <<b, v>> \notin votes[a]                  \* not voted in this ballot yet
          /\ \A a2 \in Acceptor :
                \A w \in Value :
                    (<<b, w>> \in votes[a2]) => w = v   \* at most one value per ballot
          /\ Safe(v, b)                                \* value is safe
          /\ prom' = [prom EXCEPT ![a] = b]
          /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]

Spec == Init /\ [] [Next]_<<votes, prom>>

(*--- Invariant ---*)
Inv ==
    /\ \A a \in Acceptor : votes[a] \subseteq Ballot \X Value
    /\ \A a \in Acceptor : prom[a] \in Ballot \/ prom[a] = -1
    /\ \A a \in Acceptor, p \in votes[a] :
          LET b == p[1] IN LET v == p[2] IN Safe(v, b)
    /\ \A b \in Ballot :
          \A a1, a2 \in Acceptor :
            \A v1, v2 \in Value :
               (<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2]) => v1 = v2

(*--- Definition of a chosen value ---*)
Chosen(v) ==
    \E b \in Ballot, Q \in Quorum :
        \A a \in Q : <<b, v>> \in votes[a]

(*--- Consensus safety property ---*)
ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (Chosen(v1) /\ Chosen(v2)) => v1 = v2

(*--- Symmetry set (permutations of acceptors) ---*)
MCSymmetry ==
    {
        [a \in Acceptor |-> a],
        [a \in Acceptor |
            IF a = a1 THEN a2
            ELSE IF a = a2 THEN a1
            ELSE a3]
    }

====