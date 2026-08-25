---- MODULE Voting ----
EXTENDS Integers, Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* operators substituted by the .cfg file *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, prom

(* ------------------------------------------------------------------- *)
(* Helper type for a vote *)
VoteRec == [ballot : Ballot, value : Value]

(* ------------------------------------------------------------------- *)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ prom  = [a \in Acceptor |-> -1]

(* ------------------------------------------------------------------- *)
IncreasePromise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > prom[a]
    /\ prom' = [prom EXCEPT ![a] = b]
    /\ UNCHANGED votes

Safe(b, v) ==
    /\ b \in Ballot
    /\ v \in Value
    /\ \A c \in Ballot :
         (c < b) =>
           \E Q \in Quorum :
               (\A a \in Q :
                    (\E p \in votes[a] :
                         p.ballot = c /\ p.value = v) \/
                    prom[a] > c)

Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= prom[a]
    /\ ~(\E p \in votes[a] : p.ballot = b)          \* not already voted in this ballot
    /\ \A acc \in Acceptor: \A p \in votes[acc] :
          (p.ballot = b) => p.value = v            \* no conflicting vote
    /\ Safe(b, v)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ prom'  = [prom  EXCEPT ![a] = b]

(* ------------------------------------------------------------------- *)
Next ==
    \/ \E a \in Acceptor: \E b \in Ballot: IncreasePromise(a, b)
    \/ \E a \in Acceptor: \E b \in Ballot: \E v \in Value: Vote(a, b, v)

Spec ==
    Init /\ [][Next]_<<votes, prom>>

(* ------------------------------------------------------------------- *)
Chosen ==
    { v \in Value :
        \E b \in Ballot :
            \E Q \in Quorum :
                (\A a \in Q :
                     \E p \in votes[a] :
                         p.ballot = b /\ p.value = v) }

Inv ==
    /\ \A a \in Acceptor:
          \A p \in votes[a] : Safe(p.ballot, p.value)
    /\ \A b \in Ballot:
          /\ \A acc1, acc2 \in Acceptor:
                \A p1 \in votes[acc1], p2 \in votes[acc2]:
                   (p1.ballot = b /\ p2.ballot = b) => p1.value = p2.value
    /\ \A a \in Acceptor: prom[a] \in Ballot \/ prom[a] = -1

ConsensusSpecBar ==
    /\ \A val1, val2 \in Value :
          (val1 \in Chosen /\ val2 \in Chosen) => val1 = val2

(* ------------------------------------------------------------------- *)
(* Symmetry set – identity permutation (satisfies required type) *)
MCSymmetry == { [a \in Acceptor |-> a] }

====