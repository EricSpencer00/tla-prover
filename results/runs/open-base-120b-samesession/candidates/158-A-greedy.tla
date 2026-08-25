---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* bounded versions used by the model checker *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, thresh

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

(* ------------------------------------------------------------------- *)
(* Helper predicate: a vote is safe at its ballot *)
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( (\E vote \in votes[a] :
                           vote.ballot = c /\ vote.value = v)
                      \/ thresh[a] > c )

(* ------------------------------------------------------------------- *)
(* Actions *)

Promise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > thresh[a]
    /\ thresh' = [thresh EXCEPT ![a] = b]
    /\ votes'  = votes

Vote(a, v, b) ==
    /\ a \in Acceptor
    /\ v \in Value
    /\ b \in Ballot
    /\ b >= thresh[a]                         \* not below current promise
    /\ \A vote \in votes[a] : vote.ballot # b \* not already voted in b
    /\ \A a2 \in Acceptor : \A vote2 \in votes[a2] :
          (vote2.ballot = b) => vote2.value = v
    /\ Safe(v, b)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup
                     { [ballot |-> b, value |-> v] }]
    /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor: \E b \in Ballot: Promise(a, b)
    \/ \E a \in Acceptor: \E v \in Value: \E b \in Ballot: Vote(a, v, b)

Spec == Init /\ [][Next]_<<votes, thresh>>

(* ------------------------------------------------------------------- *)
(* Invariants *)

TypeInv ==
    /\ votes \in [Acceptor -> SUBSET [ballot: Ballot, value: Value]]
    /\ thresh \in [Acceptor -> (Ballot \cup {-1})]

VoteSafety ==
    \A a \in Acceptor: \A vote \in votes[a] : Safe(vote.value, vote.ballot)

OneValuePerBallot ==
    \A b \in Ballot :
        \A a1, a2 \in Acceptor :
            \A v1, v2 \in Value :
                ( \E vote1 \in votes[a1] :
                      vote1.ballot = b /\ vote1.value = v1 )
                /\ ( \E vote2 \in votes[a2] :
                      vote2.ballot = b /\ vote2.value = v2 )
                => v1 = v2

QuorumOverlap ==
    \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Inv == TypeInv /\ VoteSafety /\ OneValuePerBallot /\ QuorumOverlap

(* ------------------------------------------------------------------- *)
(* Consistency property *)

Chosen ==
    { v \in Value :
        \E b \in Ballot, Q \in Quorum :
            \A a \in Q :
                \E vote \in votes[a] :
                    vote.ballot = b /\ vote.value = v }

ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (v1 \in Chosen /\ v2 \in Chosen) => v1 = v2

(* ------------------------------------------------------------------- *)
(* Symmetry set: all permutations of Acceptor *)

MCSymmetry ==
    { f \in [Acceptor -> Acceptor] :
        \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2 }

====