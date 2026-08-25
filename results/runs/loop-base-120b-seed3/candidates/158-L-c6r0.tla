---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* bounded versions for the model checker *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, prom

(* --------------------------------------------------------------------- *)
(* Types *)

VoteRecord == [ballot : Ballot, value : Value]

(* --------------------------------------------------------------------- *)
(* Initial state *)

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ prom  = [a \in Acceptor |-> -1]

(* --------------------------------------------------------------------- *)
(* Safety predicate for a vote *)

Safe(b, v) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E vr \in votes[a] :
                          vr.ballot = c /\ vr.value = v )
                    \/ ( prom[a] > c )

(* --------------------------------------------------------------------- *)
(* Actions *)

PromiseIncrease ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > prom[a]
            /\ prom' = [prom EXCEPT ![a] = b]
            /\ UNCHANGED votes

CastVote ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= prom[a]
                /\ ~(\E vr \in votes[a] : vr.ballot = b)          \* a has not voted in b yet
                /\ \A a2 \in Acceptor :
                       \A vr \in votes[a2] :
                           (vr.ballot = b) => vr.value = v        \* no conflicting value in b
                /\ Safe(b, v)
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
                /\ prom'  = [prom  EXCEPT ![a] = b]

Next ==
    \/ PromiseIncrease
    \/ CastVote

(* --------------------------------------------------------------------- *)
(* Specification *)

Spec ==
    Init /\ [][Next]_<<votes, prom>>

(* --------------------------------------------------------------------- *)
(* Derived definitions *)

Chosen ==
    { v \in Value :
        \E b \in Ballot :
            \E Q \in Quorum :
                \A a \in Q :
                    \E vr \in votes[a] : vr.ballot = b /\ vr.value = v }

(* --------------------------------------------------------------------- *)
(* Invariant *)

Inv ==
    /\ \A a \in Acceptor :
          \A vr \in votes[a] :
                /\ vr \in VoteRecord
                /\ Safe(vr.ballot, vr.value)
    /\ \A b \in Ballot :
          ( \E v \in Value :
                \A a \in Acceptor :
                    \A vr \in votes[a] :
                        (vr.ballot = b) => vr.value = v )
          \/ ( \A a \in Acceptor :
                \A vr \in votes[a] :
                    vr.ballot # b )
    /\ \A a \in Acceptor : prom[a] \in Int

(* --------------------------------------------------------------------- *)
(* Safety property (consensus) *)

ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (v1 \in Chosen /\ v2 \in Chosen) => v1 = v2

(* --------------------------------------------------------------------- *)
(* Symmetry set *)

MCSymmetry ==
    { [a \in Acceptor |-> a] }

====