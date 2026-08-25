---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* substitutions for the model‑checking constants *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, promise

(* ----------------------------------------------------------------------
   Types
   ---------------------------------------------------------------------- *)

Vote == [ballot : Ballot, value : Value]

TypeOK ==
    /\ votes   \in [Acceptor -> SUBSET Vote]
    /\ promise \in [Acceptor -> Int]

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
    /\ votes   = [a \in Acceptor |-> {}]
    /\ promise = [a \in Acceptor |-> -1]

(* ----------------------------------------------------------------------
   Safety predicate for a value at a ballot
   ---------------------------------------------------------------------- *)

Safe(v, b) ==
    \A c \in Ballot :
        (c < b) => 
            \E q \in Quorum :
                \A a \in q :
                    ( \E vv \in votes[a] :
                          vv.ballot = c /\ vv.value = v )
                    \/ (promise[a] > c)

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

PromiseIncrease ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > promise[a]
            /\ promise' = [promise EXCEPT ![a] = b]
            /\ UNCHANGED votes

VoteAction ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= promise[a]
                /\ ~(\E vv \in votes[a] : vv.ballot = b)               \* not voted in this ballot yet
                /\ (\A a2 \in Acceptor :
                        (\A vv2 \in votes[a2] :
                            (vv2.ballot = b) => vv2.value = v))   \* no different value in same ballot
                /\ Safe(v, b)                                         \* safety condition
                /\ votes'   = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
                /\ promise' = [promise EXCEPT ![a] = b]

Next ==
    \/ PromiseIncrease
    \/ VoteAction

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec ==
    Init /\ [][Next]_<<votes, promise>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)

AtMostOneValuePerBallot ==
    \A b \in Ballot :
        \A v1, v2 \in Value :
            ( (\E a1 \in Acceptor : \E vv1 \in votes[a1] : vv1.ballot = b /\ vv1.value = v1) /\
              (\E a2 \in Acceptor : \E vv2 \in votes[a2] : vv2.ballot = b /\ vv2.value = v2) )
            => v1 = v2

VoteSafety ==
    \A a \in Acceptor :
        \A vv \in votes[a] :
            Safe(vv.value, vv.ballot)

Inv == TypeOK /\ AtMostOneValuePerBallot /\ VoteSafety

(* ----------------------------------------------------------------------
   Chosen values and the consensus property
   ---------------------------------------------------------------------- *)

Chosen(v) ==
    \E b \in Ballot :
        \E q \in Quorum :
            \A a \in q :
                \E vv \in votes[a] :
                    vv.ballot = b /\ vv.value = v

ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (Chosen(v1) /\ Chosen(v2)) => v1 = v2

(* ----------------------------------------------------------------------
   Assumptions about quorums
   ---------------------------------------------------------------------- *)

QuorumOverlap ==
    \A q1 \in Quorum : \A q2 \in Quorum : q1 \cap q2 # {}

(* ----------------------------------------------------------------------
   Symmetry set (identity permutation)
   ---------------------------------------------------------------------- *)

MCSymmetry == { [a \in Acceptor |-> a] }

=============================================================================