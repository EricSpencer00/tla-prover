---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(*  CONSTANTS                                                            *)
(***************************************************************************)
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(***************************************************************************)
(*  Symmetry and model checking substitutions                              *)
(***************************************************************************)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

(***************************************************************************)
(*  Variables                                                            *)
(***************************************************************************)
VARIABLES Votes, Promise

(***************************************************************************)
(*  Helper definitions                                                   *)
(***************************************************************************)

(* a vote is a record containing a ballot number and a value *)
VoteRec == [ballot : Ballot, value : Value]

(* a quorum is a set of acceptors; the overlap property is assumed *)
QuorumOverlap == 
  \A q1, q2 \in Quorum : q1 # {} /\ q2 # {} => q1 \cap q2 # {}

(* safety of a value at a given ballot *)
Safe(v, b) == 
  \A c \in Ballot : 
    (c < b) => 
      \E q \in Quorum :
        \A a \in q :
          ( \E dv \in Votes[a] : dv.ballot = c /\ dv.value = v )
          \/ (Promise[a] > c)

(* a value is chosen if some quorum has all its members voting for it at the same ballot *)
Chosen(v) == 
  \E b \in Ballot, q \in Quorum :
    \A a \in q :
      \E dv \in Votes[a] : dv.ballot = b /\ dv.value = v

(* the set of values that have been chosen *)
ChosenVals == { v \in Value : Chosen(v) }

(***************************************************************************)
(*  Initial state                                                         *)
(***************************************************************************)
Init ==
  /\ Votes = [a \in Acceptor |-> {}]
  /\ Promise = [a \in Acceptor |-> -1]

(***************************************************************************)
(*  Actions                                                               *)
(***************************************************************************)

(* an acceptor raises its promise threshold *)
PromiseIncrease ==
  \E a \in Acceptor, nb \in Ballot :
    /\ nb > Promise[a]
    /\ Promise' = [Promise EXCEPT ![a] = nb]
    /\ UNCHANGED Votes

(* an acceptor casts a vote for a value in a ballot *)
CastVote ==
  \E a \in Acceptor, b \in Ballot, v \in Value :
    /\ b >= Promise[a]                                 \* condition 1
    /\ \A dv \in Votes[a] : dv.ballot # b              \* condition 2
    /\ \A a2 \in Acceptor, dv \in Votes[a2] :
         (dv.ballot = b) => dv.value = v               \* condition 3
    /\ Safe(v, b)                                      \* condition 4
    /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ Promise' = [Promise EXCEPT ![a] = b]
    /\ UNCHANGED << >>

Next == PromiseIncrease \/ CastVote

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<Votes, Promise>>

(***************************************************************************)
(*  Invariant                                                             *)
(***************************************************************************)

(* every vote is safe, and at most one value per ballot *)
Inv ==
  /\ \A a \in Acceptor :
        \A dv \in Votes[a] :
          /\ dv.ballot \in Ballot
          /\ dv.value \in Value
          /\ Safe(dv.value, dv.ballot)
  /\ \A b \in Ballot :
        ( \E v \in Value, a \in Acceptor :
            [ballot |-> b, value |-> v] \in Votes[a] )
        => 
        ( \A a2 \in Acceptor :
            \A dv2 \in Votes[a2] :
              (dv2.ballot = b) => 
                dv2.value = 
                  CHOOSE v \in Value :
                    \E a0 \in Acceptor :
                      [ballot |-> b, value |-> v] \in Votes[a0] )

(***************************************************************************)
(*  Property (consensus)                                                  *)
(***************************************************************************)
ConsensusSpecBar == [] ( Cardinality(ChosenVals) <= 1 )

(***************************************************************************)
(*  Symmetry set                                                          *)
(***************************************************************************)
MCSymmetry ==
  { p \in [Acceptor -> Acceptor] :
      /\ DOMAIN p = Acceptor
      /\ RANGE p = Acceptor
      /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2
      /\ \A a \in Acceptor : \E a0 \in Acceptor : p[a0] = a }

=============================================================================