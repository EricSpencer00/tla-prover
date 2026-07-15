---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

*************************************************************************
(*  Constants (instantiated in the .cfg)                               *)
(*  a1        : an arbitrary element of Acceptor (used only for the   *)
(*              definition of a non‑empty set)                         *)
(*  Acceptor  : the finite set of acceptor identifiers                 *)
(*  Value     : the finite set of possible values                      *)
(*  Quorum    : the finite set of quorum subsets of Acceptor           *)
(*  Ballot    : the finite set of ballot numbers (subset of Nat)      *)
*************************************************************************

(*---------------------------------------------------------------------*)
(*  Type definitions                                                   *)
(*---------------------------------------------------------------------*)

Vote == [bal : Ballot, val : Value]

(*---------------------------------------------------------------------*)
(*  State variables                                                    *)
(*---------------------------------------------------------------------*)

VARIABLES
    votes,      \* votes \in [Acceptor -> SUBSET Vote]
    threshold   \* threshold \in [Acceptor -> Nat]  (negative one is encoded as -1)

(*---------------------------------------------------------------------*)
(*  Helper definitions                                                *)
(*---------------------------------------------------------------------*)

\* The set of values that have been voted for in a particular ballot
ValuesInBallot(b) == { v : Value : \E a \in Acceptor : [bal |-> b, val |-> v] \in votes[a] }

\* A quorum is any element of the constant set Quorum
Quorums == Quorum

\* Safety predicate for a value v at ballot b
Safe(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E q \in Quorums :
        \A a \in q :
          ( [bal |-> c, val |-> v] \in votes[a] )
          \/ (threshold[a] > c)

(*---------------------------------------------------------------------*)
(*  Initial state                                                     *)
(*---------------------------------------------------------------------*)

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

(*---------------------------------------------------------------------*)
(*  Actions                                                            *)
(*---------------------------------------------------------------------*)

\* Increase promise threshold (no vote)
IncreaseThresh(a, b) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Cast a vote for value v in ballot b
Vote(a, b, v) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ v \in Value
  /\ b >= threshold[a]
  /\ \A w \in ValuesInBallot(b) : w = v          \* at most one value per ballot
  /\ \A a2 \in Acceptor :
        ( [bal |-> b, val |-> v] \in votes[a2] ) => a2 = a
  /\ Safe(v, b)                                 \* value is safe at b
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [bal |-> b, val |-> v] }]
  /\ threshold' = [threshold EXCEPT ![a] = b]

\* Next can be either an IncreaseThresh or a Vote by some acceptor
Next ==
  \E a \in Acceptor :
    ( \E b \in Ballot : IncreaseThresh(a, b) )
    \/ ( \E b \in Ballot : \E v \in Value : Vote(a, b, v) )

(*---------------------------------------------------------------------*)
(*  Specification                                                     *)
(*---------------------------------------------------------------------*)

Spec == Init /\ [][Next]_<<votes, threshold>>

(*---------------------------------------------------------------------*)
(*  Invariant (the one required by the .cfg)                           *)
(*---------------------------------------------------------------------*)

Inv ==
  /\ \A a \in Acceptor :
        \A vote \in votes[a] :
          /\ vote.val \in Value
          /\ vote.bal \in Ballot
          /\ Safe(vote.val, vote.bal)
  /\ \A b \in Ballot :
        Cardinality(ValuesInBallot(b)) <= 1
  /\ threshold \in [Acceptor -> Nat]

(*---------------------------------------------------------------------*)
(*  Safety property required by the .cfg                               *)
(*---------------------------------------------------------------------*)

ConsensusSpecBar ==
  \A b1, b2 \in Ballot :
    \A v1, v2 \in Value :
      ( (Cardinality({ a : a \in Acceptor : [bal |-> b1, val |-> v1] \in votes[a] }) >= 1)
        /\ (Cardinality({ a : a \in Acceptor : [bal |-> b2, val |-> v2] \in votes[a] }) >= 1) )
      => v1 = v2

=============================================================================