---- MODULE Voting ----
EXTENDS Integers, Naturals, Sequences, FiniteSets, Functions, TLAPS

(***************************************************************************)
(* Constants representing the domain of values, the set of acceptors, and  *)
(* the collection of quorums.                                              *)
(***************************************************************************)
CONSTANTS
    Value,      \* The set of choosable values.
    Acceptor,   \* A set of processes that will choose a value.
    Quorum      \* The set of "quorums", each a large enough set of acceptors.

(***************************************************************************)
(* Assumptions about quorums: each quorum is a non‑empty subset of the      *)
(* acceptor set, and any two quorums intersect.                             *)
(***************************************************************************)
ASSUME
  QuorumAssumption == 
    /\ \A Q \in Quorum : Q \subseteq Acceptor /\ Q # {}
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}

(***************************************************************************)
(* Ballot numbers are natural numbers.                                      *)
(***************************************************************************)
Ballot == Nat

(***************************************************************************)
(* Variables:                                                             *)
(*   votes   maps each acceptor to the set of votes it has cast.            *)
(*   maxBal  maps each acceptor to the highest ballot number it has seen   *)
(*           (or -1 if it has seen none).                                   *)
(***************************************************************************)
VARIABLES votes, maxBal

(***************************************************************************)
(* Type correctness invariant.                                            *)
(***************************************************************************)
TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ maxBal \in [Acceptor -> { -1 } \cup Ballot]

(***************************************************************************)
(* Helper definitions.                                                    *)
(***************************************************************************)
VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) == \E Q \in Quorum :
                    \A a \in Q : VotedFor(a, b, v)

chosen == { v \in Value : \E b \in Ballot : ChosenAt(b, v) }

DidNotVoteAt(a, b) == \A v \in Value : ~VotedFor(a, b, v)

CannotVoteAt(a, b) == /\ maxBal[a] > b
                     /\ DidNotVoteAt(a, b)

NoneOtherChoosableAt(b, v) == 
   \E Q \in Quorum :
     \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)

SafeAt(b, v) == \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)

VotesSafe == \A a \in Acceptor, b \in Ballot, v \in Value :
               VotedFor(a, b, v) => SafeAt(b, v)

OneVote == \A a \in Acceptor, b \in Ballot, v, w \in Value :
             VotedFor(a, b, v) /\ VotedFor(a, b, w) => v = w

OneValuePerBallot ==
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
       VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => v1 = v2

(***************************************************************************)
(* ShowsSafeAt: a safety condition required before an acceptor may cast   *)
(* a vote.  It is unchanged from the original specification.                *)
(***************************************************************************)
ShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : maxBal[a] >= b
  /\ \E c \in -1..(b-1) :
        /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
        /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)

ShowsSafety ==
  TypeOK /\ VotesSafe /\ OneValuePerBallot =>
    \A Q \in Quorum, b \in Ballot, v \in Value :
      ShowsSafeAt(Q, b, v) => SafeAt(b, v)

(***************************************************************************)
(* Initial state.                                                         *)
(***************************************************************************)
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ maxBal = [a \in Acceptor |-> -1]

(***************************************************************************)
(* Actions.                                                               *)
(***************************************************************************)

IncreaseMaxBal(a, b) ==
  /\ a \in Acceptor /\ b \in Ballot
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]
  /\ UNCHANGED votes

VoteFor(a, b, v) ==
  /\ a \in Acceptor /\ b \in Ballot /\ v \in Value
  /\ maxBal[a] <= b
  /\ \A vt \in votes[a] : vt[1] # b
  /\ \A c \in Acceptor \ {a} :
        \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
  /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]

Next ==
  \E a \in Acceptor, b \in Ballot :
    \/ IncreaseMaxBal(a, b)
    \/ \E v \in Value : VoteFor(a, b, v)

(***************************************************************************)
(* Specification.                                                         *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<votes, maxBal>>

(***************************************************************************)
(* Global invariant required by the original module.                       *)
(***************************************************************************)
Inv == TypeOK /\ VotesSafe /\ OneValuePerBallot

=============================================================================