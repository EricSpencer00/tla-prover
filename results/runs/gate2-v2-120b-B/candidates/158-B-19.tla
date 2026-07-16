---- MODULE Voting --------------------------------------------------------------
EXTENDS Integers, TLAPS

(***************************************************************************)
(* Constants                                                             *)
(***************************************************************************)
CONSTANT Value,               \* The set of choosable values.
         Acceptor,            \* A set of processes that will choose a value.
         Quorum               \* The set of quorums (each a subset of Acceptor)

(***************************************************************************)
(* Quorum assumptions (as given)                                         *)
(***************************************************************************)
ASSUME QuorumAssumption == 
    /\ \A Q \in Quorum : Q \subseteq Acceptor
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

(***************************************************************************)
(* Ballots                                                               *)
(***************************************************************************)
Ballot == Nat

(***************************************************************************)
(* Variables                                                             *)
(***************************************************************************)
VARIABLE votes,   \* votes[a] is the set of votes cast by acceptor a
         maxBal   \* maxBal[a] is the highest ballot number a has participated in

(***************************************************************************)
(* Type correctness invariant (unchanged)                                 *)
(***************************************************************************)
TypeOK == 
    /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

(***************************************************************************)
(* Helper definitions                                                    *)
(***************************************************************************)
VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == { v \in Value : \E b \in Ballot : ChosenAt(b, v) }

DidNotVoteAt(a, b) == \A v \in Value : ~VotedFor(a, b, v)

CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)

NoneOtherChoosableAt(b, v) ==
    \E Q \in Quorum :
        \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)

SafeAt(b, v) == \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)

ShowsSafeAt(Q, b, v) ==
    /\ \A a \in Q : maxBal[a] >= b
    /\ \E c \in -1..(b-1) :
         /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
         /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)

(***************************************************************************)
(* Safety‑related invariants (as given)                                   *)
(***************************************************************************)
VotesSafe == \A a \in Acceptor, b \in Ballot, v \in Value :
                VotedFor(a, b, v) => SafeAt(b, v)

OneVote == \A a \in Acceptor, b \in Ballot, v, w \in Value :
             VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

OneValuePerBallot ==
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
        VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

Inv == TypeOK /\ VotesSafe /\ OneValuePerBallot

(***************************************************************************)
(* Initial predicate                                                     *)
(***************************************************************************)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ maxBal = [a \in Acceptor |-> -1]

(***************************************************************************)
(* Actions                                                               *)
(***************************************************************************)
IncreaseMaxBal(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]
    /\ UNCHANGED votes

VoteFor(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ maxBal[a] <= b
    /\ \A vt \in votes[a] : vt[1] # b
    /\ \A c \in Acceptor \ {a} :
          \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
    /\ maxBal' = [maxBal EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : IncreaseMaxBal(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : VoteFor(a, b, v)

(***************************************************************************)
(* Specification                                                          *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<votes, maxBal>>

=============================================================================