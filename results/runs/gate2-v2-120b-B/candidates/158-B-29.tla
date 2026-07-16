------------------------------- MODULE Voting -------------------------------
(***************************************************************************)
(* This is a high-level algorithm in which a set of processes              *)
(* cooperatively choose a value.                                           *)
(***************************************************************************)
EXTENDS Integers, TLAPS
-----------------------------------------------------------------------------

CONSTANT Value,     \* The set of choosable values.
         Acceptor,  \* A set of processes that will choose a value.
         Quorum     \* The set of "quorums", where a quorum is a 
                    \*   "large enough" set of acceptors

(***************************************************************************)
(* Here are the assumptions we make about quorums.                         *)
(***************************************************************************)
ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}  

THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Ballot is a set of "ballot numbers".  For simplicity, we let it be the  *)
(* set of natural numbers.  However, we write Ballot for that set to       *)
(* distinguish ballots from natural numbers used for other purposes.       *)
(***************************************************************************)
Ballot == Nat
-----------------------------------------------------------------------------

(***************************************************************************)
(* In the algorithm, each acceptor can cast one or more votes, where each  *)
(* vote cast by an acceptor has the form <<b, v>> indicating that the      *)
(* acceptor has voted for value v in ballot b.  A value is chosen if a     *)
(* quorum of acceptors have voted for it in the same ballot.               *)
(***************************************************************************)

(***************************************************************************)
(* The algorithm's variables.                                              *)
(***************************************************************************)
VARIABLE votes,   \* votes[a] is the set of votes cast by acceptor a
         maxBal   \* maxBal[a] is a ballot number.  Acceptor a will cast
                  \*   further votes only in ballots numbered \geq maxBal[a]

(***************************************************************************)
(* The type-correctness invariant.                                         *)
(***************************************************************************)
TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Helper definitions                                                       *)
(***************************************************************************)

VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

DidNotVoteAt(a, b) == \A v \in Value : ~VotedFor(a, b, v)

CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)

NoneOtherChoosableAt(b, v) == 
   \E Q \in Quorum :
     \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)

SafeAt(b, v) == \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)

ShowsSafeAt(Q, b, v) == 
  /\ \A a \in Q : maxBal[a] \geq b
  /\ \E c \in -1..(b-1) : 
      /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
      /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariant definitions                                                   *)
(***************************************************************************)

VotesSafe == \A a \in Acceptor, b \in Ballot, v \in Value :
                 VotedFor(a, b, v) => SafeAt(b, v)

OneVote == \A a \in Acceptor, b \in Ballot, v, w \in Value : 
              VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)

OneValuePerBallot ==  
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
       VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

Inv == TypeOK /\ VotesSafe /\ OneValuePerBallot

-----------------------------------------------------------------------------
(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)

Init == /\ votes = [a \in Acceptor |-> {}]
        /\ maxBal = [a \in Acceptor |-> -1]

IncreaseMaxBal(a, b) ==
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]
  /\ UNCHANGED votes

VoteFor(a, b, v) ==
  /\ maxBal[a] <= b
  /\ \A vt \in votes[a] : vt[1] # b
  /\ \A c \in Acceptor \ {a} :
        \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
  /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]

Next  == \E a \in Acceptor, b \in Ballot :
            \/ IncreaseMaxBal(a, b)
            \/ \E v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_<<votes, maxBal>>

=============================================================================