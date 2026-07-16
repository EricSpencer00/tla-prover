---- MODULE Voting --------------------------------------------------------------
EXTENDS Integers, TLAPS

CONSTANT Value,     \* Set of choosable values.
         Acceptor,  \* Set of processes (acceptors).
         Quorum     \* Set of quorums (each a non‑empty subset of Acceptor).

\*-------------------- Assumptions about quorums -----------------------------
ASSUME QuorumAssumption == 
          /\ \A Q \in Quorum : Q \subseteq Acceptor
          /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}

\*-------------------- Ballots ---------------------------------------------
Ballot == Nat           \* Alias for natural numbers.

\*-------------------- Variables -------------------------------------------
VARIABLES votes, maxBal   \* See comments below.

\*-------------------- Type correctness invariant -------------------------
TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

\*-------------------- Helper definitions ---------------------------------
VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) == \E Q \in Quorum :
                     \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v)

CannotVoteAt(a, b) == 
    /\ maxBal[a] > b
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

\*-------------------- Theorems (unchanged) -------------------------------
THEOREM AllSafeAtZero == \A v \in Value : SafeAt(0, v)

THEOREM ChoosableThm ==
   \A b \in Ballot, v \in Value :
        ChosenAt(b, v) => NoneOtherChoosableAt(b, v)

THEOREM OneValuePerBallot => OneVote

THEOREM ShowsSafety ==
   TypeOK /\ VotesSafe /\ OneValuePerBallot =>
      \A Q \in Quorum, b \in Ballot, v \in Value :
          ShowsSafeAt(Q, b, v) => SafeAt(b, v)

THEOREM VotesSafeImpliesConsistency ==
   /\ TypeOK 
   /\ VotesSafe
   /\ OneVote
   => \/ chosen = {}
      \/ \E v \in Value : chosen = {v}

\*-------------------- Specification ---------------------------------------
Init ==
   /\ votes = [a \in Acceptor |-> {}]
   /\ maxBal = [a \in Acceptor |-> -1]

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
   /\ \A vt \in votes[a] : vt[1] # b          \* no previous vote by a in ballot b
   /\ \A c \in Acceptor \ {a} :
        \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)   \* all votes in b agree on value
   /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
   /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
   /\ maxBal' = [maxBal EXCEPT ![a] = b]

Next ==
   \/ \E a \in Acceptor, b \in Ballot : IncreaseMaxBal(a, b)
   \/ \E a \in Acceptor, b \in Ballot, v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_<<votes, maxBal>>

Inv == TypeOK /\ VotesSafe /\ OneValuePerBallot

THEOREM Invariance == Spec => []Inv

\*-------------------- Instantiation of Consensus (unchanged) ------------
C == INSTANCE Consensus

THEOREM Spec => C!Spec
<1>1. Inv /\ Init => C!Init
<1>2. Inv /\ [Next]_<<votes, maxBal>> => [C!Next]_chosen
<1>3. QED
  BY <1>1, <1>2, Invariance, PTL DEF Spec, C!Spec

=============================================================================