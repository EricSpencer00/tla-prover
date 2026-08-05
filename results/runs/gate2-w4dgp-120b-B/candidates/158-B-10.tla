---- MODULE Voting ----
EXTENDS Integers, TLAPS

CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

\* In this algorithm, the ballot number is a single value shared by all
\* acceptors, not a per-acceptor value.  A quorum is a set of acceptors.
VARIABLES votes, maxBal, ballot

Ballot == Nat

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ maxBal \in Ballot \cup {-1}
  /\ ballot \in Ballot

VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

\* An acceptor will not vote in a ballot less than maxBal, so if it has not
\* voted in ballot b and maxBal > b it will never vote there either.
DidNotVoteAt(a, b) == \A v \in Value : ~VotedFor(a, b, v)
CannotVoteAt(a, b) == /\ maxBal > b
                      /\ DidNotVoteAt(a, b)

\* If this holds, then no other value can be chosen in ballot b.
NoneOtherChoosableAt(b, v) ==
  \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)

SafeAt(b, v) == \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)

OneVote == \A a \in Acceptor, b \in Ballot, v, w \in Value :
             (VotedFor(a, b, v) /\ VotedFor(a, b, w)) => (v = w)

OneValuePerBallot ==
  \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
    (VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2)) => (v1 = v2)

VotesSafe == \A a \in Acceptor, b \in Ballot, v \in Value :
               VotedFor(a, b, v) => SafeAt(b, v)

ShowsSafeAt(Q, b, v) ==
  /\ \A a \in Q : maxBal >= b
  /\ \E c \in -1..(b-1) :
       /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
       /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)

ShowsSafety ==
  OneValuePerBallot => (\A Q \in Quorum, b \in Ballot, v \in Value :
                          ShowsSafeAt(Q, b, v) => SafeAt(b, v))

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ maxBal = -1
  /\ ballot = 0

IncreaseMaxBal(b) ==
  /\ b > maxBal
  /\ maxBal' = b
  /\ UNCHANGED <<votes, ballot>>

VoteFor(a, b, v) ==
  /\ maxBal <= b
  /\ \A vt \in votes[a] : vt[1] # b
  /\ \A c \in Acceptor \ {a} :
       \A vt \in votes[c] : (vt[1] = b) => (vt[2] = v)
  /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ ballot' = IF b > ballot THEN b ELSE ballot
  /\ UNCHANGED maxBal

Next ==
  \/ \E b \in Ballot : IncreaseMaxBal(b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_<<votes, maxBal, ballot>>

Inv == TypeOK /\ VotesSafe /\ OneVote

====