---- MODULE Voting ----
\* This is a high-level algorithm in which a set of processes cooperatively
\* choose a value.
EXTENDS Integers, TLAPS
CONSTANTS Value,     \* The set of choosable values.
          Acceptor,  \* The set of processes that will each vote.
          Quorum     \* Nonempty sets of acceptors deemed sufficiently large

ASSUME /\ QuorumAssumption == \A Q \in Quorum : /\ Q \subseteq Acceptor
                                                /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
       /\ QuorumNonEmpty == \A Q \in Quorum : Q # {}

Ballot == Nat
VARIABLES votes, maxBal

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

VotedFor(a, b, v) == <<b, v>> \in votes[a]
\* An acceptor a has voted for v in ballot b.

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)
\* A quorum has all voted for v in ballot b.
chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

DidNotVoteAt(a, b) == \A v \in Value : ~VotedFor(a, b, v)
CannotVoteAt(a, b) == /\ maxBal[a] > b
                      /\ DidNotVoteAt(a, b)

NoneOtherChoosableAt(b, v) == 
  \E Q \in Quorum : \A a \in Q : (VotedFor(a, b, v) \/ CannotVoteAt(a, b))
\* If true, ChosenAt(b, w) is not and cannot become true for any w # v.
SafeAt(b, v) == \A c \in 0..(b-1) : NoneOtherChoosableAt(c, v)
VotesSafe == \A a, b, v : VotedFor(a, b, v) => SafeAt(b, v)
OneVote == \A a, b, v, w : VotedFor(a, b, v) /\ VotedFor(a, b, w) => (v = w)
OneValuePerBallot == 
  \A a1, a2, b, v1, v2 : VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

ShowsSafeAt(Q, b, v) == 
  /\ \A a \in Q : maxBal[a] >= b
  /\ \E c \in -1..(b-1) : /\ (c # -1) => \E a \in Q : VotedFor(a, c, v)
                          /\ \A d \in (c+1)..(b-1), a \in Q : DidNotVoteAt(a, d)

ShowsSafety == OneValuePerBallot => \A Q \in Quorum, b \in Ballot, v \in Value :
                  ShowsSafeAt(Q, b, v) => SafeAt(b, v)

Init == /\ votes = [a \in Acceptor |-> {}]
        /\ maxBal = [a \in Acceptor |-> -1]

IncreaseMaxBal(a, b) == /\ b > maxBal[a]
                       /\ maxBal' = [maxBal EXCEPT ![a] = b]
                       /\ UNCHANGED votes

VoteFor(a, b, v) == /\ maxBal[a] <= b
                    /\ \A vt \in votes[a] : vt[1] # b
                    /\ \A c \in Acceptor \ {a} : \A vt \in votes[c] : vt[1] = b => vt[2] = v
                    /\ \E Q \in Quorum : ShowsSafeAt(Q, b, v)
                    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
                    /\ maxBal' = [maxBal EXCEPT ![a] = b]

Next == \E a \in Acceptor, b \in Ballot : \/ IncreaseMaxBal(a, b)
                                      \/ \E v \in Value : VoteFor(a, b, v)
Spec == Init /\ [][Next]_<<votes, maxBal>>

Inv == TypeOK /\ VotesSafe /\ OneValuePerBallot

Invariance == Spec => []Inv

C == INSTANCE Consensus
TheoremSpec == Spec => C!Spec

====