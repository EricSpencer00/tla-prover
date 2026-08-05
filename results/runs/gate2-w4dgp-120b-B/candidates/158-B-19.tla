---- MODULE Voting ----
EXTENDS Integers, TLAPS
CONSTANT Value, Acceptors, Quorums
ASSUME QuorumsAssume == /\ \A q \in Quorums : q \subseteq Acceptors
                    /\ \A q1, q2 \in Quorums : q1 \cap q2 # {}
Ballot == Nat
VARIABLES votes, maxBal
TypeOK == /\ votes \in [Acceptors -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptors -> Ballot \cup {-1}]
VotedFor(a, b, v) == <<b, v>> \in votes[a]
ChosenAt(b, v) == \E q \in Quorums : \A a \in q : VotedFor(a, b, v)
Chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}
DidNotVoteAt(a, b) == \A v \in Value : ~ VotedFor(a, b, v)
CannotVoteAt(a, b) == /\ maxBal[a] > b /\ DidNotVoteAt(a, b)
NotChoosableAt(b, v) == \E q \in Quorums : \A a \in q : VotedFor(a, b, v) \/ CannotVoteAt(a, b)
SafeAt(b, v) == \A c \in 0..(b-1) : NotChoosableAt(c, v)
AllSafeAtZero == \A v \in Value : SafeAt(0, v)
ChoosableThm == \A b \in Ballot, v \in Value : ChosenAt(b, v) => NotChoosableAt(b, v)
VotesSafe == \A a \in Acceptors, b \in Ballot, v \in Value : VotedFor(a, b, v) => SafeAt(b, v)
OneVote == \A a \in Acceptors, b \in Ballot, v, w \in Value :
              (VotedFor(a, b, v) /\ VotedFor(a, b, w)) => v = w
OneValuePerBallot == \A a1, a2 \in Acceptors, b \in Ballot, v1, v2 \in Value :
                       (VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2)) => v1 = v2
OneValueImpliesOneVote == OneValuePerBallot => OneVote
ShowsSafeAt(q, b, v) ==
    /\ \A a \in q : maxBal[a] >= b
    /\ \E c \in -1..(b-1) : (c # -1 => \E a \in q : VotedFor(a, c, v))
              /\ \A d \in (c+1)..(b-1), a \in q : DidNotVoteAt(a, d)
ShowsSafety == TypeOK /\ VotesSafe /\ OneValuePerBallot =>
               \A q \in Quorums, b \in Ballot, v \in Value : ShowsSafeAt(q, b, v) => SafeAt(b, v)
Init == /\ votes = [a \in Acceptors |-> {}]
        /\ maxBal = [a \in Acceptors |-> -1]
IncreaseMaxBal(a, b) == /\ b > maxBal[a]
                        /\ maxBal' = [maxBal EXCEPT ![a] = b]
                        /\ UNCHANGED votes
VoteFor(a, b, v) == /\ maxBal[a] <= b
                    /\ \A vt \in votes[a] : vt[1] # b
                    /\ \A c \in Acceptors \ {a} : \A vt \in votes[c] : vt[1] = b => vt[2] = v
                    /\ \E q \in Quorums : ShowsSafeAt(q, b, v)
                    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
                    /\ maxBal' = [maxBal EXCEPT ![a] = b]
Next == \E a \in Acceptors, b \in Ballot : IncreaseMaxBal(a, b) \/ (\E v \in Value : VoteFor(a, b, v))
Spec == Init /\ [][Next]_<<votes, maxBal>>
Inv == TypeOK /\ VotesSafe /\ OneValuePerBallot
Invariance == Spec => []Inv
C == INSTANCE Consensus
SpecImpliesCSpec == Spec => C!Spec

====