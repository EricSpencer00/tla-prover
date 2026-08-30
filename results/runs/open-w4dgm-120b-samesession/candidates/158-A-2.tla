---- MODULE Voting ----
EXTENDS Integers, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

Votes == [ball : Ballot, val : Value]
QuorumsOf(v) == {Q \in Quorum : \A x \in Q : x \in Acceptor}
Voted(a) == {cv \in votes[a] : TRUE}

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Votes]
  /\ threshold \in [Acceptor -> Ballot]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

Cast(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A cv \in votes[a] : cv.ball # b
  /\ \A x \in Acceptor : \A cv \in votes[x] : (cv.ball = b) => (cv.val = v)
  /\ \E Q \in QuorumsOf(v) :
       \A x \in Q : (\A cv \in votes[x] : cv.ball < b) \/ (\E cv \in votes[x] : cv.val = v)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Raise(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

Next ==
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Cast(a, b, v)
  \/ \E a \in Acceptor, b \in Ballot : Raise(a, b)

Spec == Init /\ [][Next]_vars

VoteSafe ==
  \A a \in Acceptor : \A cv \in votes[a] :
    \A Q \in QuorumsOf(cv.val) :
      (\A x \in Q : (\A cv2 \in votes[x] : cv2.ball < cv.ball) \/ (\E cv2 \in votes[x] : cv2.val = cv.val))
        \/ (cv.ball = 0 /\ \A x \in Q : votes[x] = {})

BallotUnique == \A a, x \in Acceptor : \A cv, cx \in votes[a] \X votes[x] :
  (cv.ball = cx.ball) => (cv.val = cx.val)

NoBadStates == TypeOK /\ VoteSafe /\ BallotUnique

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

QuorumOverlap ==
  \A Q1, Q2 \in Quorum : \E x \in Q1 \cap Q2 : TRUE

ConsensusSpecBar == QuorumOverlap /\ NoBadStates

MCSymmetry == { (<<a1, a2, a3>>, <<a2, a1, a3>>) }

====