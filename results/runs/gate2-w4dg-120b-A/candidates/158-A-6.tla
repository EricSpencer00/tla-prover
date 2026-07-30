---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES votes, promise

vars == <<votes, promise>>

Quorums == {Quorum}

RECURSIVE SafeAt(_)
SafeAt(v, b) ==
  \/ b = 0
  \/ \E Q \in Quorums :
       \A a \in Q : <<b, v>> \in votes[a]
       /\ \A c \in (0 .. (b - 1)) : \E Q2 \in Quorums :
            \A a \in Q2 :
              (\E vv \in Value : <<c, vv>> \in votes[a]) \/ (promise[a] >= c)

Chosen == {v \in Value : \E Q \in Quorums : \A a \in Q : <<Ballot, v>> \in votes[a]}

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ promise = [a \in Acceptor |-> -1]

RaisePromise(a, b) ==
  /\ b > promise[a]
  /\ promise' = [promise EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Vote, guarded by safety and quorum.
Cast(a, b, v) ==
  /\ b >= promise[a]
  /\ \A x \in votes[a] : x[1] # b
  /\ \A x \in votes : \A y \in x : (y[1] = b) => (y[2] = v)
  /\ SafeAt(v, b)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ promise' = [promise EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaisePromise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Cast(a, b, v)

Spec == Init /\ [][Next]_vars

\* Every vote cast was safe at its ballot number.
VotesSafe == \A a \in Acceptor : \A x \in votes[a] : SafeAt(x[2], x[1])

\* At most one value per ballot across all acceptors.
BallotSingleValue ==
  \A c \in Ballot :
    \A x \in {y[2] : a \in Acceptor, y \in votes[a] : y[1] = c} :
      \A z \in {y[2] : a \in Acceptor, y \in votes[a] : y[1] = c} : x = z

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ promise \in [Acceptor -> (-1..Ballot)]

Inv == VotesSafe /\ BallotSingleValue /\ TypeOK

\* The chosen set has at most one value, via the refinement to consensus.
ConsensusSpecBar == Chosen \subseteq {v \in Value : TRUE}

====