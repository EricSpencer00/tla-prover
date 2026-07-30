---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

Restrict(a) ==
  \E b \in Ballot :
    /\ b >= threshold[a]
    /\ \A v \in Value : <<b, v>> \notin votes[a]
    /\ \A a2 \in Acceptor :
         \A v2 \in Value :
           (<<b, v2>> \in votes[a2]) => (v2 = v)
    /\ SafeValue(b, v)
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Propose(a) ==
  \E b \in Ballot :
    /\ b >= threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

Next ==
  \/ \E a \in Acceptor : Propose(a)
  \/ \E a \in Acceptor : Restrict(a)

Spec == Init /\ [][Next]_vars

\* A value is safe at ballot b if every lower ballot is quorified for it.
SafeValue(b, v) ==
  \A c \in Ballot :
    (c < b) =>
      (\E q \in Quorum :
         \A a \in q :
           \/ <<c, v>> \in votes[a]
           \/ \A d \in Ballot : d < c => <<d, v>> \in votes[a])

\* Every vote is safe at its ballot number.
AllVotesSafe ==
  \A a \in Acceptor :
    \A e \in votes[a] : SafeValue(e[1], e[2])

\* At most one value per ballot across all acceptors.
BallotUnique ==
  \A a1 \in Acceptor :
    \A a2 \in Acceptor :
      \A e1 \in votes[a1] :
        \A e2 \in votes[a2] :
          (e1[1] = e2[1]) => (e1[2] = e2[2])

Inv == TypeOK /\ AllVotesSafe /\ BallotUnique

\* Consistency: the set of chosen values is a subset of the values single-valued.
ConsensusSpecBar ==
  \A q1 \in Quorum :
    \A q2 \in Quorum :
      \A v1 \in Value :
        (\A a \in q1 : <<a1, v1>> \in votes[a]) =>
          \A v2 \in Value :
            (\A a \in q2 : <<a1, v2>> \in votes[a]) => (v1 = v2)

====