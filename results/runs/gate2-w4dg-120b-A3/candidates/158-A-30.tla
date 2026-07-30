---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Substitutions the .cfg file makes: the operators below supply the
\* bounded versions of the participant sets and ballot numbers.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

VotePairs == [ballot : Ballot, val : Value]
Quorums == Quorum

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET VotePairs]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* Raising a promise threshold without voting.
RaiseThreshold(a, b) ==
  /\ b \notin Ballot
  /\ (threshold[a] = -1 \/ b > threshold[a])
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Safe(v, b): every prior ballot has a unanimous supporting quorum for v.
Safe(v, b) ==
  /\ \A c \in Ballot :
       (c < b) =>
         \E Q \in Quorums :
           \A q \in Q :
             \/ \E p \in votes[q] : p.val = v /\ p.ballot = c
             \/ threshold[q] \notin Ballot \/ threshold[q] > c
  /\ \A a \in Acceptor :
       ~(\E p \in votes[a] : p.val = v /\ p.ballot < b)
  /\ TRUE

\* Casting a vote, which also raises the voter's threshold.
Cast(a, b, v) ==
  /\ b \in Ballot
  /\ threshold[a] \in {-1, b} \/ b > threshold[a]
  /\ \A p \in votes[a] : p.ballot # b
  /\ \A x \in Acceptor : \A p \in votes[x] : (p.ballot = b) => (p.val = v)
  /\ Safe(v, b)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[ballot |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor : \E b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor : \E b \in Ballot : \E v \in Value : Cast(a, b, v)

Spec == Init /\ [][Next]_vars

\* Consistency: at most one value is ever chosen (votes forming a quorum
\* for two values in two ballots must be the same value).
ConsensusSpecBar ==
  \A v \in Value :
    /\ (\E Q \in Quorums : \A q \in Q : \E p \in votes[q] : p.val = v)
    /\ (\A w \in Value :
          (\E R \in Quorums : \A r \in R : \E p \in votes[r] : p.val = w) => w = v)

Inv == TypeOK /\ ConsensusSpecBar

\* Symmetries: any swap of acceptors or of values preserves the spec.
MCSymmetry == {f \in [Acceptor -> Acceptor] : \A a \in Acceptor : f[a] \in Acceptor}
              \cup
              {f \in [Value -> Value] : \A v \in Value : f[v] \in Value}

====