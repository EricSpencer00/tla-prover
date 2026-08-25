---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets

\* ---------- Constants ----------
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ---------- Substitution aliases ----------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ---------- Concrete definitions (can be overridden in the .cfg) ----------
\* For the sake of a self‑contained module we give concrete values;
\* the model checker may replace them via the configuration file.
Acceptor == { a1, a2, a3 }
Value    == { v1, v2 }
\* A simple quorum system where every two quorums intersect.
Quorum   == { {a1, a2}, {a2, a3}, {a1, a3} }
Ballot   == 0..2

\* ---------- Variables ----------
VARIABLES votes, threshold

\* ---------- Helper definitions ----------
\* A vote is a record with fields ballot and value.
VoteRec == [ballot : Ballot, value : Value]

\* The set of all acceptors.
AcceptorSet == Acceptor

\* The set of all values.
ValueSet == Value

\* The set of all ballots.
BallotSet == Ballot

\* The minimal threshold (no promise made yet).
MinThresh == -1

\* Safety predicate for a value at a given ballot.
Safe(b, v) ==
  \A c \in BallotSet :
    (c < b) =>
      \E Q \in Quorum :
        \A a \in Q :
          ( \E vt \in votes[a] : vt.ballot = c /\ vt.value = v )
          \/ threshold[a] > c

\* A quorum has all its members voting for the same value in the same ballot.
Chosen(b, v) ==
  \E Q \in Quorum :
    \A a \in Q :
      [ballot |-> b, value |-> v] \in votes[a]

\* ---------- Initial state ----------
Init ==
  /\ votes = [a \in AcceptorSet |-> {}]
  /\ threshold = [a \in AcceptorSet |-> MinThresh]

\* ---------- Actions ----------
\* 1. Increase promise threshold without voting.
PromiseIncrease(a, b) ==
  /\ a \in AcceptorSet
  /\ b \in BallotSet
  /\ b > threshold[a]
  /\ UNCHANGED votes
  /\ threshold' = [threshold EXCEPT ![a] = b]

\* 2. Cast a vote for a value in a ballot.
CastVote(a, b, v) ==
  /\ a \in AcceptorSet
  /\ b \in BallotSet
  /\ v \in ValueSet
  /\ b >= threshold[a]                         \* not below current promise
  /\ \A vt \in votes[a] : vt.ballot # b        \* a has not voted in b yet
  /\ \A a2 \in AcceptorSet :
        a2 # a =>
          \A vt \in votes[a2] :
            vt.ballot = b => vt.value = v   \* no different value in same ballot
  /\ Safe(b, v)                               \* value is safe at b
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in AcceptorSet, b \in BallotSet : PromiseIncrease(a, b)
  \/ \E a \in AcceptorSet, b \in BallotSet, v \in ValueSet : CastVote(a, b, v)

\* ---------- Specification ----------
Spec ==
  Init /\ [][Next]_<<votes, threshold>>

\* ---------- Invariant ----------
Inv ==
  /\ \A a \in AcceptorSet : votes[a] \subseteq { vt \in VoteRec : TRUE }
  /\ \A a \in AcceptorSet : threshold[a] \in Int
  /\ \A a \in AcceptorSet :
        \A vt1, vt2 \in votes[a] :
          vt1.ballot = vt2.ballot => vt1.value = vt2.value
  /\ \A b \in BallotSet :
        (\E v \in ValueSet :
            \E a \in AcceptorSet : [ballot |-> b, value |-> v] \in votes[a])
        => (\A a2 \in AcceptorSet :
              \A vt \in votes[a2] :
                vt.ballot = b => (\E v' \in ValueSet :
                                   [ballot |-> b, value |-> v'] = vt
                                   /\ (\E a1 \in AcceptorSet :
                                          [ballot |-> b, value |-> v'] \in votes[a1])))
  /\ \A a \in AcceptorSet :
        \A vt \in votes[a] : Safe(vt.ballot, vt.value)

\* ---------- Property (Consensus) ----------
ConsensusSpecBar ==
  \A b1, b2 \in BallotSet :
    \A v1, v2 \in ValueSet :
      (Chosen(b1, v1) /\ Chosen(b2, v2)) => v1 = v2

\* ---------- Symmetry ----------
\* The identity permutation over Acceptor (sufficient for the configuration).
MCSymmetry == { [a \in AcceptorSet |-> a] }

====