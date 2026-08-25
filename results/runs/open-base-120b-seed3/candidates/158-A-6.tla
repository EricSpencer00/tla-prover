---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Alias constants for model checking substitution
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, threshold

\* ---------- Helper definitions ----------
VoteRec == [ballot : Ballot, value : Value]

SafeAt(b, v) ==
  \A c \in Ballot :
    (c < b) =>
      \E Q \in Quorum :
        \A a \in Q :
          ( \E rec \in votes[a] :
                /\ rec.ballot = c
                /\ rec.value  = v )
          \/ threshold[a] > c

OneValuePerBallot ==
  \A b \in Ballot :
    \A a1 \in Acceptor, a2 \in Acceptor,
        rec1 \in votes[a1], rec2 \in votes[a2] :
      (rec1.ballot = b /\ rec2.ballot = b) => rec1.value = rec2.value

\* ---------- Initial state ----------
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* ---------- Actions ----------
Promise(a, b) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ b > threshold[a]
  /\ UNCHANGED votes
  /\ threshold' = [threshold EXCEPT ![a] = b]

Vote(a, b, v) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ v \in Value
  /\ b >= threshold[a]                 \* respects current promise
  /\ \A rec \in votes[a] : rec.ballot # b   \* hasn't voted in this ballot
  /\ \A a2 \in Acceptor :
        \A rec2 \in votes[a2] :
          (rec2.ballot = b) => rec2.value = v   \* no other value in same ballot
  /\ SafeAt(b, v)                     \* value is safe at this ballot
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<votes, threshold>>

\* ---------- Invariant ----------
Inv ==
  /\ \A a \in Acceptor : votes[a] \subseteq { VoteRec }
  /\ \A a \in Acceptor : threshold[a] \in Int
  /\ \A a \in Acceptor, rec \in votes[a] : SafeAt(rec.ballot, rec.value)
  /\ OneValuePerBallot

\* ---------- Chosen values ----------
Chosen ==
  { v \in Value :
      \E b \in Ballot, Q \in Quorum :
        \A a \in Q :
          \E rec \in votes[a] :
            /\ rec.ballot = b
            /\ rec.value  = v }

\* ---------- Property (consensus) ----------
ConsensusSpecBar ==
  \A v1, v2 \in Value :
    (v1 \in Chosen /\ v2 \in Chosen) => v1 = v2

\* ---------- Symmetry ----------
MCSymmetry ==
  { [a \in Acceptor |-> a] }   \* identity permutation (satisfies overlap assumption)

====