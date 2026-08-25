---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* Operators used by the .cfg file to substitute finite versions
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES votes, promise

VoteRecord == [ballot : Ballot, value : Value]

\* ----------------------------------------------------------------------
\* Safety predicate for a value at a ballot
\* ----------------------------------------------------------------------
Safe(val, b) ==
  \A c \in Ballot :
    (c < b) => 
      \E Q \in Quorum :
        \A a \in Q :
          ( \E vr \in votes[a] : vr.ballot = c /\ vr.value = val )
          \/ (promise[a] > c)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ votes   = [a \in Acceptor |-> {}]
  /\ promise = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Action: increase promise threshold
\* ----------------------------------------------------------------------
IncreaseThreshold(a, b) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ b > promise[a]
  /\ UNCHANGED votes
  /\ promise' = [promise EXCEPT ![a] = b]

\* ----------------------------------------------------------------------
\* Action: cast a vote
\* ----------------------------------------------------------------------
CastVote(a, b, v) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ v \in Value
  /\ b >= promise[a]                           \* not below current promise
  /\ \A vr \in votes[a] : vr.ballot # b        \* a has not voted in b yet
  /\ \A a2 \in Acceptor :
        \A vr2 \in votes[a2] :
          (vr2.ballot = b) => (vr2.value = v) \* no conflicting vote in same ballot
  /\ Safe(v, b)                                 \* value is safe at b
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup
                         { [ballot |-> b, value |-> v] } ]
  /\ promise' = [promise EXCEPT ![a] = b]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E a \in Acceptor, b \in Ballot : IncreaseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<votes, promise>>

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
Inv ==
  /\ votes \in [Acceptor -> SUBSET VoteRecord]
  /\ promise \in [Acceptor -> Int]
  /\ \A a \in Acceptor :
        \A vr \in votes[a] : Safe(vr.value, vr.ballot)
  /\ \A b \in Ballot :
        \A v1, v2 \in Value :
          ( (\E a1 \in Acceptor : \E vr1 \in votes[a1] :
                vr1.ballot = b /\ vr1.value = v1) /\
            (\E a2 \in Acceptor : \E vr2 \in votes[a2] :
                vr2.ballot = b /\ vr2.value = v2) )
          => v1 = v2

\* ----------------------------------------------------------------------
\* Chosen values (a value chosen when a quorum has all voted for it in the same ballot)
\* ----------------------------------------------------------------------
ChosenValues ==
  { v \in Value :
      \E b \in Ballot, Q \in Quorum :
        \A a \in Q :
          \E vr \in votes[a] : vr.ballot = b /\ vr.value = v }

\* ----------------------------------------------------------------------
\* Property expressing consensus (at most one chosen value)
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
  \A v1, v2 \in Value :
    (v1 \in ChosenValues /\ v2 \in ChosenValues) => v1 = v2

\* ----------------------------------------------------------------------
\* Symmetry set: all permutations of the Acceptor set
\* ----------------------------------------------------------------------
IsPermutation(p) ==
  /\ p \in [Acceptor -> Acceptor]
  /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2
  /\ \A a \in Acceptor : \E b \in Acceptor : p[b] = a

MCSymmetry ==
  { p \in [Acceptor -> Acceptor] : IsPermutation(p) }

\* ----------------------------------------------------------------------
\* THE END
\* ----------------------------------------------------------------------
====