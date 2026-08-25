---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences, Permutations

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Substitution operators (used by the .cfg file)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, prom

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ votes \in [Acceptor -> SUBSET [ballot : Ballot, value : Value]]
  /\ prom  \in [Acceptor -> Int]

\* ----------------------------------------------------------------------
\* Safety definition
\* ----------------------------------------------------------------------
SafeAt(b, v) ==
  \A c \in Ballot :
    (c < b) => 
      \E Q \in Quorum :
        \A a \in Q :
          ( \E vt \in votes[a] :
                /\ vt.ballot = c
                /\ vt.value = v )
          \/ ( prom[a] > c )

AllVotesSafe ==
  \A a \in Acceptor :
    \A vt \in votes[a] :
      SafeAt(vt.ballot, vt.value)

AtMostOneValuePerBallot ==
  \A b \in Ballot :
    \A a1, a2 \in Acceptor :
      \A v1, v2 \in Value :
        ( (\E vt1 \in votes[a1] : vt1.ballot = b /\ vt1.value = v1) /\
          (\E vt2 \in votes[a2] : vt2.ballot = b /\ vt2.value = v2) )
        => v1 = v2

Inv == /\ TypeInvariant
       /\ AllVotesSafe
       /\ AtMostOneValuePerBallot

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ChosenValues ==
  { v \in Value :
      \E b \in Ballot :
        \E Q \in Quorum :
          \A a \in Q :
            \E vt \in votes[a] :
               vt.ballot = b /\ vt.value = v }

ConsensusSpecBar == Cardinality(ChosenValues) <= 1

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
PromiseIncrease(a, b) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ b > prom[a]
  /\ prom' = [prom EXCEPT ![a] = b]
  /\ votes' = votes

Vote(a, b, v) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ v \in Value
  /\ b >= prom[a]                 \* not below current promise
  /\ \A vt \in votes[a] : vt.ballot # b   \* a has not voted in b yet
  /\ \A a2 \in Acceptor :
        \A vt2 \in votes[a2] :
          (vt2.ballot = b) => vt2.value = v   \* no conflicting vote
  /\ SafeAt(b, v)                 \* there exists a quorum proving safety
  /\ prom' = [prom EXCEPT ![a] = b]
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]

Next ==
  \E a \in Acceptor :
    \E b \in Ballot :
      ( PromiseIncrease(a, b) \/ \E v \in Value : Vote(a, b, v) )

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ prom  = [a \in Acceptor |-> -1]

Spec == Init /\ [][Next]_<<votes, prom>>

\* ----------------------------------------------------------------------
\* Symmetry for model checking
\* ----------------------------------------------------------------------
MCSymmetry == { p \in [Acceptor -> Acceptor] : IsPermutation(p) }

\* ----------------------------------------------------------------------
\* Assumptions about quorums
\* ----------------------------------------------------------------------
QuorumOverlap ==
  \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

=============================================================================