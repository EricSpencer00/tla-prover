---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

\* ---------- CONSTANTS ----------
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ---------- CONSTANT DEFINITIONS ----------
Acceptor == {a1, a2, a3}
Value    == {v1, v2}
\* Example quorum collection satisfying the overlap property
Quorum   == {{a1, a2}, {a2, a3}}
Ballot   == Nat          \* model checking will bound this set (e.g., 0..2)

\* ---------- STATE VARIABLES ----------
VARIABLES Votes, Threshold

\* ---------- INITIAL STATE ----------
Init ==
  /\ \A a \in Acceptor : Votes[a] = {}
  /\ \A a \in Acceptor : Threshold[a] = -1

\* ---------- HELPERS ----------
VoteRec == [ballot : Ballot, value : Value]

Safe(b, v) ==
  \A c \in Ballot :
    (c < b) =>
      \E Q \in Quorum :
        \A a \in Q :
          ( \E vote \in Votes[a] :
                /\ vote.ballot = c
                /\ vote.value = v )
          \/ (Threshold[a] > c)

AllVotesSafe ==
  \A a \in Acceptor :
    \A vote \in Votes[a] :
      Safe(vote.ballot, vote.value)

AtMostOneValuePerBallot ==
  \A b \in Ballot :
    ( \E v \in Value :
        \A a \in Acceptor :
          \A vote \in Votes[a] :
            (vote.ballot = b) => (vote.value = v) )
    \/ ~(\E a \in Acceptor : \E vote \in Votes[a] : vote.ballot = b)

TypeInv ==
  /\ \A a \in Acceptor : Votes[a] \subseteq { VoteRec }
  /\ \A a \in Acceptor : Threshold[a] \in Ballot \cup {-1}

Inv == 
  /\ TypeInv
  /\ AllVotesSafe
  /\ AtMostOneValuePerBallot

\* ---------- ACTIONS ----------
PromiseIncrease ==
  \E a \in Acceptor :
    \E b \in Ballot :
      /\ b > Threshold[a]
      /\ Threshold' = [Threshold EXCEPT ![a] = b]
      /\ UNCHANGED Votes

Vote ==
  \E a \in Acceptor :
    \E b \in Ballot :
      \E v \in Value :
        /\ b >= Threshold[a]
        /\ \A vote \in Votes[a] : vote.ballot # b
        /\ \A a2 \in Acceptor :
             \A vote2 \in Votes[a2] :
               (vote2.ballot = b) => (vote2.value = v)
        /\ Safe(b, v)
        /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup {{ballot |-> b, value |-> v}}]
        /\ Threshold' = [Threshold EXCEPT ![a] = b]

Next == 
  \/ PromiseIncrease
  \/ Vote

\* ---------- SPECIFICATION ----------
Spec == Init /\ [][Next]_<<Votes, Threshold>>

\* ---------- CONSENSUS PROPERTY ----------
ChosenVals ==
  { v \in Value :
      \E b \in Ballot :
        \E Q \in Quorum :
          \A a \in Q :
            \E vote \in Votes[a] :
              /\ vote.ballot = b
              /\ vote.value = v }

ConsensusSpecBar ==
  \A v1, v2 \in Value :
    (v1 # v2) => ~(v1 \in ChosenVals /\ v2 \in ChosenVals)

\* ---------- SYMMETRY ----------
MCSymmetry ==
  { p \in [Acceptor -> Acceptor] :
      /\ p \in Permutations(Acceptor)
      /\ \A Q \in Quorum : p[Q] \in Quorum }

\* ---------- MC REPLACEMENTS ----------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

====