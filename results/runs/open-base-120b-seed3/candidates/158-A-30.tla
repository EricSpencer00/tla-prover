---- MODULE Voting ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* Operators substituted by the .cfg file (bounded versions of the sets)
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES votes, prom

\* votes[a] is the set of votes cast by acceptor a.
\* Each vote is a record [ballot |-> b, value |-> v].
\* prom[a] is the current promise threshold (minimum ballot the acceptor may
\* participate in).  Initialized to -1.
\* ----------------------------------------------------------------------
Init ==
   /\ votes = [a \in Acceptor |-> {}]
   /\ prom  = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Safety predicate: a value v is safe at ballot b
\* ----------------------------------------------------------------------
Safe(v, b) ==
   \A c \in Ballot :
       (c < b) =>
          \E Q \in Quorum :
              /\ Q \subseteq Acceptor
              /\ \A a \in Q :
                    ( \E rec \in votes[a] :
                          /\ rec.ballot = c
                          /\ rec.value  = v )
                    \/ prom[a] > c

\* ----------------------------------------------------------------------
\* Action: an acceptor raises its promise threshold
\* ----------------------------------------------------------------------
Promote ==
   \E a \in Acceptor :
      \E b \in Ballot :
         /\ b > prom[a]
         /\ prom' = [prom EXCEPT ![a] = b]
         /\ UNCHANGED votes

\* ----------------------------------------------------------------------
\* Action: an acceptor casts a vote
\* ----------------------------------------------------------------------
Vote ==
   \E a \in Acceptor :
      \E v \in Value :
         \E b \in Ballot :
            /\ b >= prom[a]                                   \* not below threshold
            /\ ~(\E rec \in votes[a] : rec.ballot = b)        \* not already voted in b
            /\ (\A a2 \in Acceptor :
                   \A rec \in votes[a2] :
                       (rec.ballot = b) => rec.value = v)   \* no conflicting vote in b
            /\ Safe(v, b)                                     \* value is safe
            /\ votes' = [votes EXCEPT ![a] = votes[a] \cup
                         { [ballot |-> b, value |-> v] }]
            /\ prom'  = [prom EXCEPT ![a] = b]
            /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == \/ Promote \/ Vote

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<votes, prom>>
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeInv ==
   /\ votes \in [Acceptor -> SUBSET [ballot: Ballot, value: Value]]
   /\ prom  \in [Acceptor -> Int]

\* ----------------------------------------------------------------------
\* Every vote is safe at its ballot
\* ----------------------------------------------------------------------
AllVotesSafe ==
   \A a \in Acceptor :
      \A rec \in votes[a] :
         Safe(rec.value, rec.ballot)

\* ----------------------------------------------------------------------
\* At most one value per ballot across all acceptors
\* ----------------------------------------------------------------------
OneValuePerBallot ==
   \A b \in Ballot :
      \A v1, v2 \in Value :
         ( (\E a1 \in Acceptor : \E rec1 \in votes[a1] :
                rec1.ballot = b /\ rec1.value = v1) /\
           (\E a2 \in Acceptor : \E rec2 \in votes[a2] :
                rec2.ballot = b /\ rec2.value = v2) )
         => v1 = v2

\* ----------------------------------------------------------------------
\* Combined invariant
\* ----------------------------------------------------------------------
Inv == TypeInv /\ AllVotesSafe /\ OneValuePerBallot

\* ----------------------------------------------------------------------
\* Consensus property: at most one value can ever be chosen
\* (chosen = a quorum unanimously voting for a value in some ballot)
\* ----------------------------------------------------------------------
Chosen(v) ==
   \E b \in Ballot :
      \E Q \in Quorum :
         /\ Q \subseteq Acceptor
         /\ \A a \in Q :
               \E rec \in votes[a] :
                  rec.ballot = b /\ rec.value = v

ConsensusSpecBar ==
   \A v1, v2 \in Value :
      (Chosen(v1) /\ Chosen(v2)) => v1 = v2

\* ----------------------------------------------------------------------
\* Symmetry definition (identity permutation)
\* ----------------------------------------------------------------------
MCSymmetry == { [a \in Acceptor |-> a] }

====