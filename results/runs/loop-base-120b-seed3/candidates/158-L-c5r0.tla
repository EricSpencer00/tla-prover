---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Operators substituted by the .cfg file
MCAcceptor == Acceptor
MCValue   == Value
MCQuorum  == Quorum
MCBallot  == Ballot

VARIABLES votes, thresh

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
VoteRec == [ballot : Ballot, value : Value]

\* The set of all votes cast by any acceptor
AllVotes == { vt : VoteRec :
               \E a \in Acceptor : vt \in votes[a] }

\* A quorum is a member of the constant set Quorum (each element of Quorum is a set of acceptors)
\* Image of a set of acceptors under a function f
Image(f, S) == { f[a] : a \in S }

\* ----------------------------------------------------------------------
\* Safety predicate for a single vote
\* A vote (b,v) is safe if for every lower ballot c<b there exists a quorum Q
\* such that every member of Q either has already voted for v in c
\* or can never vote in c (its threshold is > c)
\* ----------------------------------------------------------------------
SafeVote(vt) ==
  LET b == vt.ballot IN
  LET val == vt.value IN
    \A c \in Ballot :
        (c < b) => 
          \E Q \in Quorum :
            \A a \in Q :
              ( \E w \in votes[a] : w.ballot = c /\ w.value = val )
              \/ ( thresh[a] > c )

\* ----------------------------------------------------------------------
\* At most one distinct value may be voted for in any given ballot
\* ----------------------------------------------------------------------
AtMostOneValuePerBallot ==
  \A b \in Ballot :
    \A v1, v2 \in Value :
      ( (\E a1 \in Acceptor : \E w1 \in votes[a1] : w1.ballot = b /\ w1.value = v1) /\
        (\E a2 \in Acceptor : \E w2 \in votes[a2] : w2.ballot = b /\ w2.value = v2) )
        => v1 = v2

\* ----------------------------------------------------------------------
\* Type‑correctness of the state
\* ----------------------------------------------------------------------
TypeCorrect ==
  /\ \A a \in Acceptor : votes[a] \subseteq VoteRec
  /\ \A a \in Acceptor : thresh[a] \in (Ballot \cup {-1})

\* ----------------------------------------------------------------------
\* The overall invariant required by the specification
\* ----------------------------------------------------------------------
Inv ==
  /\ TypeCorrect
  /\ AtMostOneValuePerBallot
  /\ \A a \in Acceptor : \A vt \in votes[a] : SafeVote(vt)

\* ----------------------------------------------------------------------
\* Definition of a chosen value (a value that a quorum has unanimously voted for
\* in some ballot)
\* ----------------------------------------------------------------------
Chosen ==
  { v \in Value :
      \E b \in Ballot :
        \E Q \in Quorum :
          \A a \in Q :
            \E w \in votes[a] : w.ballot = b /\ w.value = v }

\* ----------------------------------------------------------------------
\* Property stating that at most one value can ever be chosen
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
  \A v1, v2 \in Value :
    ( v1 \in Chosen /\ v2 \in Chosen ) => v1 = v2

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ votes = [ a \in Acceptor |-> {} ]
  /\ thresh = [ a \in Acceptor |-> -1 ]

\* ----------------------------------------------------------------------
\* Action: an acceptor raises its promise threshold
\* ----------------------------------------------------------------------
Promise ==
  \E a \in Acceptor :
    \E b \in Ballot :
      /\ b > thresh[a]
      /\ UNCHANGED votes
      /\ thresh' = [ thresh EXCEPT ![a] = b ]

\* ----------------------------------------------------------------------
\* Action: an acceptor casts a vote
\* ----------------------------------------------------------------------
Vote ==
  \E a \in Acceptor :
    \E b \in Ballot :
      \E v \in Value :
        /\ b >= thresh[a]                         \* respect current promise
        /\ ~(\E w \in votes[a] : w.ballot = b)    \* not voted in this ballot yet
        /\ \A a2 \in Acceptor :
              \A w \in votes[a2] :
                (w.ballot = b) => w.value = v   \* no conflicting vote
        /\ \E Q \in Quorum :
              \A a2 \in Q :
                ( \E w \in votes[a2] : w.ballot = b /\ w.value = v )
                \/ ( thresh[a2] > b )            \* quorum witnesses safety
        /\ votes' = [ votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] } ]
        /\ thresh' = [ thresh EXCEPT ![a] = b ]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == \/ Promise
        \/ Vote

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, thresh>>

\* ----------------------------------------------------------------------
\* Symmetry set: permutations of Acceptor that map quorums to quorums
\* ----------------------------------------------------------------------
MCSymmetry ==
  { p \in [Acceptor -> Acceptor] :
      /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2   \* bijection (injective on a finite set)
      /\ \A Q \in Quorum : Image(p, Q) \in Quorum }

====