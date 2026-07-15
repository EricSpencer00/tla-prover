---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  Constants (to be instantiated in the .cfg file)                        *)
(*  a1      – a distinguished acceptor (not used directly, but required   *)
(*  Acceptor – the set of all acceptors                                    *)
(*  Value    – the set of all values that may be chosen                    *)
(*  Quorum   – the set of quorums, each quorum is a subset of Acceptor     *)
(*  Ballot   – the set of all ballot numbers (naturals)                    *)
(***************************************************************************)

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
BallotMinusOne == -1

\* A quorum overlaps every other quorum (assumed by .cfg or by a theorem)
QuorumsOverlap == 
  \A q1, q2 \in Quorum : q1 # q2 => q1 \cap q2 # {}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES votes, prom

\* votes[a] is the set of votes cast by acceptor a;
\* each vote is a record [b : Ballot, v : Value]
\* prom[a] is the promise threshold of acceptor a (the lowest ballot it
\*        will accept in the future)
Vote == [b : Ballot, v : Value]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ prom  = [a \in Acceptor |-> BallotMinusOne]

\* ----------------------------------------------------------------------
\* Safety predicate: a vote is safe at its ballot number
\* ----------------------------------------------------------------------
SafeVote(vote) ==
  LET b == vote.b
      val == vote.v
  IN
    \A c \in 0..b-1 :
      \E q \in Quorum :
        \A a \in q :
          ( [b |-> c, v |-> val] \in votes[a] ) \/ ( prom[a] > c )

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. An acceptor raises its promise threshold
RaiseProm(a) ==
  /\ a \in Acceptor
  /\ \E newB \in Ballot :
        /\ newB > prom[a]
        /\ prom' = [prom EXCEPT ![a] = newB]
        /\ UNCHANGED votes

\* 2. An acceptor casts a vote for a value in a ballot
VoteAction(a) ==
  /\ a \in Acceptor
  /\ \E b \in Ballot :
        /\ b >= prom[a]
        /\ \E val \in Value :
            /\ [b |-> b, v |-> val] \notin votes[a]               \* not voted in this ballot
            /\ \A a2 \in Acceptor :
                 ( [b |-> b, v |-> val] \in votes[a2] ) => a2 = a \* at most one vote per ballot
            /\ \E q \in Quorum :
                 \A a2 \in q :
                    ( [b |-> b, v |-> val] \in votes[a2] ) \/ ( prom[a2] > b )
            /\ /\ prom' = [prom EXCEPT ![a] = b]
               /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [b |-> b, v |-> val] }]
               /\ UNCHANGED <<>>

\* 3. Stuttering step (allows TLC to explore infinite behaviours)
Stutter ==
  UNCHANGED <<votes, prom>>

Next ==
  \/ \E a \in Acceptor : RaiseProm(a)
  \/ \E a \in Acceptor : VoteAction(a)
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, prom>>

\* ----------------------------------------------------------------------
\* Derived concepts
\* ----------------------------------------------------------------------
ChosenSet ==
  { v \in Value :
      \E b \in Ballot :
        \E q \in Quorum :
          \A a \in q : [b |-> b, v |-> v] \in votes[a] }

\* ----------------------------------------------------------------------
\* Invariant required by the .cfg
\* ----------------------------------------------------------------------
Inv ==
  /\ \A a \in Acceptor : prom[a] \in BallotMinusOne \cup Ballot
  /\ \A a \in Acceptor :
        \A vote \in votes[a] :
            /\ vote.b \in Ballot
            /\ vote.v \in Value
            /\ SafeVote(vote)
  /\ \A b \in Ballot :
        \A a1, a2 \in Acceptor :
            ( [b |-> b, v |-> v] \in votes[a1] /\ [b |-> b, v |-> v2] \in votes[a2] )
                => v = v2
  /\ ~ ( Cardinality(ChosenSet) > 1 )   \* at most one value is ever chosen

\* ----------------------------------------------------------------------
\* Safety property (consensus) – the property required by the .cfg
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
  ~ ( Cardinality(ChosenSet) > 1 )

=============================================================================