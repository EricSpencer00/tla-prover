---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (instantiated by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* Operators used by the .cfg to bind concrete finite versions
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Votes, Promise

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* A vote is a record with fields ballot and value
VoteRec == [ballot : Ballot, value : Value]

\* Safe(v,b)  –  value v is safe to vote for at ballot b
Safe(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E q \in Quorum :
        /\ q \subseteq Acceptor
        /\ \A a \in q :
             ( \E vt \in Votes[a] : vt.ballot = c /\ vt.value = v )
             \/ (c < Promise[a])

\* At most one value per ballot across all acceptors
OneValuePerBallot ==
  \A b \in Ballot :
    \E v \in Value :
      \A a \in Acceptor :
        ( \E vt \in Votes[a] : vt.ballot = b ) => 
          \A vt \in Votes[a] : vt.ballot = b => vt.value = v

\* Every vote that has been cast is safe
AllVotesSafe ==
  \A a \in Acceptor :
    \A vt \in Votes[a] :
      Safe(vt.value, vt.ballot)

\* Type correctness of the state
TypeOK ==
  /\ Votes \in [Acceptor -> SUBSET VoteRec]
  /\ Promise \in [Acceptor -> Int]

\* The global invariant
Inv == TypeOK /\ AllVotesSafe /\ OneValuePerBallot

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
  /\ Votes = [a \in Acceptor |-> {}]
  /\ Promise = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Increase promise threshold (no vote)
IncreasePromise ==
  \E a \in Acceptor, b \in Ballot :
    /\ b > Promise[a]
    /\ Promise' = [Promise EXCEPT ![a] = b]
    /\ Votes' = Votes
    /\ UNCHANGED << >>

\* 2. Cast a vote for value v at ballot b
CastVote ==
  \E a \in Acceptor, v \in Value, b \in Ballot :
    /\ b >= Promise[a]                                 \* not below current promise
    /\ \A vt \in Votes[a] : vt.ballot # b              \* hasn't voted in this ballot yet
    /\ \A a2 \in Acceptor :
         ( \E vt2 \in Votes[a2] : vt2.ballot = b ) =>
           (\A vt2 \in Votes[a2] : vt2.ballot = b => vt2.value = v)  \* no conflicting vote
    /\ Safe(v, b)                                      \* safety condition
    /\ Promise' = [Promise EXCEPT ![a] = b]
    /\ Votes'   = [Votes EXCEPT ![a] = Votes[a] \cup { [ballot |-> b, value |-> v] } ]
    /\ UNCHANGED << >>

Next == IncreasePromise \/ CastVote

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Votes, Promise>>

\* ----------------------------------------------------------------------
\* Derived notions for the consensus property
\* ----------------------------------------------------------------------
ChosenValues ==
  { v \in Value :
      \E b \in Ballot, q \in Quorum :
        /\ q \subseteq Acceptor
        /\ \A a \in q :
             \E vt \in Votes[a] : vt.ballot = b /\ vt.value = v }

ConsensusSpecBar == 
  \A v1, v2 \in Value :
    (v1 \in ChosenValues /\ v2 \in ChosenValues) => v1 = v2

\* ----------------------------------------------------------------------
\* Symmetry set (all permutations of Acceptor)
\* ----------------------------------------------------------------------
IsBijective(p) ==
  /\ DOMAIN p = Acceptor
  /\ RANGE p = Acceptor
  /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2

MCSymmetry == { p \in [Acceptor -> Acceptor] : IsBijective(p) }

====