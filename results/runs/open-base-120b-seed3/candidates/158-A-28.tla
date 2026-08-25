---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(*--------------------------------------------------------------------
  Derived constants (used by the .cfg file)
--------------------------------------------------------------------*)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES votes, promise

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
VoteRec == [ballot : Ballot, value : Value]

TypeInvariant ==
    /\ votes \in [Acceptor -> SUBSET VoteRec]
    /\ promise \in [Acceptor -> Int]   \* may hold -1 as the initial value

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ promise = [a \in Acceptor |-> -1]

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
\* A quorum is a set of acceptors; Quorum is a constant set of such sets.
\* Overlap property (assumed as an additional assumption)
Overlap ==
    \A q1, q2 \in Quorum : q1 # q2 => q1 \cap q2 # {}

\* Safety of a value at ballot b
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) => 
            \E q \in Quorum :
                \A a \in q :
                    ( \E r \in votes[a] : r.ballot = c /\ r.value = v )
                     \/ (promise[a] > c)

\* No two different values are voted for in the same ballot
OneValuePerBallot ==
    \A b \in Ballot :
        \A a1, a2 \in Acceptor :
            \A r1 \in votes[a1] :
                \A r2 \in votes[a2] :
                    (r1.ballot = b /\ r2.ballot = b) => r1.value = r2.value

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
PromiseIncrease(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > promise[a]
    /\ UNCHANGED votes
    /\ promise' = [promise EXCEPT ![a] = b]

Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= promise[a]                     \* not below current promise
    /\ \A r \in votes[a] : r.ballot # b    \* a has not voted in b yet
    /\ \A a2 \in Acceptor :
          \A r2 \in votes[a2] :
              (r2.ballot = b) => r2.value = v   \* no other value in same ballot
    /\ Safe(v, b)                         \* value is safe at b
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ promise' = [promise EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : PromiseIncrease(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
vars == << votes, promise >>
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Invariant
--------------------------------------------------------------------*)
Inv == 
    /\ TypeInvariant
    /\ OneValuePerBallot
    /\ \A a \in Acceptor : \A r \in votes[a] : Safe(r.value, r.ballot)

(*--------------------------------------------------------------------
  Consensus property (at most one chosen value)
--------------------------------------------------------------------*)
Chosen(q, v, b) ==
    /\ q \in Quorum
    /\ \A a \in q :
          \E r \in votes[a] : r.ballot = b /\ r.value = v

ConsensusSpecBar ==
    \A v1, v2 \in Value, b1, b2 \in Ballot :
        ( \E q1 \in Quorum : Chosen(q1, v1, b1) ) /\ 
        ( \E q2 \in Quorum : Chosen(q2, v2, b2) ) => v1 = v2

(*--------------------------------------------------------------------
  Symmetry set (identity permutation)
--------------------------------------------------------------------*)
MCSymmetry == { [a \in Acceptor |-> a] }

====