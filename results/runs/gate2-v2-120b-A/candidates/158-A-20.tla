---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Acceptor, \* Set of acceptor identifiers
    Value,    \* Set of proposable values
    Quorum,   \* Set of quorums; each quorum is a subset of Acceptor
    Ballot    \* Set of ballot numbers (natural numbers)

\* ----------------------------------------------------------------------
\* Derived constants (not exported, but useful for readability)
\* ----------------------------------------------------------------------
AcceptorIDs == Acceptor
Values      == Value
Quorums     == Quorum
Ballots     == Ballot

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES votes, prom

\* votes   : [Acceptor -> SUBSET (Ballots X Values)]
\*           the set of (ballot, value) pairs each acceptor has cast
\* prom    : [Acceptor -> Nat]
\*           the current promise threshold of each acceptor

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Vote == [b : Ballots, v : Values]   \* a vote is a tuple (ballot, value)

AcceptorVotes(a) == votes[a]

(* Quorums satisfy the required overlap property *)
QuorumsOverlap ==
    \A q1, q2 \in Quorums : q1 # q2 => \E a \in Acceptor : a \in q1 /\ a \in q2

(* A quorum is a subset of Acceptor *)
QuorumsWellFormed ==
    \A q \in Quorums : q \subseteq Acceptor

\* The set of chosen values is the set of values that have been voted for by
\* a quorum in some ballot.
Chosen == { v \in Values :
            \E b \in Ballots :
                \E q \in Quorums :
                    \A a \in q : [b, v] \in votes[a] }

\* ----------------------------------------------------------------------
\* Safety predicate used in the invariant: a vote is safe at its ballot
\* ----------------------------------------------------------------------
Safe(b, v) ==
    \A c \in Ballots :
        (c < b) =>
            \E q \in Quorums :
                \A a \in q :
                    ([c, v] \in votes[a]) \/ (prom[a] > c)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ prom  = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Promise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballots
    /\ b > prom[a]
    /\ prom' = [prom EXCEPT ![a] = b]
    /\ UNCHANGED votes

Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballots
    /\ v \in Values
    /\ b >= prom[a]               \* ballot not below current promise
    /\ ~([b, v] \in votes[a])     \* acceptor has not already voted in ballot b
    /\ \A a2 \in Acceptor :
          ( [b, v] \in votes[a2] ) \/ (~\E v2 \in Values : [b, v2] \in votes[a2])
          \* No other acceptor has voted for a different value in same ballot
    /\ \E q \in Quorums :
          \A a2 \in q :
               ([b, v] \in votes[a2]) \/ (prom[a2] > b)
          \* There exists a quorum that makes the value safe at ballot b
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [b, v] }]
    /\ prom'  = [prom  EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballots : Promise(a, b)
    \/ \E a \in Acceptor, b \in Ballots, v \in Values : Vote(a, b, v)
    \/ UNCHANGED <<votes, prom>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, prom>>

\* ----------------------------------------------------------------------
\* Invariant required by the .cfg
\* ----------------------------------------------------------------------
Inv ==
    /\ \A a \in Acceptor :
          \A vb \in votes[a] :
              Safe(vb[1], vb[2])
    /\ \A b \in Ballots :
          \A v1, v2 \in Values :
            ( (\E a \in Acceptor : [b, v1] \in votes[a]) /\
              (\E a \in Acceptor : [b, v2] \in votes[a]) ) => v1 = v2
    /\ AcceptorVotes \in [Acceptor -> SUBSET (Ballots X Values)]
    /\ prom \in [Acceptor -> Nat]

\* ----------------------------------------------------------------------
\* Property that asserts the consensus spec: at most one value ever chosen
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
    \A v1, v2 \in Chosen : v1 = v2

\* ----------------------------------------------------------------------
\* Theorem (optional, but useful for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv

====