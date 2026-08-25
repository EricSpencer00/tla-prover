---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    a1, a2, a3,
    v1, v2,
    Acceptor,   \* set of acceptors
    Value,      \* set of values
    Quorum,     \* set of quorum subsets of Acceptor
    Ballot      \* set of ballot numbers (natural numbers)

\* ----------------------------------------------------------------------
\* Symmetry definition (permutations of Acceptor)
\* ----------------------------------------------------------------------
IsPermutation(p) ==
    /\ DOMAIN p = Acceptor
    /\ RANGE p = Acceptor
    /\ \A x, y \in Acceptor : p[x] = p[y] => x = y

MCSymmetry == { p \in [Acceptor -> Acceptor] : IsPermutation(p) }

\* ----------------------------------------------------------------------
\* Operators that the .cfg substitutes (aliases for the constant sets)
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* State variables
\*   votes[a]    : the set of votes cast by acceptor a
\*                each vote is a record [ballot |-> b, value |-> v]
\*   threshold[a]: the minimal ballot number a will vote in from now on
\*                -1 means no promise has been made yet
\* ----------------------------------------------------------------------
VARIABLES votes, threshold

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
VoteRecord == [ballot : Ballot, value : Value]

\* A vote for value v in ballot b is safe if for every lower ballot c
\* there exists a quorum all of whose members have either already voted
\* for v in c or are promised to a higher ballot (> c).
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E q \in Quorum :
                \A a \in q :
                    ( \E vr \in votes[a] :
                          vr.ballot = c /\ vr.value = v )
                  \/ (threshold[a] > c)

\* The set of values that have been chosen (i.e., some quorum has unanimously
\* voted for the value in the same ballot).
ChosenValues ==
    { v \in Value :
        \E b \in Ballot, q \in Quorum :
            \A a \in q :
                \E vr \in votes[a] :
                    vr.ballot = b /\ vr.value = v }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Promise: an acceptor raises its threshold without voting.
Promise ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > threshold[a]
            /\ threshold' = [threshold EXCEPT ![a] = b]
            /\ votes' = votes

\* Vote: an acceptor casts a vote for value v in ballot b.
Vote ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= threshold[a]
                /\ \A vr \in votes[a] : vr.ballot # b        \* not voted in this ballot yet
                /\ \A a2 \in Acceptor :
                        (\E vr2 \in votes[a2] : vr2.ballot = b) =>
                        (\A vr2 \in votes[a2] : vr2.ballot = b => vr2.value = v)
                /\ Safe(v, b)
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
                /\ threshold' = [threshold EXCEPT ![a] = b]

Next == \/ Promise \/ Vote

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, threshold>>

\* ----------------------------------------------------------------------
\* Invariant
\*   (1) Every vote recorded is safe.
\*   (2) At most one distinct value is voted for in any given ballot.
\*   (3) Thresholds are integers ≥ -1.
\* ----------------------------------------------------------------------
Inv ==
    /\ \A a \in Acceptor :
          \A vr \in votes[a] : Safe(vr.value, vr.ballot)
    /\ \A b \in Ballot :
          \A v1, v2 \in Value :
              ( (\E a1 \in Acceptor : \E vr1 \in votes[a1] : vr1.ballot = b /\ vr1.value = v1) /\
                (\E a2 \in Acceptor : \E vr2 \in votes[a2] : vr2.ballot = b /\ vr2.value = v2) )
              => v1 = v2
    /\ \A a \in Acceptor : threshold[a] \in Int

\* ----------------------------------------------------------------------
\* Safety property: at most one value can be chosen.
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
    \A v1, v2 \in ChosenValues : v1 = v2

====