---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
BallotSet == Nat
Vote == [ballot : BallotSet, value : Value]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES votes, threshold

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all possible votes for a given ballot
BallotVotes(b) == { v \in votes : v.ballot = b }

\* The set of values voted for in a given ballot
BallotValues(b) == { v.value : v \in BallotVotes(b) }

\* A quorum is safe for a value at ballot b if every member of the quorum
\* has either voted for that value in some lower ballot or can never vote
\* in that lower ballot.  For the abstract model we simply require that
\* the value appears in the votes of all members of the quorum in some
\* lower ballot.
SafeAt(v, b) ==
    \A c \in 0..(b-1) :
        \E q \in Quorum :
            \A a \in q :
                \E v' \in votes :
                    v'.ballot = c /\ v'.value = v

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ votes = {}
    /\ threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Promise action: an acceptor raises its threshold to a higher ballot
Promise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* Vote action: an acceptor votes for a value in a ballot, subject to the
\* four conditions described in the natural-language description.
VoteAction(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= threshold[a]
    /\ \A v' \in votes : (v'.ballot = b) => (v'.value = v)
    /\ \A q \in Quorum :
            \A a' \in q :
                \A v' \in votes :
                    (v'.ballot = b /\ v'.value # v) => FALSE
    /\ SafeAt(v, b)
    /\ votes' = votes \cup { [ballot |-> b, value |-> v] }
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                VoteAction(a, b, v)
    \/ \E a \in Acceptor :
        \E b \in Ballot :
            Promise(a, b)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, threshold>>

\* ----------------------------------------------------------------------
\* Invariant: every vote is safe at its ballot number
Inv ==
    \A v \in votes : SafeAt(v.value, v.ballot)

\* ----------------------------------------------------------------------
\* Property: the chosen set contains at most one value
ConsensusSpecBar ==
    \A b1, b2 \in Ballot :
        \A v1, v2 \in Value :
            ( \E q1 \in Quorum : \A a \in q1 : v1 \in { v.value : v \in votes /\ v.ballot = b1 } ) /\
            ( \E q2 \in Quorum : \A a \in q2 : v2 \in { v.value : v \in votes /\ v.ballot = b2 } ) =>
            v1 = v2

====