---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Acceptor, \* Set of acceptor identifiers
    Value,    \* Set of possible values
    Quorum,   \* Set of quorums, each quorum is a subset of Acceptor
    Ballot    \* Set of ballot numbers (natural numbers, bounded in the .cfg)

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
Vote == [b : Ballot, v : Value]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    votes,      \* votes[acc] is the set of votes cast by acceptor acc
    threshold   \* threshold[acc] is the smallest ballot number acc will accept

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Quorums must overlap – this is assumed in the .cfg but we keep a definition
OverlapQuorums ==
    /\ \A q1, q2 \in Quorum : q1 # q2 => q1 \cap q2 # {}

\* A quorum q is said to "support" a value v at ballot b if every member
\* either has already voted for v at b or has a threshold > b (i.e., can never
\* vote in ballot b).
Support(q, b, v) ==
    \A a \in q :
        ( \E w \in votes[a] : w.b = b /\ w.v = v )
        \/ threshold[a] > b

\* A value v is safe at ballot b if for every lower ballot c (< b) there exists
\* a quorum supporting v at c.
SafeAt(v, b) ==
    \A c \in Ballot :
        c < b => \E q \in Quorum : Support(q, c, v)

\* The set of chosen values: a value is chosen if a quorum has voted for it
\* in the same ballot.
ChosenSet ==
    { v \in Value :
        \E b \in Ballot :
            \E q \in Quorum :
                \A a \in q :
                    \E w \in votes[a] : w.b = b /\ w.v = v }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. RaisePromise: an acceptor may increase its threshold to any higher ballot
RaisePromise ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > threshold[a]
            /\ threshold' = [threshold EXCEPT ![a] = b]
            /\ UNCHANGED votes

\* 2. VoteAction: an acceptor votes for a value in a ballot
VoteAction ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= threshold[a]                         \* not below promise
                /\ \A w \in votes[a] : w.b # b               \* hasn't voted in b yet
                /\ \A a2 \in Acceptor :
                       \A w \in votes[a2] :
                           (w.b = b) => (w.v = v)            \* at most one value per ballot
                /\ SafeAt(v, b)                               \* safety condition
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [b |-> b, v |-> v] }]
                /\ threshold' = [threshold EXCEPT ![a] = b]
                /\ UNCHANGED << >>

\* The next-step relation
Next ==
    \/ RaisePromise
    \/ VoteAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, threshold>>

\* ----------------------------------------------------------------------
\* Invariant required by the cfg
\* ----------------------------------------------------------------------
Inv ==
    /\ \A a \in Acceptor :
          \A w \in votes[a] : SafeAt(w.v, w.b)          \* every vote is safe
    /\ \A b \in Ballot :
          \A a1, a2 \in Acceptor :
              ( \E w1 \in votes[a1] : w1.b = b ) /\ ( \E w2 \in votes[a2] : w2.b = b )
              => \A w1 \in votes[a1] : \A w2 \in votes[a2] :
                     (w1.b = b /\ w2.b = b) => w1.v = w2.v   \* at most one value per ballot
    /\ OverlapQuorums                                 \* quorums overlap (assumed)

\* ----------------------------------------------------------------------
\* Property representing the abstract consensus specification
\* (the chosen set never contains more than one distinct value)
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
    \A v1, v2 \in ChosenSet : v1 = v2

=============================================================================