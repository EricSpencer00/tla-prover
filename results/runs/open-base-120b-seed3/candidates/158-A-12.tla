---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ---------- CONSTANTS ----------
CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ---------- TYPE DEFINITIONS ----------
VoteRec == [ballot : Ballot, value : Value]

\* ---------- STATE VARIABLES ----------
VARIABLES votes, thresh

\* ---------- INITIAL STATE ----------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

\* ---------- HELPERS ----------
\* A quorum is any element of the constant set Quorum
QuorumSet(q) == q \in Quorum

\* Safety of a value v at ballot b within a given quorum Q
SafeInQuorum(Q, b, v) ==
    /\ Q \in Quorum
    /\ \A a \in Q :
        \A c \in Nat :
            c < b =>
                ( (\E w \in votes[a] : w.ballot = c /\ w.value = v)
                  \/ (thresh[a] > c) )

\* A value is safe at ballot b if there exists a quorum proving it
SafeAt(b, v) ==
    \E Q \in Quorum : SafeInQuorum(Q, b, v)

\* No two different values have been voted for in the same ballot
OneValuePerBallot ==
    \A b \in Ballot :
        \A v1, v2 \in Value :
            ( (\E a1 \in Acceptor : \E w1 \in votes[a1] :
                    w1.ballot = b /\ w1.value = v1)
              /\ (\E a2 \in Acceptor : \E w2 \in votes[a2] :
                    w2.ballot = b /\ w2.value = v2) )
            => v1 = v2

\* Each acceptor votes at most once per ballot
NoDuplicateBallots ==
    \A a \in Acceptor :
        \A w1, w2 \in votes[a] :
            w1.ballot = w2.ballot => w1 = w2

\* ---------- ACTIONS ----------
\* Promise: an acceptor raises its threshold
Promise(a, newB) ==
    /\ a \in Acceptor
    /\ newB \in Ballot
    /\ newB > thresh[a]
    /\ UNCHANGED votes
    /\ thresh' = [thresh EXCEPT ![a] = newB]

\* Vote: an acceptor casts a vote for value v in ballot b
Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= thresh[a]                     \* not below current promise
    /\ \A w \in votes[a] : w.ballot # b   \* not already voted in this ballot
    /\ \A a2 \in Acceptor :
          \A w2 \in votes[a2] :
              (w2.ballot = b) => (w2.value = v)   \* no conflicting vote
    /\ \E Q \in Quorum : SafeInQuorum(Q, b, v)   \* safety quorum exists
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor : \E nb \in Ballot : Promise(a, nb)
    \/ \E a \in Acceptor : \E b \in Ballot : \E v \in Value : Vote(a, b, v)

\* ---------- SPECIFICATION ----------
Spec ==
    Init /\ [][Next]_<<votes, thresh>>

\* ---------- INVARIANT ----------
Inv ==
    /\ votes \in [Acceptor -> SUBSET VoteRec]
    /\ thresh \in [Acceptor -> Ballot]
    /\ NoDuplicateBallots
    /\ OneValuePerBallot
    /\ \A a \in Acceptor : \A w \in votes[a] : SafeAt(w.ballot, w.value)

\* ---------- CHOSEN VALUES ----------
Chosen(v) ==
    \E b \in Ballot :
        \E Q \in Quorum :
            \A a \in Q :
                \E w \in votes[a] :
                    w.ballot = b /\ w.value = v

ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (Chosen(v1) /\ Chosen(v2)) => v1 = v2

\* ---------- SYMMETRY ----------
\* The set of all bijections (permutations) on Acceptor
MCSymmetry ==
    { p \in [Acceptor -> Acceptor] :
        /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2   \* injective
        /\ \A a \in Acceptor : \E a0 \in Acceptor : p[a0] = a }   \* surjective

\* ---------- MC OPERATORS (substituted by the .cfg) ----------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ---------- THEOREMS ----------
THEOREM Spec => []Inv
THEOREM Spec => []ConsensusSpecBar

====