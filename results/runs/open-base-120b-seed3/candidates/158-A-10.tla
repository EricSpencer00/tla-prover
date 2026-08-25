---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ---------- CONSTANT DECLARATIONS ----------
CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ---------- DERIVED CONSTANTS (overridden by the .cfg) ----------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ---------- STATE VARIABLES ----------
VARIABLES votes, thresh

\* votes[a] is the set of votes cast by acceptor a.
\* each vote is a record [ballot : Ballot, value : Value]
\* thresh[a] is the current promise threshold of acceptor a (an integer,
\*   initialised to -1 meaning no promise).

\* ---------- INITIAL STATE ----------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

\* ---------- HELPERS ----------
IsBijective(f) ==
    /\ DOMAIN f = Acceptor
    /\ RANGE f = Acceptor
    /\ \A x, y \in Acceptor : f[x] = f[y] => x = y

\* Overlap property of quorums (assumed true for all models)
QuorumOverlap ==
    \A q1, q2 \in Quorum : q1 # {} /\ q2 # {} => q1 \cap q2 # {}

\* Safe(v,b) : value v is safe at ballot b given the current votes and thresholds
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) => 
            \E q \in Quorum :
                \A a \in q :
                    ( \E vote \in votes[a] :
                        /\ vote.ballot = c
                        /\ vote.value  = v )
                    \/ (thresh[a] > c)   \* a can never vote in ballot c

\* No other value has been voted for in ballot b
NoConflictingVote(b) ==
    \A a1, a2 \in Acceptor :
        \A vote1 \in votes[a1] :
            \A vote2 \in votes[a2] :
                (vote1.ballot = b /\ vote2.ballot = b) => vote1.value = vote2.value

\* ---------- ACTIONS ----------
\* (1) Increase promise threshold without voting
PromiseIncrease ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > thresh[a]
            /\ thresh' = [thresh EXCEPT ![a] = b]
            /\ votes' = votes
            /\ UNCHANGED << >>

\* (2) Cast a vote for value v in ballot b
CastVote ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= thresh[a]                     \* not below current promise
                /\ ~(\E vote \in votes[a] : vote.ballot = b)   \* no prior vote in this ballot
                /\ NoConflictingVote(b)               \* no other acceptor voted a different value
                /\ Safe(v, b)                         \* safety condition
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup
                                 {[ballot |-> b, value |-> v]}]
                /\ thresh' = [thresh EXCEPT ![a] = b]
                /\ UNCHANGED << >>

Next == PromiseIncrease \/ CastVote

\* ---------- SPECIFICATION ----------
Spec == Init /\ [][Next]_<<votes, thresh>>

\* ---------- INVARIANTS ----------
\* Type correctness and safety of all votes
TypeInv ==
    /\ \A a \in Acceptor : votes[a] \subseteq {[ballot : Ballot, value : Value]} 
    /\ \A a \in Acceptor : thresh[a] \in Int

SafetyInv ==
    \A a \in Acceptor :
        \A vote \in votes[a] :
            Safe(vote.value, vote.ballot)

OneValuePerBallot ==
    \A b \in Ballot :
        LET vals == { v \in Value :
                        \E a \in Acceptor :
                            \E vote \in votes[a] :
                                /\ vote.ballot = b
                                /\ vote.value = v }
        IN Cardinality(vals) <= 1

Inv == TypeInv /\ SafetyInv /\ OneValuePerBallot /\ QuorumOverlap

\* ---------- CHOSEN VALUES ----------
ChosenValues ==
    { v \in Value :
        \E b \in Ballot :
            \E q \in Quorum :
                \A a \in q :
                    \E vote \in votes[a] :
                        /\ vote.ballot = b
                        /\ vote.value = v }

\* ---------- PROPERTY ----------
ConsensusSpecBar == Cardinality(ChosenValues) <= 1

\* ---------- SYMMETRY ----------
MCSymmetry ==
    { f \in [Acceptor -> Acceptor] : IsBijective(f) }

\* ---------- THEOREMS (optional) ----------
THEOREM Spec => []Inv
THEOREM Spec => []ConsensusSpecBar

====