---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    a1, a2, a3,
    v1, v2,
    Acceptor,          \* set of acceptors
    Value,             \* set of values
    Quorum,            \* set of subsets of Acceptor (each element is a quorum)
    Ballot             \* set of ballot numbers (naturals, bounded in the model)

\* ----------------------------------------------------------------------
\* Operators that the .cfg file may substitute (they are simply aliases)
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    Votes,      \* [Acceptor -> SUBSET [ballot : Ballot, value : Value]]
    Promised    \* [Acceptor -> Int]   (the promise threshold; -1 means no promise)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
VoteRec(b, v) == [ballot |-> b, value |-> v]

\* A quorum is a set of acceptors; the model assumes the overlap property
QuorumOverlap == 
    \A Q1, Q2 \in Quorum : Q1 # Q2 => Q1 \cap Q2 # {}

\* Safety predicate: a value v is safe at ballot b
Safe(v, b) == 
    \A c \in Ballot :
        (c < b) => 
            \E Q \in Quorum :
                \A a \in Q :
                    (VoteRec(c, v) \in Votes[a]) \/ (Promised[a] > c)

\* The set of values that have been chosen (a quorum of acceptors all
\* voted for the same value in the same ballot)
ChosenVals == { v \in Value :
                \E b \in Ballot :
                    \E Q \in Quorum :
                        \A a \in Q : VoteRec(b, v) \in Votes[a] }

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ Votes = [a \in Acceptor |-> {}]
    /\ Promised = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Increase promise threshold without voting
Promise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > Promised[a]
    /\ UNCHANGED Votes
    /\ Promised' = [Promised EXCEPT ![a] = b]

\* 2. Cast a vote for value v in ballot b
Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= Promised[a]                     \* not below current promise
    /\ ~\E w \in Value : VoteRec(b, w) \in Votes[a]   \* a has not voted in b yet
    /\ \A a2 \in Acceptor :
          (a2 # a) => 
             \A w \in Value :
                (VoteRec(b, w) \in Votes[a2]) => w = v   \* no other value in same ballot
    /\ Safe(v, b)                           \* value is safe at b
    /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup {VoteRec(b, v)}]
    /\ Promised' = [Promised EXCEPT ![a] = b]

\* The overall next-state relation
Next ==
    \E a \in Acceptor :
        \E b \in Ballot :
            (Promise(a, b) \/ \E v \in Value : Vote(a, b, v))

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Votes, Promised>>

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
Inv ==
    /\ \A a \in Acceptor :
          /\ Votes[a] \subseteq [ballot : Ballot, value : Value]
          /\ \A rec \in Votes[a] :
                Safe(rec.value, rec.ballot)      \* every vote is safe
    /\ \A b \in Ballot :
          \A a1, a2 \in Acceptor :
            \A v1, v2 \in Value :
                (VoteRec(b, v1) \in Votes[a1] /\ VoteRec(b, v2) \in Votes[a2]) => v1 = v2
    /\ \A a \in Acceptor : Promised[a] \in Int

\* ----------------------------------------------------------------------
\* Safety property (consensus)
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (v1 \in ChosenVals /\ v2 \in ChosenVals) => v1 = v2

\* ----------------------------------------------------------------------
\* Symmetry set: all permutations of Acceptor
\* ----------------------------------------------------------------------
MCSymmetry ==
    { f \in [Acceptor -> Acceptor] :
        /\ (\A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2)   \* injective
        /\ (\A a \in Acceptor : \E a0 \in Acceptor : f[a0] = a) \* surjective
    }

====