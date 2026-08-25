---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* Operators substituting the model‑checking bounded versions
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES votes, promise

\* votes[a] is the set of records [ballot : Ballot, value : Value] cast by acceptor a
\* promise[a] is the smallest ballot number a will accept from now on
\* (initialized to -1 meaning “no promise yet”)
\* ----------------------------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ promise = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* A quorum Q is a set of acceptors; the overlap property is required for safety
QuorumOverlap ==
    \A q1, q2 \in Quorum : q1 # {} /\ q2 # {} => (q1 \cap q2) # {}

\* “Safe(b, v)” states that value v is safe to be voted for in ballot b
Safe(b, v) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    (   (\E rec \in votes[a] :
                            /\ rec.ballot = c
                            /\ rec.value  = v)
                    \/  promise[a] > c )   \* a cannot vote in c any more

\* The set of values that have been “chosen”:
\* a value is chosen when some quorum has all its members voting for it
\* in the same ballot.
Chosen ==
    { v \in Value :
        \E b \in Ballot :
            \E Q \in Quorum :
                \A a \in Q :
                    \E rec \in votes[a] :
                        /\ rec.ballot = b
                        /\ rec.value  = v }

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Increase the promise threshold of an acceptor
PromiseInc ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > promise[a]
            /\ promise' = [promise EXCEPT ![a] = b]
            /\ UNCHANGED votes

\* 2. Cast a vote for value v in ballot b
Vote ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= promise[a]                         \* respects current promise
                /\ \A rec \in votes[a] : rec.ballot # b   \* not already voted in b
                /\ \A a2 \in Acceptor :
                       \A rec2 \in votes[a2] :
                           (rec2.ballot = b) => rec2.value = v   \* at most one value per ballot
                /\ Safe(b, v)                               \* safety condition
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup
                                            { [ballot |-> b, value |-> v] }]
                /\ promise' = [promise EXCEPT ![a] = b]

Next ==
    \/ PromiseInc
    \/ Vote

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, promise>>

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
Inv ==
    /\ \A a \in Acceptor :
          (promise[a] = -1) \/ (promise[a] \in Ballot)
    /\ \A a \in Acceptor :
          votes[a] \subseteq {[ballot : Ballot, value : Value] }
    /\ \A b \in Ballot :
          \A v1, v2 \in Value :
              ( (\E a1 \in Acceptor : \E rec1 \in votes[a1] :
                       /\ rec1.ballot = b /\ rec1.value = v1) /\
                (\E a2 \in Acceptor : \E rec2 \in votes[a2] :
                       /\ rec2.ballot = b /\ rec2.value = v2) )
              => v1 = v2
    /\ \A a \in Acceptor :
          \A rec \in votes[a] :
              Safe(rec.ballot, rec.value)
    /\ QuorumOverlap

\* ----------------------------------------------------------------------
\* Property expressing consensus: at most one value can ever be chosen
\* ----------------------------------------------------------------------
ConsensusSpecBar == [] (Cardinality(Chosen) <= 1)

\* ----------------------------------------------------------------------
\* Symmetry definition (trivial identity symmetry)
\* ----------------------------------------------------------------------
MCSymmetry == { [a \in Acceptor |-> a] }

====