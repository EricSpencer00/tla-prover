---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES votes, prom

\* ----- Operators required by the .cfg -----
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----- Initial state -----
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ prom  = [a \in Acceptor |-> -1]

\* ----- Safety of a value at a ballot -----
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E w \in votes[a] : w.ballot = c /\ w.value = v )
                    \/ ( prom[a] > c )

\* ----- Actions -----
PromiseIncrease(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > prom[a]
    /\ prom' = [prom EXCEPT ![a] = b]
    /\ UNCHANGED votes

Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= prom[a]
    /\ \A w \in votes[a] : w.ballot # b               \* not already voted in this ballot
    /\ \A a2 \in Acceptor :
          \A w \in votes[a2] :
              (w.ballot = b) => (w.value = v)        \* no different value in same ballot
    /\ Safe(v, b)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ prom'  = [prom EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : PromiseIncrease(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

\* ----- Specification -----
Spec == Init /\ [][Next]_<<votes, prom>>

\* ----- Invariants -----
TypeInv ==
    /\ votes \in [Acceptor -> SUBSET { [ballot: Ballot, value: Value] }]
    /\ prom  \in [Acceptor -> Int]

VoteSafety ==
    \A a \in Acceptor :
        \A w \in votes[a] : Safe(w.value, w.ballot)

OneValuePerBallot ==
    \A b \in Ballot :
        \A v1, v2 \in Value :
            ( (\E a1 \in Acceptor : \E w1 \in votes[a1] : w1.ballot = b /\ w1.value = v1) /\
              (\E a2 \in Acceptor : \E w2 \in votes[a2] : w2.ballot = b /\ w2.value = v2) )
            => v1 = v2

QuorumOverlapInv ==
    \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Inv == TypeInv /\ VoteSafety /\ OneValuePerBallot /\ QuorumOverlapInv

\* ----- Property: at most one value can be chosen -----
ChosenVals ==
    { v \in Value :
        \E b \in Ballot, Q \in Quorum :
            \A a \in Q :
                \E w \in votes[a] : w.ballot = b /\ w.value = v }

ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (v1 \in ChosenVals /\ v2 \in ChosenVals) => v1 = v2

\* ----- Symmetry set for model checking -----
MCSymmetry ==
    { p \in [Acceptor -> Acceptor] :
        /\ \A a \in Acceptor : p[a] \in Acceptor
        /\ \A a1, a2 \in Acceptor : a1 # a2 => p[a1] # p[a2] }

====