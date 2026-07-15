---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

\* -------------------------------------------------------------
\* Constants (instantiated in the .cfg file)
\* -------------------------------------------------------------
CONSTANTS a1, Acceptor, Value, Quorum, Ballot

\* -------------------------------------------------------------
\* State variables
\* -------------------------------------------------------------
VARIABLES votes, threshold

\* -------------------------------------------------------------
\* Derived definitions
\* -------------------------------------------------------------
Votes    == [a \in Acceptor |-> SUBSET (Ballot \X Value)]

Quorums  == { Q \in SUBSET Acceptor : Q # {} }

\* -------------------------------------------------------------
\* Initial predicate
\* -------------------------------------------------------------
Init ==
    /\ votes    = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* -------------------------------------------------------------
\* Helper predicates
\* -------------------------------------------------------------
SafeAt(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorums :
                \A a \in Q :
                    ( (\<b, v\> \in votes[a]) \/ (b > threshold[a]) )

CanVote(a, b, v) ==
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= threshold[a] + 1
    /\ ~(\E w \in Value : \<b, w\> \in votes[a])
    /\ \A a2 \in Acceptor :
        (\E w \in Value : \<b, w\> \in votes[a2]) => w = v
    /\ SafeAt(v, b)

\* -------------------------------------------------------------
\* Actions
\* -------------------------------------------------------------
IncreasePromise ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > threshold[a]
            /\ threshold' = [threshold EXCEPT ![a] = b]
            /\ UNCHANGED votes

Vote ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ CanVote(a, b, v)
                /\ votes'    = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
                /\ threshold' = [threshold EXCEPT ![a] = b]

Next == Vote \/ IncreasePromise

\* -------------------------------------------------------------
\* Specification
\* -------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, threshold>>

\* -------------------------------------------------------------
\* Invariant (as required by the cfg file)
\* -------------------------------------------------------------
Inv ==
    /\ \A a \in Acceptor : threshold[a] \in -1..Max(Ballot)
    /\ \A a \in Acceptor : votes[a] \subseteq Ballot \X Value
    /\ \A b \in Ballot :
        \A v1, v2 \in Value :
            ( (\E a1 \in Acceptor : <<b, v1>> \in votes[a1]) /\
              (\E a2 \in Acceptor : <<b, v2>> \in votes[a2]) ) => v1 = v2

\* -------------------------------------------------------------
\* Derived property implementing the abstract consensus spec
\* -------------------------------------------------------------
ChosenValues ==
    { v \in Value :
        \E b \in Ballot :
            \E Q \in Quorums :
                \A a \in Q : <<b, v>> \in votes[a] }

ConsensusSpecBar ==
    Cardinality(ChosenValues) <= 1

\* -------------------------------------------------------------
\* THEOREM (optional, not required by cfg but useful)
\* -------------------------------------------------------------
THEOREM Spec => []Inv

====