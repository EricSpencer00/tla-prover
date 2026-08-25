---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* substitution operators for the model checker *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, promised

Init ==
    /\ votes    = [a \in Acceptor |-> {}]
    /\ promised = [a \in Acceptor |-> -1]

(* --- safety definition ----------------------------------- *)
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                /\ Q \subseteq Acceptor
                /\ \A a \in Q :
                       ( \E w \in votes[a] : w.ballot = c /\ w.value = v )
                       \/ promised[a] > c

Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= promised[a]                                   \* respects current promise
    /\ \A w \in votes[a] : w.ballot # b                   \* not already voted in this ballot
    /\ \A a_ \in Acceptor :
         \A w \in votes[a_] :
              (w.ballot = b) => (w.value = v)            \* at most one value per ballot
    /\ Safe(v, b)                                         \* safety condition
    /\ votes'    = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ promised' = [promised EXCEPT ![a] = b]

Promise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > promised[a]                                    \* raise the promise
    /\ promised' = [promised EXCEPT ![a] = b]
    /\ UNCHANGED votes

Next ==
    \/ \E a \in Acceptor: \E b \in Ballot: \E v \in Value: Vote(a, b, v)
    \/ \E a \in Acceptor: \E b \in Ballot: Promise(a, b)

Spec == Init /\ [][Next]_<<votes, promised>>

TypeOK ==
    /\ votes    \in [Acceptor -> SUBSET [ballot: Ballot, value: Value]]
    /\ promised \in [Acceptor -> Int]

OneValuePerBallot ==
    \A b \in Ballot :
        \A aA, aB \in Acceptor :
            \A w1 \in votes[aA] :
                \A w2 \in votes[aB] :
                    (w1.ballot = b /\ w2.ballot = b) => w1.value = w2.value

AllVotesSafe ==
    \A a \in Acceptor : \A w \in votes[a] : Safe(w.value, w.ballot)

Inv == TypeOK /\ OneValuePerBallot /\ AllVotesSafe

(* --- chosen values and consensus property ---------------- *)
ChosenVals ==
    { v \in Value :
        \E b \in Ballot :
            \E Q \in Quorum :
                /\ Q \subseteq Acceptor
                /\ \A a \in Q :
                       \E w \in votes[a] : w.ballot = b /\ w.value = v }

ConsensusSpecBar ==
    \A vv1, vv2 \in Value :
        (vv1 \in ChosenVals /\ vv2 \in ChosenVals) => vv1 = vv2

(* --- symmetry set (identity permutation) ----------------- *)
MCSymmetry == { [a \in Acceptor |-> a] }

====