---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* Default concrete interpretations – can be overridden by the .cfg *)
Acceptor == {a1, a2, a3}
Value    == {v1, v2}
Quorum   == {{a1, a2}, {a2, a3}, {a1, a3}}
Ballot   == Nat

MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, prom

(* ---------------------------------------------------------------------- *)
(* Types *)

VoteRec == [ballot : Ballot, value : Value]

(* ---------------------------------------------------------------------- *)
(* Initial state *)

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ prom  = [a \in Acceptor |-> -1]

(* ---------------------------------------------------------------------- *)
(* Safety of a (ballot,value) pair *)

Safe(b, v) ==
    \A c \in Ballot :
        c < b =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E w \in votes[a] : w.ballot = c /\ w.value = v )
                    \/ ( prom[a] > c )

(* ---------------------------------------------------------------------- *)
(* Actions *)

IncreasePromise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > prom[a]
    /\ prom' = [prom EXCEPT ![a] = b]
    /\ votes' = votes

Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= prom[a]
    /\ \A w \in votes[a] : w.ballot # b
    /\ \A a2 \in Acceptor :
          \A w2 \in votes[a2] :
            (w2.ballot = b) => w2.value = v
    /\ Safe(b, v)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ prom'  = [prom EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : IncreasePromise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

vars == <<votes, prom>>

(* ---------------------------------------------------------------------- *)
(* Specification *)

Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(* Invariants *)

TypeInvariant ==
    /\ votes \in [Acceptor -> SUBSET VoteRec]
    /\ prom  \in [Acceptor -> Int]

AtMostOnePerBallot ==
    \A b \in Ballot :
        \A v1, v2 \in Value :
            ( (\E a1 \in Acceptor, w1 \in votes[a1] : w1.ballot = b /\ w1.value = v1) /\
              (\E a2 \in Acceptor, w2 \in votes[a2] : w2.ballot = b /\ w2.value = v2) )
            => v1 = v2

SafeVotes ==
    \A a \in Acceptor :
        \A w \in votes[a] :
            Safe(w.ballot, w.value)

Inv == /\ TypeInvariant /\ AtMostOnePerBallot /\ SafeVotes

(* ---------------------------------------------------------------------- *)
(* Consistency property *)

ChosenVals ==
    { v \in Value :
        \E b \in Ballot, Q \in Quorum :
            \A a \in Q :
                \E w \in votes[a] : w.ballot = b /\ w.value = v }

ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (v1 \in ChosenVals /\ v2 \in ChosenVals) => v1 = v2

(* ---------------------------------------------------------------------- *)
(* Symmetry *)

MCSymmetry == { [a \in Acceptor |-> a] }

====