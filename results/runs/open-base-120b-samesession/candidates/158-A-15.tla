---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(*--------------------------------------------------------------------
  Operators required by the .cfg file
--------------------------------------------------------------------*)
MCAcceptor == Acceptor
MCValue   == Value
MCQuorum  == Quorum
MCBallot  == Ballot

VARIABLES votes, prom

(*--------------------------------------------------------------------
  Type safety
--------------------------------------------------------------------*)
TypeOK ==
    /\ votes \in [Acceptor -> SUBSET [ballot : Ballot, value : Value]]
    /\ prom  \in [Acceptor -> (Ballot \cup {-1})]

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ prom  = [a \in Acceptor |-> -1]

(*--------------------------------------------------------------------
  Safety of a value at a ballot
--------------------------------------------------------------------*)
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E vv \in votes[a] :
                          vv.ballot = c /\ vv.value = v )
                    \/ (prom[a] > c)

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
Promise ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > prom[a]
            /\ prom' = [prom EXCEPT ![a] = b]
            /\ UNCHANGED votes

Vote ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= prom[a]                     \* respect current promise
                /\ \A vv \in votes[a] : vv.ballot # b   \* not voted in b yet
                /\ \A a2 \in Acceptor :
                       /\ a2 # a =>
                          \A vv2 \in votes[a2] :
                              (vv2.ballot = b) => vv2.value = v   \* no conflicting vote
                /\ Safe(v, b)                      \* value is safe
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup
                                   { [ballot |-> b, value |-> v] }]
                /\ prom'  = [prom  EXCEPT ![a] = b]

Next ==
    \/ Promise
    \/ Vote

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<votes, prom>>

(*--------------------------------------------------------------------
  Invariant
--------------------------------------------------------------------*)
Inv ==
    /\ TypeOK
    /\ \A a \in Acceptor :
          \A vv1, vv2 \in votes[a] :
              (vv1.ballot = vv2.ballot) => vv1 = vv2          \* one vote per ballot per acceptor
    /\ \A b \in Ballot :
          \A a1, a2 \in Acceptor :
              \A vv1 \in votes[a1] :
                  \A vv2 \in votes[a2] :
                      (vv1.ballot = b /\ vv2.ballot = b) => vv1.value = vv2.value
    /\ \A a \in Acceptor :
          \A vv \in votes[a] :
              Safe(vv.value, vv.ballot)                       \* every vote is safe

(*--------------------------------------------------------------------
  Chosen values and consensus property
--------------------------------------------------------------------*)
Chosen(v) ==
    \E b \in Ballot :
        \E Q \in Quorum :
            \A a \in Q :
                \E vv \in votes[a] :
                    vv.ballot = b /\ vv.value = v

ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (Chosen(v1) /\ Chosen(v2)) => v1 = v2

(*--------------------------------------------------------------------
  Symmetry set (identity permutation)
--------------------------------------------------------------------*)
MCSymmetry == { [a \in Acceptor |-> a] }

====