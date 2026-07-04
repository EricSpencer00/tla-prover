---- MODULE FastPaxos ----
EXTENDS Paxos, FiniteSets

CONSTANTS FastQuorums, FastBallots, Replicas, Ballots, Quorums, Values, any, none

VARIABLES cValue \* Value chosen by coordinator.

ClassicBallots == Ballots \ FastBallots \* The set of ballots of classic rounds.

FastAssume ==
    /\ \A q \in FastQuorums : q \subseteq Replicas
    /\ \A q, r \in FastQuorums : q \intersect r # {}
    /\ \A q \in FastQuorums : (3 * Cardinality(Replicas)) \div 4 <= Cardinality(q)
    /\ \A q \in Quorums : \A r, s \in FastQuorums : q \intersect r \intersect s # {}

ASSUME PaxosAssume /\ FastAssume

IsMajorityValue(M, v) == Cardinality(M) \div 2 < Cardinality({m \in M : m.value = v})

(*
    Phase 2a (Fast):

    The coordinator starts a fast round by sending a P2a "Any" message, if no other values has been proposed before.
*)
FastAny ==
    /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E f \in FastBallots :
        /\ SendMessage([type |-> "P2a",
                        ballot |-> f,
                        value |-> any])

(*
    Phase 2b (Fast):

    Acceptors can reply to a P2a "Any" message with a P2b message containing their proposed value.
*)
FastPropose ==
    /\ UNCHANGED <<decision, cValue>>
    /\ \E a \in Replicas, m \in p2aMessages, v \in Values :
        /\ m.value = any
        /\ maxBallot[a] <= m.ballot
        /\ maxValue[a] = none \/ maxValue[a] = v
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
        /\ maxValue' = [maxValue EXCEPT ![a] = v]
        /\ \A n \in p2bMessages : ~(n.ballot = m.ballot /\ n.acceptor = a)
        /\ SendMessage([type |-> "P2b",
                        ballot |-> m.ballot,
                        acceptor |-> a,
                        value |-> v])

(*
    A value is chosen if a fast quorum of acceptors proposed that value in a fast round.
*)
FastDecide ==
    /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E b \in FastBallots, q \in FastQuorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
            V == {w \in Values : \E m \in M : w = m.value}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ 1 = Cardinality(V)
           /\ \E m \in M : decision' = m.value

(*
    Phase 2a (Classic)
*)
ClassicAccept ==
    /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in ClassicBallots, f \in FastBallots, q \in FastQuorums, v \in Values :
        /\ f < b \* There was a fast round before this classic round.
        /\ cValue = none \/ cValue = v
        /\ cValue' = v
        /\ \A m \in p2aMessages : m.ballot # b
        /\ LET M == {m \in p2bMessages : m.ballot = f /\ m.acceptor \in q}
               V == {w \in Values : \E m \in M : w = m.value}
           IN /\ \A a \in q : \E m \in M : m.acceptor = a
              /\ 1 < Cardinality(V) \* Collision occurred.
              /\ IF \E w \in V : IsMajorityValue(M, w)
                 THEN IsMajorityValue(M, v) \* Choose majority in quorum.
                 ELSE v \in V \* Choose any.
              /\ SendMessage([type |-> "P2a",
                              ballot |-> b,
                              value |-> v])

(*
    Phase 2b (Classic)
*)
ClassicAccepted ==
    /\ UNCHANGED <<cValue>>
    /\ PaxosAccepted

(*
    Consensus is achieved when a majority of acceptors accept the same ballot number.
*)
ClassicDecide ==
    /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E b \in ClassicBallots, q \in Quorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ \E m \in M : decision' = m.value

FastTypeOK == /\ PaxosTypeOK
              /\ cValue \in Values \union {none}

FastInit == /\ PaxosInit
            /\ cValue = none

FastNext == \/ FastAny
            \/ FastPropose
            \/ FastDecide
            \/ ClassicAccept
            \/ ClassicAccepted
            \/ ClassicDecide

FastSpec == /\ FastInit
            /\ [][FastNext]_<<messages, decision, maxBallot, maxVBallot, maxValue, cValue>>
            /\ SF_<<messages, decision, maxBallot, maxVBallot, maxValue, cValue>>(FastDecide)
            /\ SF_<<messages, decision, maxBallot, maxVBallot, maxValue, cValue>>(ClassicDecide)

\* Non-triviality safety property: Only proposed values can be learnt.
FastNontriviality == \/ decision = none
                     \/ \E m \in p2bMessages : m.value = decision /\ m.ballot \in FastBallots

====