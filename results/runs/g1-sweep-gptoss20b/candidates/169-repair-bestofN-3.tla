---- MODULE FastPaxos ----
EXTENDS Paxos

CONSTANTS Ballots, Replicas, Quorums, Values, any, none, FastQuorums, FastBallots

VARIABLES decision, maxBallot, maxVBallot, maxValue, cValue, messages, p2aMessages, p2bMessages

(* Cardinality predicate *)
Cardinality == Len

(* Majority check *)
IsMajorityValue(M, v) == Cardinality(M) \div 2 < Cardinality({m \in M : m.value = v})

(* Classic ballots are those not in FastBallots *)
ClassicBallots == Ballots \ FastBallots

(* Assumptions about fast quorums and ballots *)
FastAssume ==
    /\ \A q \in FastQuorums : q \subseteq Replicas
    /\ \A q, r \in FastQuorums : q \intersect r # {}
    /\ \A q \in FastQuorums : (3 * Cardinality(Replicas)) \div 4 <= Cardinality(q)
    /\ \A q \in Quorums : \A r, s \in FastQuorums : q \intersect r \intersect s # {}

(* Placeholder definitions for missing operators from Paxos *)
PaxosAssume == \TRUE
PaxosTypeOK == \TRUE
PaxosInit == \TRUE
PaxosAccepted == \TRUE
PaxosSymmetry == {decision, maxBallot, maxVBallot, maxValue, cValue, messages, p2aMessages, p2bMessages}
PaxosConsistency == \TRUE

(* Message sending primitive *)
SendMessage(msg) ==
    /\ messages' = messages \cup {msg}
    /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue, cValue, p2aMessages, p2bMessages>>

ASSUME PaxosAssume /\ FastAssume

(* Phase 2a (Fast): Coordinator sends a P2a "Any" message *)
FastAny ==
    /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E f \in FastBallots :
        /\ SendMessage([type |-> "P2a",
                        ballot |-> f,
                        value |-> any])

(* Phase 2b (Fast): Acceptors reply to a P2a "Any" message *)
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

(* Phase 2b (Fast): Decision when a fast quorum proposes the same value *)
FastDecide ==
    /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E b \in FastBallots, q \in FastQuorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
            V == {w \in Values : \E m \in M : w = m.value}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ 1 = Cardinality(V)
           /\ \E m \in M : decision' = m.value

(* Phase 2a (Classic): Resolve collisions after a fast round *)
ClassicAccept ==
    /\ UNCHANGED <<decision, maxBallot, maxVBallot, maxValue>>
    /\ \E b \in ClassicBallots, f \in FastBallots, q \in FastQuorums, v \in Values :
        /\ f < b
        /\ cValue = none \/ cValue = v
        /\ cValue' = v
        /\ \A m \in p2aMessages : m.ballot # b
        /\ LET M == {m \in p2bMessages : m.ballot = f /\ m.acceptor \in q}
               V == {w \in Values : \E m \in M : w = m.value}
           IN /\ \A a \in q : \E m \in M : m.acceptor = a
              /\ 1 < Cardinality(V)
              /\ IF \E w \in V : IsMajorityValue(M, w)
                 THEN IsMajorityValue(M, v)
                 ELSE v \in V
              /\ SendMessage([type |-> "P2a",
                              ballot |-> b,
                              value |-> v])

(* Phase 2b (Classic): Same as in Paxos *)
ClassicAccepted ==
    /\ UNCHANGED <<cValue>>
    /\ PaxosAccepted

(* Classical decision: majority acceptance of a ballot *)
ClassicDecide ==
    /\ UNCHANGED <<messages, maxBallot, maxVBallot, maxValue, cValue>>
    /\ \E b \in ClassicBallots, q \in Quorums :
        LET M == {m \in p2bMessages : m.ballot = b /\ m.acceptor \in q}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ \E m \in M : decision' = m.value

(* Type and initialization *)
FastTypeOK == /\ PaxosTypeOK
              /\ cValue \in Values \union {none}

FastInit == /\ PaxosInit
            /\ cValue = none

(* Next-state relation *)
FastNext == \/ FastAny
            \/ FastPropose
            \/ FastDecide
            \/ ClassicAccept
            \/ ClassicAccepted
            \/ ClassicDecide

(* Specification *)
FastSpec == /\ FastInit
            /\ [][FastNext]_<<messages, decision, maxBallot, maxVBallot, maxValue, cValue>>
            /\ SF_<<messages, decision, maxBallot, maxVBallot, maxValue, cValue>>(FastDecide)
            /\ SF_<<messages, decision, maxBallot, maxVBallot, maxValue, cValue>>(ClassicDecide)

(* Non-triviality safety property *)
FastNontriviality == \/ decision = none
                     \/ \E m \in p2bMessages : m.value = decision /\ m.ballot \in FastBallots

====