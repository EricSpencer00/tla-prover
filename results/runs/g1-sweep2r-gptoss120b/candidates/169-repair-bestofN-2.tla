---- MODULE FastPaxos ----
EXTENDS Naturals, Sequences, FiniteSets
INSTANCE Paxos

CONSTANTS FastQuorums, FastBallots

VARIABLES cValue \* Value chosen by coordinator.

ClassicBallots == Paxos!Ballots \ FastBallots \* The set of ballots of classic rounds.

FastAssume ==
    /\ \A q \in FastQuorums : q \subseteq Paxos!Replicas
    /\ \A q, r \in FastQuorums : q \intersect r # {}
    /\ \A q \in FastQuorums : (3 * Cardinality(Paxos!Replicas)) \div 4 <= Cardinality(q)
    /\ \A q \in Paxos!Quorums : \A r, s \in FastQuorums : q \intersect r \intersect s # {}

ASSUME Paxos!PaxosAssume /\ FastAssume

IsMajorityValue(M, v) == Cardinality(M) \div 2 < Cardinality({m \in M : m.value = v})

(*
    Phase 2a (Fast):

    The coordinator starts a fast round by sending a P2a "Any" message, if no other values has been proposed before.
*)
FastAny ==
    /\ UNCHANGED <<Paxos!decision, Paxos!maxBallot, Paxos!maxVBallot, Paxos!maxValue, cValue>>
    /\ \E f \in FastBallots :
        /\ Paxos!SendMessage([type |-> "P2a",
                              ballot |-> f,
                              value |-> any])

(*
    Phase 2b (Fast):

    Acceptors can reply to a P2a "Any" message with a P2b message containing their proposed value.
*)
FastPropose ==
    /\ UNCHANGED <<Paxos!decision, cValue>>
    /\ \E a \in Paxos!Replicas,
          m \in Paxos!p2aMessages,
          v \in Paxos!Values :
        /\ m.value = any
        /\ Paxos!maxBallot[a] <= m.ballot
        /\ Paxos!maxValue[a] = none \/ Paxos!maxValue[a] = v
        /\ Paxos!maxBallot' = [Paxos!maxBallot EXCEPT ![a] = m.ballot]
        /\ Paxos!maxVBallot' = [Paxos!maxVBallot EXCEPT ![a] = m.ballot]
        /\ Paxos!maxValue' = [Paxos!maxValue EXCEPT ![a] = v]
        /\ \A n \in Paxos!p2bMessages : ~(n.ballot = m.ballot /\ n.acceptor = a)
        /\ Paxos!SendMessage([type |-> "P2b",
                              ballot |-> m.ballot,
                              acceptor |-> a,
                              value |-> v])

(*
    A value is chosen if a fast quorum of acceptors proposed that value in a fast round.

    Because the quorum size of a fast round and classic round is different, we assume that the acceptor distinguishes
    a fast round and classic round based on the P2a message it receives. If the P2a message contains the special value
    "any", it is a fast round. Else it is a classic round.
*)
FastDecide ==
    /\ UNCHANGED <<Paxos!messages, Paxos!maxBallot, Paxos!maxVBallot, Paxos!maxValue, cValue>>
    /\ \E b \in FastBallots, q \in FastQuorums :
        LET M == {m \in Paxos!p2bMessages : m.ballot = b /\ m.acceptor \in q}
            V == {w \in Paxos!Values : \E m \in M : w = m.value}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ 1 = Cardinality(V)
           /\ \E m \in M : Paxos!decision' = m.value

ClassicAccept ==
    /\ UNCHANGED <<Paxos!decision, Paxos!maxBallot, Paxos!maxVBallot, Paxos!maxValue>>
    /\ \E b \in ClassicBallots,
          f \in FastBallots,
          q \in FastQuorums,
          v \in Paxos!Values :
        /\ f < b \* There was a fast round before this classic round.
        /\ cValue = none \/ cValue = v
        /\ cValue' = v
        /\ \A m \in Paxos!p2aMessages : m.ballot # b
        /\ LET M == {m \in Paxos!p2bMessages : m.ballot = f /\ m.acceptor \in q}
               V == {w \in Paxos!Values : \E m \in M : w = m.value}
           IN /\ \A a \in q : \E m \in M : m.acceptor = a
              /\ 1 < Cardinality(V) \* Collision occurred.
              /\ IF \E w \in V : IsMajorityValue(M, w)
                 THEN IsMajorityValue(M, v) \* Choose majority in quorum.
                 ELSE v \in V \* Choose any.
              /\ Paxos!SendMessage([type |-> "P2a",
                                    ballot |-> b,
                                    value |-> v])

ClassicAccepted ==
    /\ UNCHANGED <<cValue>>
    /\ Paxos!PaxosAccepted

ClassicDecide ==
    /\ UNCHANGED <<Paxos!messages, Paxos!maxBallot, Paxos!maxVBallot, Paxos!maxValue, cValue>>
    /\ \E b \in ClassicBallots, q \in Paxos!Quorums :
        LET M == {m \in Paxos!p2bMessages : m.ballot = b /\ m.acceptor \in q}
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ \E m \in M : Paxos!decision' = m.value

FastTypeOK == /\ Paxos!PaxosTypeOK
              /\ cValue \in Paxos!Values \cup {none}

FastInit == /\ Paxos!PaxosInit
            /\ cValue = none

FastNext == \/ FastAny
            \/ FastPropose
            \/ FastDecide
            \/ ClassicAccept
            \/ ClassicAccepted
            \/ ClassicDecide

FastSpec == /\ FastInit
            /\ [][FastNext]_<<Paxos!messages, Paxos!decision, Paxos!maxBallot,
                         Paxos!maxVBallot, Paxos!maxValue, cValue>>
            /\ Paxos!SF_<<Paxos!messages, Paxos!decision, Paxos!maxBallot,
                        Paxos!maxVBallot, Paxos!maxValue, cValue>>(FastDecide)
            /\ Paxos!SF_<<Paxos!messages, Paxos!decision, Paxos!maxBallot,
                        Paxos!maxVBallot, Paxos!maxValue, cValue>>(ClassicDecide)

\* Non-triviality safety property: Only proposed values can be learnt.
FastNontriviality == \/ Paxos!decision = none
                     \/ \E m \in Paxos!p2bMessages : m.value = Paxos!decision /\ m.ballot \in FastBallots

===============================================================