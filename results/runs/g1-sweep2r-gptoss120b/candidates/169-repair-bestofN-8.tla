---- MODULE FastPaxos ----
EXTENDS Paxos, FiniteSets

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANTS 
    FastQuorums,
    FastBallots,
    Replicas,               \* from Paxos (re‑declared for the parser)
    Values,                 \* from Paxos (re‑declared for the parser)
    Ballots,                \* from Paxos (re‑declared for the parser)
    Quorums,                \* from Paxos (re‑declared for the parser)
    any,                    \* special value used by the protocol
    none                    \* special value used by the protocol

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    cValue,                 \* value chosen by the coordinator
    messages,               \* the multiset of all messages in the system
    decision,               \* the value that has been decided (if any)
    maxBallot,              \* mapping from acceptor to the highest ballot it has seen
    maxVBallot,             \* mapping from acceptor to the highest ballot for which it has a value
    maxValue                \* mapping from acceptor to the value associated with maxVBallot

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
ClassicBallots == Ballots \ FastBallots

FastAssume ==
    /\ \A q \in FastQuorums : q \subseteq Replicas
    /\ \A q, r \in FastQuorums : q \cap r # {}
    /\ \A q \in FastQuorums : (3 * Cardinality(Replicas)) \div 4 <= Cardinality(q)
    /\ \A q \in Quorums : \A r, s \in FastQuorums : q \cap r \cap s # {}

ASSUME PaxosAssume /\ FastAssume

IsMajorityValue(M, v) ==
    Cardinality(M) \div 2 < Cardinality({ m \in M : m.value = v })

\* ----------------------------------------------------------------------
\* Fast round – Phase 2a
\* ----------------------------------------------------------------------
FastAny ==
    /\ UNCHANGED << decision, maxBallot, maxVBallot, maxValue, cValue >>
    /\ \E f \in FastBallots :
        /\ SendMessage([ type    |-> "P2a",
                        ballot  |-> f,
                        value   |-> any ])

\* ----------------------------------------------------------------------
\* Fast round – Phase 2b
\* ----------------------------------------------------------------------
FastPropose ==
    /\ UNCHANGED << decision, cValue >>
    /\ \E a \in Replicas,
          m \in p2aMessages,
          v \in Values :
        /\ m.value = any
        /\ maxBallot[a] <= m.ballot
        /\ maxValue[a] = none \/ maxValue[a] = v
        /\ maxBallot'   = [ maxBallot   EXCEPT ![a] = m.ballot ]
        /\ maxVBallot'  = [ maxVBallot  EXCEPT ![a] = m.ballot ]
        /\ maxValue'    = [ maxValue    EXCEPT ![a] = v ]
        /\ \A n \in p2bMessages : ~(n.ballot = m.ballot /\ n.acceptor = a)
        /\ SendMessage([ type    |-> "P2b",
                        ballot  |-> m.ballot,
                        acceptor|-> a,
                        value   |-> v ])

\* ----------------------------------------------------------------------
\* Fast round – Decision
\* ----------------------------------------------------------------------
FastDecide ==
    /\ UNCHANGED << messages, maxBallot, maxVBallot, maxValue, cValue >>
    /\ \E b \in FastBallots,
          q \in FastQuorums :
        LET M == { m \in p2bMessages : m.ballot = b /\ m.acceptor \in q }
            V == { w \in Values : \E m \in M : w = m.value }
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ 1 = Cardinality(V)
           /\ \E m \in M : decision' = m.value

\* ----------------------------------------------------------------------
\* Classic round – Phase 2a (collision handling)
\* ----------------------------------------------------------------------
ClassicAccept ==
    /\ UNCHANGED << decision, maxBallot, maxVBallot, maxValue >>
    /\ \E b \in ClassicBallots,
          f \in FastBallots,
          q \in FastQuorums,
          v \in Values :
        /\ f < b                         \* there was a fast round before this classic round
        /\ cValue = none \/ cValue = v
        /\ cValue' = v
        /\ \A m \in p2aMessages : m.ballot # b
        /\ LET M == { m \in p2bMessages : m.ballot = f /\ m.acceptor \in q }
               V == { w \in Values : \E m \in M : w = m.value }
           IN /\ \A a \in q : \E m \in M : m.acceptor = a
              /\ 1 < Cardinality(V)        \* collision occurred
              /\ IF \E w \in V : IsMajorityValue(M, w)
                 THEN IsMajorityValue(M, v) \* choose majority in quorum
                 ELSE v \in V               \* choose any
              /\ SendMessage([ type   |-> "P2a",
                               ballot |-> b,
                               value  |-> v ])

\* ----------------------------------------------------------------------
\* Classic round – Phase 2b
\* ----------------------------------------------------------------------
ClassicAccepted ==
    /\ UNCHANGED << cValue >>
    /\ PaxosAccepted

\* ----------------------------------------------------------------------
\* Classic round – Decision
\* ----------------------------------------------------------------------
ClassicDecide ==
    /\ UNCHANGED << messages, maxBallot, maxVBallot, maxValue, cValue >>
    /\ \E b \in ClassicBallots,
          q \in Quorums :
        LET M == { m \in p2bMessages : m.ballot = b /\ m.acceptor \in q }
        IN /\ \A a \in q : \E m \in M : m.acceptor = a
           /\ \E m \in M : decision' = m.value

\* ----------------------------------------------------------------------
\* Type correctness
\* ----------------------------------------------------------------------
FastTypeOK ==
    /\ PaxosTypeOK
    /\ cValue \in Values \cup { none }

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
FastInit ==
    /\ PaxosInit
    /\ cValue = none

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
FastNext ==
    \/ FastAny
    \/ FastPropose
    \/ FastDecide
    \/ ClassicAccept
    \/ ClassicAccepted
    \/ ClassicDecide

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
FastSpec ==
    /\ FastInit
    /\ [][FastNext]_<< messages, decision, maxBallot, maxVBallot, maxValue, cValue >>
    /\ SF_<< messages, decision, maxBallot, maxVBallot, maxValue, cValue >>(FastDecide)
    /\ SF_<< messages, decision, maxBallot, maxVBallot, maxValue, cValue >>(ClassicDecide)

\* ----------------------------------------------------------------------
\* Safety property: only proposed values can be learned
\* ----------------------------------------------------------------------
FastNontriviality ==
    \/ decision = none
    \/ \E m \in p2bMessages : m.value = decision /\ m.ballot \in FastBallots

====