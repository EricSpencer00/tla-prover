---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (must be provided in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Node,               \* Set of nodes
    SlushLoopProcess,   \* Set of loop processes (one per node)
    SlushQueryProcess,  \* Set of query processes (one per node)
    HostMapping,        \* Set of triples <<proc, "host", node>>
    SlushIterationCount,\* Number of iterations each loop process must run
    SampleSetSize,      \* Number of peers sampled each round
    PickFlipThreshold,  \* Threshold for adopting a color
    NoColor,            \* Special value meaning "uncolored"
    NoMessage           \* Special value meaning "no pending message"

\* ----------------------------------------------------------------------
\* Derived mappings
\* ----------------------------------------------------------------------
ProcHost(p) == 
    CASE p \in SlushLoopProcess  -> 
            CHOOSE n \in Node : <<p, "host", n>> \in HostMapping
         [] p \in SlushQueryProcess -> 
            CHOOSE n \in Node : <<p, "host", n>> \in HostMapping
         
NodeOfLoop(p) == ProcHost(p)
NodeOfQuery(p) == ProcHost(p)

NodeProcs == { <<n, l, q>> : n \in Node,
                            l \in SlushLoopProcess,
                            q \in SlushQueryProcess,
                            <<l, "host", n>> \in HostMapping,
                            <<q, "host", n>> \in HostMapping }

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue", NoColor}
MessageTypes == {"query", "reply", "terminate", NoMessage}
ProcSet == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    color,          \* [Node -> Colors] current color of each node
    msgs,           \* Set of in‑flight messages
    pc,             \* [ProcSet -> Nat] program counters
    sample,         \* [SlushLoopProcess -> SUBSET Node] current sample set
    iterCnt         \* [SlushLoopProcess -> Nat] iteration counters

\* ----------------------------------------------------------------------
\* Message record definition
\* ----------------------------------------------------------------------
Message == [type : {"query","reply","terminate"},
            src  : ProcSet,
            dst  : ProcSet,
            payload : UNION {Colors, NoMessage}]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ pc     = [p \in ProcSet |-> IF p = "Client" THEN 1 ELSE 1]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iterCnt= [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
UncoloredNodes == { n \in Node : color[n] = NoColor }

LoopReady(lp) == color[NodeOfLoop(lp)] # NoColor

AllLoopsDone == \A lp \in SlushLoopProcess : pc[lp] = 5

AllQueriesDone == \A qp \in SlushQueryProcess : pc[qp] = 3

ClientDone == pc["Client"] = 2

AllTerminated == \A lp \in SlushLoopProcess : 
                    \E m \in msgs : 
                        /\ m.type = "terminate"
                        /\ m.src = lp

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssign ==
    /\ pc["Client"] = 1
    /\ UncoloredNodes # {}
    /\ LET n == CHOOSE n \in UncoloredNodes : TRUE
          c == IF RandomElement({"Red","Blue"}) = "Red" THEN "Red" ELSE "Blue"
       IN /\ color' = [color EXCEPT ![n] = c]
          /\ pc'    = [pc EXCEPT !["Client"] = 2]
    /\ UNCHANGED <<msgs, sample, iterCnt>>

LoopWaitForColor(lp) ==
    /\ pc[lp] = 1
    /\ ~LoopReady(lp)          \* still waiting
    /\ UNCHANGED <<color, msgs, pc, sample, iterCnt>>

LoopStartIteration(lp) ==
    /\ pc[lp] = 1
    /\ LoopReady(lp)
    /\ pc' = [pc EXCEPT ![lp] = 2]
    /\ UNCHANGED <<color, msgs, sample, iterCnt>>

LoopSendQueries(lp) ==
    /\ pc[lp] = 2
    /\ sample[lp] = {}
    /\ LET peers == { n \in Node : n # NodeOfLoop(lp) }
           sam    == { n \in peers : 
                       Cardinality({ m \in msgs : 
                                      m.type = "query" /\ m.dst = NodeOfQuery(n) }) 
                       < SampleSetSize }
       IN 
        /\ sample' = [sample EXCEPT ![lp] = sam]
        /\ msgs'   = msgs 
                    \cup { [type |-> "query",
                           src  |-> lp,
                           dst  |-> NodeOfQuery(n),
                           payload |-> color[NodeOfLoop(lp)]] 
                         : n \in sam }
        /\ pc' = [pc EXCEPT ![lp] = 3]
    /\ UNCHANGED <<color, iterCnt>>

LoopCollectReplies(lp) ==
    /\ pc[lp] = 3
    /\ \A n \in sample[lp] : 
          \E m \in msgs : 
            /\ m.type = "reply"
            /\ m.dst = lp
            /\ m.src = NodeOfQuery(n)
    /\ LET redCnt == Cardinality({ m \in msgs :
                                   /\ m.type = "reply"
                                   /\ m.dst = lp
                                   /\ m.payload = "Red" })
           blueCnt== Cardinality({ m \in msgs :
                                   /\ m.type = "reply"
                                   /\ m.dst = lp
                                   /\ m.payload = "Blue" })
        IN 
          /\ IF redCnt >= PickFlipThreshold
                THEN color' = [color EXCEPT ![NodeOfLoop(lp)] = "Red"]
             ELSE IF blueCnt >= PickFlipThreshold
                THEN color' = [color EXCEPT ![NodeOfLoop(lp)] = "Blue"]
             ELSE color' = color
          /\ msgs'   = { m \in msgs : 
                         ~ (m.type = "reply" /\ m.dst = lp) }  \* remove processed replies
          /\ sample' = [sample EXCEPT ![lp] = {}]
          /\ iterCnt' = [iterCnt EXCEPT ![lp] = @ + 1]
          /\ IF iterCnt'[lp] >= SlushIterationCount
                THEN pc' = [pc EXCEPT ![lp] = 4]
                ELSE pc' = [pc EXCEPT ![lp] = 2]
    /\ UNCHANGED <<pc>>

LoopTerminate(lp) ==
    /\ pc[lp] = 4
    /\ msgs' = msgs \cup { [type |-> "terminate",
                            src  |-> lp,
                            dst  |-> "Client",
                            payload |-> NoMessage] }
    /\ pc' = [pc EXCEPT ![lp] = 5]
    /\ UNCHANGED <<color, sample, iterCnt>>

QueryRespond(qp) ==
    /\ pc[qp] = 1
    /\ \E m \in msgs : 
          /\ m.type = "query"
          /\ m.dst = qp
    /\ LET m   == CHOOSE mm \in msgs : mm.type = "query" /\ mm.dst = qp
           n   == NodeOfQuery(qp)
           curColor == IF color[n] = NoColor THEN m.payload ELSE color[n]
           reply == [type |-> "reply",
                     src  |-> qp,
                     dst  |-> m.src,
                     payload |-> curColor]
       IN 
          /\ color' = [color EXCEPT ![n] = curColor]
          /\ msgs'   = (msgs \ {m}) \cup {reply}
          /\ pc' = [pc EXCEPT ![qp] = 1] \* stay in loop
    /\ UNCHANGED <<sample, iterCnt>>

QueryExit(qp) ==
    /\ pc[qp] = 1
    /\ AllLoopsDone
    /\ pc' = [pc EXCEPT ![qp] = 3]
    /\ UNCHANGED <<color, msgs, sample, iterCnt>>

ClientDoneAction ==
    /\ pc["Client"] = 2
    /\ pc' = [pc EXCEPT !["Client"] = 2]
    /\ UNCHANGED <<color, msgs, sample, iterCnt, pc>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E lp \in SlushLoopProcess : LoopWaitForColor(lp)
    \/ \E lp \in SlushLoopProcess : LoopStartIteration(lp)
    \/ \E lp \in SlushLoopProcess : LoopSendQueries(lp)
    \/ \E lp \in SlushLoopProcess : LoopCollectReplies(lp)
    \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
    \/ \E qp \in SlushQueryProcess : QueryRespond(qp)
    \/ \E qp \in SlushQueryProcess : QueryExit(qp)
    \/ ClientAssign
    \/ ClientDoneAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iterCnt>>

\* ----------------------------------------------------------------------
\* Invariant (type safety)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ color \in [Node -> Colors]
    /\ msgs \subseteq { m \in Message :
                       m.type \in {"query","reply","terminate"} /\
                       m.src \in ProcSet /\
                       m.dst \in ProcSet /\
                       (m.type = "query"    => m.payload \in Colors) /\
                       (m.type = "reply"    => m.payload \in Colors) /\
                       (m.type = "terminate"=> m.payload = NoMessage)}
    /\ pc \in [ProcSet -> Nat]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iterCnt \in [SlushLoopProcess -> Nat]

\* ----------------------------------------------------------------------
\* The only required invariant
\* ----------------------------------------------------------------------
TypeInvariant == TypeOK

=============================================================================