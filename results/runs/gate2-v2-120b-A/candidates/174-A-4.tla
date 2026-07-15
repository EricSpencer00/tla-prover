---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Node,                 \* Set of node identifiers
    SlushLoopProcess,     \* Set of loop process identifiers (one per node)
    SlushQueryProcess,    \* Set of query process identifiers (one per node)
    HostMapping,          \* Set of triples <<proc, "loop"/"query", node>>
    SlushIterationCount,  \* Max number of iterations each loop runs
    SampleSetSize,        \* Number of peers sampled each round
    PickFlipThreshold,    \* Minimum number of same‑color replies to flip
    NoColor,              \* Symbol for “uncolored”
    NoMessage             \* Symbol for the empty message (used for termination)

\* ----------------------------------------------------------------------
\* Types derived from the constants (useful for the type invariant)
NodeSet          == Node
LoopProcSet      == SlushLoopProcess
QueryProcSet     == SlushQueryProcess
Color            == {NoColor} \cup {"red", "blue"}
MsgKind          == {"query", "reply", "term"}
\* ----------------------------------------------------------------------
\* Record types for messages
QueryMsg   == [kind : {"query"}, src : LoopProcSet, dst : QueryProcSet, color : Color]
ReplyMsg   == [kind : {"reply"}, src : QueryProcSet, dst : LoopProcSet, color : Color]
TermMsg    == [kind : {"term"}, src : LoopProcSet]
Message    == QueryMsg \cup ReplyMsg \cup TermMsg
\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    colors,          \* [node -> Color] current color of each node
    msgs,            \* Set of in‑flight messages
    pc,              \* [proc -> Nat] program counter for each process
    sampleSet,       \* [loopProc -> SUBSET Node] current sample (may be empty)
    iterCount         \* [loopProc -> Nat] iterations completed per loop

\* ----------------------------------------------------------------------
\* Helper definitions
HostLoop(node) == CHOOSE p \in SlushLoopProcess : <<p, "loop", node>> \in HostMapping
HostQuery(node) == CHOOSE p \in SlushQueryProcess : <<p, "query", node>> \in HostMapping

OtherNodes(node) == Node \ {node}

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ colors = [n \in Node |-> NoColor]
    /\ msgs    = {}
    /\ pc      = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> 0]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ iterCount = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Client process: assign a random color to an uncolored node
ClientAssign ==
    /\ pc["client"] = 0
    /\ \E n \in Node :
         /\ colors[n] = NoColor
         /\ colors' = [colors EXCEPT ![n] = "red"]  \* nondeterministically choose "red" or "blue"
    /\ UNCHANGED <<msgs, pc, sampleSet, iterCount>>
    /\ pc' = [pc EXCEPT !["client"] = 1]

ClientAssignBlue ==
    /\ pc["client"] = 0
    /\ \E n \in Node :
         /\ colors[n] = NoColor
         /\ colors' = [colors EXCEPT ![n] = "blue"]
    /\ UNCHANGED <<msgs, pc, sampleSet, iterCount>>
    /\ pc' = [pc EXCEPT !["client"] = 1]

ClientDone ==
    /\ pc["client"] = 1
    /\ \A n \in Node : colors[n] # NoColor
    /\ pc' = [pc EXCEPT !["client"] = 2]
    /\ UNCHANGED <<colors, msgs, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Loop process actions
RequireColor(lp) ==
    /\ pc[lp] = 0
    /\ \E n \in Node : <<lp, "loop", n>> \in HostMapping
    /\ colors[n] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = 1]
    /\ UNCHANGED <<colors, msgs, sampleSet, iterCount>>

SelectSample(lp) ==
    /\ pc[lp] = 1
    /\ \E n \in Node :
         /\ colors[n] # NoColor
         /\ LET q == HostQuery(n) IN
                /\ sampleSet' = [sampleSet EXCEPT ![lp] = {n}]
                /\ msgs' = msgs \cup { [kind |-> "query",
                                         src  |-> lp,
                                         dst  |-> q,
                                         color|-> colors[n]] }
    /\ pc' = [pc EXCEPT ![lp] = 2]
    /\ UNCHANGED <<colors, iterCount>>

ReceiveAllReplies(lp) ==
    /\ pc[lp] = 2
    /\ \A n \in sampleSet[lp] :
         \E r \in msgs :
            /\ r.kind = "reply"
            /\ r.src = HostQuery(n)
            /\ r.dst = lp
    /\ \LET replies == { r \in msgs :
                           r.kind = "reply" /\ r.dst = lp } IN
       LET redCnt  == Cardinality({ r \in replies : r.color = "red" }) IN
       LET blueCnt == Cardinality({ r \in replies : r.color = "blue" }) IN
       /\ IF redCnt >= PickFlipThreshold THEN
              colors' = [colors EXCEPT ![HostLoop(n)] = "red" \* adopt red
                         ]
          ELSE IF blueCnt >= PickFlipThreshold THEN
              colors' = [colors EXCEPT ![HostLoop(n)] = "blue"]
          ELSE colors' = colors
    /\ msgs' = msgs \ { r \in msgs : r.kind = "reply" /\ r.dst = lp }
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
    /\ iterCount' = [iterCount EXCEPT ![lp] = @ + 1]
    /\ IF iterCount[lp] + 1 >= SlushIterationCount
          THEN pc' = [pc EXCEPT ![lp] = 3]      \* move to termination
          ELSE pc' = [pc EXCEPT ![lp] = 1]      \* start next round
    /\ UNCHANGED <<>>

TerminateLoop(lp) ==
    /\ pc[lp] = 3
    /\ msgs' = msgs \cup { [kind |-> "term", src |-> lp] }
    /\ pc' = [pc EXCEPT ![lp] = 4]
    /\ UNCHANGED <<colors, sampleSet, iterCount>>

LoopDone(lp) ==
    /\ pc[lp] = 4
    /\ pc' = [pc EXCEPT ![lp] = 5]
    /\ UNCHANGED <<colors, msgs, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Query process actions
QueryReceive(lp, qp) ==
    /\ pc[qp] = 0
    /\ \E m \in msgs :
         /\ m.kind = "query"
         /\ m.dst = qp
         /\ m.src = lp
    /\ LET n == CHOOSE node \in Node : <<qp, "query", node>> \in HostMapping IN
       /\ IF colors[n] = NoColor
             THEN colors' = [colors EXCEPT ![n] = m.color]
             ELSE colors' = colors
    /\ msgs' = (msgs \ {m}) \cup { [kind |-> "reply",
                                    src  |-> qp,
                                    dst  |-> lp,
                                    color|-> colors'[n]] }
    /\ pc' = [pc EXCEPT ![qp] = 0]   \* stay in receive loop
    /\ UNCHANGED <<sampleSet, iterCount>>

\* Query processes exit when every loop has sent a termination message
QueryExit(qp) ==
    /\ pc[qp] = 0
    /\ \A lp \in SlushLoopProcess :
          [kind |-> "term", src |-> lp] \in msgs
    /\ pc' = [pc EXCEPT ![qp] = 1]
    /\ UNCHANGED <<colors, msgs, sampleSet, iterCount>>

QueryDone(qp) ==
    /\ pc[qp] = 1
    /\ pc' = [pc EXCEPT ![qp] = 2]
    /\ UNCHANGED <<colors, msgs, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \/ ClientAssign
    \/ ClientAssignBlue
    \/ ClientDone
    \/ \E lp \in SlushLoopProcess : RequireColor(lp)
    \/ \E lp \in SlushLoopProcess : SelectSample(lp)
    \/ \E lp \in SlushLoopProcess : ReceiveAllReplies(lp)
    \/ \E lp \in SlushLoopProcess : TerminateLoop(lp)
    \/ \E lp \in SlushLoopProcess : LoopDone(lp)
    \/ \E qp \in SlushQueryProcess :
            \E lp \in SlushLoopProcess : QueryReceive(lp, qp)
    \/ \E qp \in SlushQueryProcess : QueryExit(qp)
    \/ \E qp \in SlushQueryProcess : QueryDone(qp)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<colors, msgs, pc, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Type invariant (the required INVARIANT)
TypeInvariant ==
    /\ colors \in [Node -> Color]
    /\ msgs \subseteq Message
    /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) -> Nat]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ iterCount \in [SlushLoopProcess -> Nat]

\* ----------------------------------------------------------------------
\* Additional (optional) termination property
Terminating == []<>(\A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) : pc[p] = 5)

=============================