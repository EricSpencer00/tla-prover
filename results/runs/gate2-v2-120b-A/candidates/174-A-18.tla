---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

\* ---------- CONSTANTS ----------
CONSTANTS 
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop‑process identifiers (one per node)
    SlushQueryProcess,  \* Set of query‑process identifiers (one per node)
    HostMapping,        \* Set of triples [proc |-> p, query |-> q, node |-> n]
    SlushIterationCount,\* Max number of iterations each loop process may perform
    SampleSetSize,      \* Size of the random peer sample
    PickFlipThreshold,  \* Minimum number of matching replies to trigger a flip
    NoColor,            \* Distinguished value meaning “uncolored”
    NoMessage           \* Distinguished value meaning “no message in the channel”

\* ---------- DERIVED CONSTANTS ----------
NodeCount == Cardinality(Node)

\* ---------- MESSAGE TYPES ----------
MessageType == {"Query", "Reply", "Terminate"}

Message == 
    [type : MessageType,
     src  : SlushLoopProcess \cup SlushQueryProcess,
     dst  : SlushLoopProcess \cup SlushQueryProcess,
     payload : {NoColor} \cup Node]  \* payload for Query/Reply is a color

\* ---------- STATE VARIABLES ----------
VARIABLES
    color,          \* [node -> NoColor or a concrete color]
    msgs,           \* Set of in‑flight messages
    pc,             \* [proc -> "client" | "waitColor" | "sample" | "waitReplies" |
                         "processReplies" | "terminate" | "done"]
    sample,         \* [loopProc -> SUBSET Node]  (peers sampled this round)
    iterCount       \* [loopProc -> Nat]  (iterations completed)

\* ---------- INITIAL STATE ----------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ pc    = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |
                IF p = "client" THEN "client"
                ELSE IF p \in SlushLoopProcess THEN "waitColor"
                ELSE "replyLoop"]
    /\ sample   = [lp \in SlushLoopProcess |-> {}]
    /\ iterCount= [lp \in SlushLoopProcess |-> 0]

\* ---------- HELPERS ----------
HostNode(lp) == 
    CHOOSE n \in Node : 
        \E h \in HostMapping : 
            /\ h["proc"] = lp
            /\ h["node"] = n

HostNodeByQuery(qp) ==
    CHOOSE n \in Node :
        \E h \in HostMapping :
            /\ h["query"] = qp
            /\ h["node"] = n

OtherNodes(node) == Node \ {node}

\* ---------- ACTIONS ----------
ClientAssign ==
    /\ pc["client"] = "client"
    /\ \E n \in Node : 
        /\ color[n] = NoColor
        /\ \E c \in Node : c # n   \* two distinct colors are just two different node ids
        /\ color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, pc, sample, iterCount>>
    /\ pc' = [pc EXCEPT !["client"] = "client"]  \* client stays in same state

RequireColor(lp) ==
    /\ pc[lp] = "waitColor"
    /\ LET n == HostNode(lp) IN
       /\ color[n] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "sample"]
    /\ UNCHANGED <<color, msgs, sample, iterCount>>

QuerySampleSet(lp) ==
    /\ pc[lp] = "sample"
    /\ LET n == HostNode(lp) IN
       /\ sampleSize == SampleSetSize
       /\ sampleSet == { n2 \in OtherNodes(n) : TRUE }
       /\ sampleChosen == CHOOSE s \in SUBSET sampleSet : Cardinality(s) = sampleSize
    /\ sample' = [sample EXCEPT ![lp] = sampleChosen]
    /\ msgs'   = msgs \cup 
        { [type |-> "Query",
           src  |-> lp,
           dst  |-> q,
           payload |-> color[n]] :
           q \in { qpq["query"] : qpq \in HostMapping : qpq["node"] \in sampleChosen } }
    /\ pc' = [pc EXCEPT ![lp] = "waitReplies"]
    /\ UNCHANGED <<color, iterCount>>

RespondToQuery ==
    /\ \E qp \in SlushQueryProcess :
        /\ \E m \in msgs :
            /\ m.type = "Query"
            /\ m.dst = qp
            /\ LET n == HostNodeByQuery(qp) IN
               /\ IF color[n] = NoColor
                  THEN color' = [color EXCEPT ![n] = m.payload]
                  ELSE UNCHANGED color
            /\ msgs' = (msgs \ {m}) \cup 
               { [type |-> "Reply",
                  src  |-> qp,
                  dst  |-> m.src,
                  payload |-> IF color[n] = NoColor THEN m.payload ELSE color[n]] }
            /\ UNCHANGED <<pc, sample, iterCount, iterCount>>
    /\ UNCHANGED <<pc>>  \* (pc unchanged for all processes)

TallyReplies(lp) ==
    /\ pc[lp] = "waitReplies"
    /\ LET n == HostNode(lp) IN
       /\ pending == { m \in msgs :
                         /\ m.type = "Reply"
                         /\ m.dst = lp
                         /\ m.payload \in Node }
    /\ Cardinality(pending) = SampleSetSize
    /\ \E c \in Node :
        /\ CountReplies(pending, c) >= PickFlipThreshold
        /\ color' = [color EXCEPT ![n] = c]
    \/ UNCHANGED color
    /\ msgs' = msgs \ pending
    /\ pc'   = [pc EXCEPT ![lp] = "processReplies"]
    /\ UNCHANGED <<sample, iterCount>>

CountReplies(pending, col) ==
    Cardinality({ m \in pending : m.payload = col })

ProcessReplies(lp) ==
    /\ pc[lp] = "processReplies"
    /\ sample'   = [sample EXCEPT ![lp] = {}]
    /\ iterCount' = [iterCount EXCEPT ![lp] = @ + 1]
    /\ IF iterCount'[lp] < SlushIterationCount
       THEN pc' = [pc EXCEPT ![lp] = "sample"]
       ELSE pc' = [pc EXCEPT ![lp] = "terminate"]
    /\ UNCHANGED <<color, msgs>>

LoopTerminate(lp) ==
    /\ pc[lp] = "terminate"
    /\ msgs' = msgs \cup 
        { [type |-> "Terminate",
           src  |-> lp,
           dst  |-> "client",
           payload |-> NoMessage] }
    /\ pc' = [pc EXCEPT ![lp] = "done"]
    /\ UNCHANGED <<color, sample, iterCount>>

QueryLoopExit ==
    /\ \E qp \in SlushQueryProcess :
        /\ pc[qp] = "replyLoop"
        /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
    /\ pc' = [pc EXCEPT ![qp] = "done"]
    /\ UNCHANGED <<color, msgs, sample, iterCount>>

\* ---------- NEXT RELATION ----------
Next ==
    \/ ClientAssign
    \/ \E lp \in SlushLoopProcess : RequireColor(lp)
    \/ \E lp \in SlushLoopProcess : QuerySampleSet(lp)
    \/ RespondToQuery
    \/ \E lp \in SlushLoopProcess : TallyReplies(lp)
    \/ \E lp \in SlushLoopProcess : ProcessReplies(lp)
    \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
    \/ QueryLoopExit

\* ---------- SAFETY INVARIANT ----------
TypeInvariant ==
    /\ \A n \in Node : color[n] \in Node \cup {NoColor}
    /\ \A m \in msgs :
        /\ m.type \in MessageType
        /\ m.src  \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"}
        /\ m.dst  \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"}
        /\ IF m.type = "Query"
           THEN m.payload \in Node \cup {NoColor}
           ELSE IF m.type = "Reply"
                THEN m.payload \in Node \cup {NoColor}
                ELSE m.payload = NoMessage

\* ---------- SPECIFICATION ----------
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iterCount>>

\* ---------- INVARIANT DECLARATION ----------
INVARIANT TypeInvariant

====