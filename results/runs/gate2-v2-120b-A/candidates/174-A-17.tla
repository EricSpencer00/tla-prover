---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants required by the .cfg
\* ----------------------------------------------------------------------
CONSTANTS
    Node,               \* set of node identifiers
    SlushLoopProcess,   \* set of loop process identifiers
    SlushQueryProcess,  \* set of query process identifiers
    HostMapping,        \* set of triples <<proc, role, node>>
    SlushIterationCount,\* number of iterations each loop process must run
    SampleSetSize,      \* size of the random sample each loop process queries
    PickFlipThreshold,  \* threshold of matching replies needed to flip
    NoColor,            \* sentinel for "uncolored"
    NoMessage           \* sentinel for "no message"

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    nodeColor,          \* [node -> color or NoColor]
    messages,           \* set of in‑flight messages
    procPC,             \* [process -> program counter label]
    loopSample,         \* [loopProc -> set of query processes currently sampled]
    loopIter,           \* [loopProc -> number of completed iterations]
    loopDone,           \* [loopProc -> BOOLEAN indicating termination]
    queryDone,          \* [queryProc -> BOOLEAN indicating termination]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Roles used in HostMapping triples
LoopRole  == "Loop"
QueryRole == "Query"

\* Function giving the node that a process hosts
NodeOf(p) == 
    IF p \in SlushLoopProcess  THEN
        CHOOSE n \in Node : <<p, LoopRole, n>> \in HostMapping
    ELSE
        CHOOSE n \in Node : <<p, QueryRole, n>> \in HostMapping

\* ----------------------------------------------------------------------
\* Message type definitions
\* ----------------------------------------------------------------------
MsgQuery == [type : "Query", from : SlushLoopProcess, to : SlushQueryProcess,
             color : {"Red","Blue","NoColor"}]

MsgReply == [type : "Reply", from : SlushQueryProcess, to : SlushLoopProcess,
             color : {"Red","Blue","NoColor"}]

MsgTerm  == [type : "Term", from : SlushLoopProcess, to : SlushQueryProcess]

Message == MsgQuery \cup MsgReply \cup MsgTerm

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ nodeColor = [n \in Node |-> NoColor]
    /\ messages   = {}
    /\ procPC     = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> "Start"]
    /\ loopSample = [lp \in SlushLoopProcess |-> {}]
    /\ loopIter   = [lp \in SlushLoopProcess |-> 0]
    /\ loopDone   = [lp \in SlushLoopProcess |-> FALSE]
    /\ queryDone  = [qp \in SlushQueryProcess |-> FALSE]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssign ==
    /\ procPC["Client"] = "Start"
    /\ \E n \in Node :
        /\ nodeColor[n] = NoColor
        /\ nodeColor' = [nodeColor EXCEPT ![n] = RandomChoice(Colors)]
    /\ UNCHANGED <<messages, procPC, loopSample, loopIter, loopDone, queryDone>>

RequireColor(lp) ==
    /\ procPC[lp] = "RequireColor"
    /\ LET n == NodeOf(lp) IN nodeColor[n] # NoColor
    /\ procPC' = [procPC EXCEPT ![lp] = "DoSample"]
    /\ UNCHANGED <<nodeColor, messages, loopSample, loopIter, loopDone, queryDone>>

DoSample(lp) ==
    /\ procPC[lp] = "DoSample"
    /\ loopIter[lp] < SlushIterationCount
    /\ loopIter' = [loopIter EXCEPT ![lp] = @ + 1]
    /\ loopSample' = [loopSample EXCEPT ![lp] = 
            { q \in SlushQueryProcess :
                q # NodeOf(lp) \in Node /\ 
                Cardinality({}) < SampleSetSize } ]  \* nondeterministically pick a set of size SampleSetSize
    /\ \A q \in loopSample'[lp] :
        messages' = messages \cup { [type |-> "Query",
                                      from |-> lp,
                                      to   |-> q,
                                      color|-> nodeColor[NodeOf(lp)]] }
    /\ procPC' = [procPC EXCEPT ![lp] = "CollectReplies"]
    /\ UNCHANGED <<nodeColor, loopDone, queryDone>>

CollectReplies(lp) ==
    /\ procPC[lp] = "CollectReplies"
    /\ \A q \in loopSample[lp] :
        \E m \in messages :
            /\ m.type = "Reply"
            /\ m.from = q
            /\ m.to   = lp
    /\ LET redCount == Cardinality({ q \in loopSample[lp] :
            \E m \in messages :
                /\ m.type = "Reply"
                /\ m.from = q /\ m.to = lp /\ m.color = "Red" })
        blueCount == Cardinality({ q \in loopSample[lp] :
            \E m \in messages :
                /\ m.type = "Reply"
                /\ m.from = q /\ m.to = lp /\ m.color = "Blue" })
        newColor == 
            IF redCount >= PickFlipThreshold THEN "Red"
            ELSE IF blueCount >= PickFlipThreshold THEN "Blue"
            ELSE nodeColor[NodeOf(lp)]
    IN
    /\ nodeColor' = [nodeColor EXCEPT ![NodeOf(lp)] = newColor]
    /\ messages'   = messages \ { m \in messages :
                                    m.type = "Reply" /\ m.to = lp }
    /\ procPC'     = [procPC EXCEPT ![lp] = 
            IF loopIter[lp] = SlushIterationCount THEN "SendTerm"
            ELSE "DoSample"]
    /\ loopSample' = [loopSample EXCEPT ![lp] = {}]
    /\ UNCHANGED <<loopIter, loopDone, queryDone>>

SendTerm(lp) ==
    /\ procPC[lp] = "SendTerm"
    /\ messages' = messages \cup { [type |-> "Term", from |-> lp, to |-> q] 
                                    : q \in SlushQueryProcess }
    /\ loopDone' = [loopDone EXCEPT ![lp] = TRUE]
    /\ procPC'   = [procPC EXCEPT ![lp] = "Done"]
    /\ UNCHANGED <<nodeColor, messages, loopSample, loopIter, queryDone>>

QueryLoop(qp) ==
    /\ procPC[qp] = "Start"
    /\ procPC' = [procPC EXCEPT ![qp] = "ReplyLoop"]
    /\ UNCHANGED <<nodeColor, messages, loopSample, loopIter, loopDone, queryDone>>

ReplyLoop(qp) ==
    /\ procPC[qp] = "ReplyLoop"
    /\ \E m \in messages :
        /\ m.type = "Query"
        /\ m.to   = qp
        /\ LET n == NodeOf(qp) IN
            IF nodeColor[n] = NoColor THEN
                nodeColor' = [nodeColor EXCEPT ![n] = m.color]
            ELSE
                nodeColor' = nodeColor
        /\ LET reply == [type |-> "Reply",
                         from |-> qp,
                         to   |-> m.from,
                         color|-> nodeColor'[n]] IN
           messages' = (messages \ {m}) \cup {reply}
    /\ UNCHANGED <<procPC, loopSample, loopIter, loopDone, queryDone>>

QueryStop(qp) ==
    /\ procPC[qp] = "ReplyLoop"
    /\ \A lp \in SlushLoopProcess : loopDone[lp] = TRUE
    /\ procPC' = [procPC EXCEPT ![qp] = "Done"]
    /\ queryDone' = [queryDone EXCEPT ![qp] = TRUE]
    /\ UNCHANGED <<nodeColor, messages, loopSample, loopIter, loopDone>>

DoneProcess(p) ==
    /\ procPC[p] = "Done"
    /\ UNCHANGED <<nodeColor, messages, procPC, loopSample, loopIter, loopDone, queryDone>>

Next ==
    \/ \E n \in Node : 
          /\ nodeColor[n] = NoColor
          /\ nodeColor' = [nodeColor EXCEPT ![n] = RandomChoice(Colors)]
          /\ UNCHANGED <<messages, procPC, loopSample, loopIter, loopDone, queryDone>>
    \/ \E lp \in SlushLoopProcess :
          \/ RequireColor(lp)
          \/ DoSample(lp)
          \/ CollectReplies(lp)
          \/ SendTerm(lp)
    \/ \E qp \in SlushQueryProcess :
          \/ QueryLoop(qp)
          \/ ReplyLoop(qp)
          \/ QueryStop(qp)
    \/ \E p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) :
          DoneProcess(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<nodeColor, messages, procPC, loopSample,
                              loopIter, loopDone, queryDone>>

\* ----------------------------------------------------------------------
\* Type invariant (the only invariant required by the .cfg)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ nodeColor \in [Node -> (Colors \cup {NoColor})]
    /\ messages \subseteq Message
    /\ procPC \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) -> 
                    {"Start","RequireColor","DoSample","CollectReplies",
                     "SendTerm","ReplyLoop","Done"} ]
    /\ loopSample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ loopIter \in [SlushLoopProcess -> Nat]
    /\ loopDone \in [SlushLoopProcess -> BOOLEAN]
    /\ queryDone \in [SlushQueryProcess -> BOOLEAN]

TypeInvariant == TypeOK

\* ----------------------------------------------------------------------
\* Theorem (optional, but useful for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

====