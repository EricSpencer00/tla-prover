---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Node,                \* set of node identifiers
    SlushLoopProcess,    \* set of loop process identifiers (one per node)
    SlushQueryProcess,   \* set of query process identifiers (one per node)
    HostMapping,         \* set of triples [proc |-> process, "host" |-> node, type |-> "loop" \/ "query"]
    SlushIterationCount, \* number of iterations each loop process must perform
    SampleSetSize,       \* size of the random sample drawn each iteration
    PickFlipThreshold,   \* number of same‑color replies needed to adopt that color
    NoColor,             \* special value meaning “uncolored”
    NoMessage            \* special value meaning “no message in flight”

\* -----------------------------------------------------------------
\* Derived mappings from HostMapping
\* -----------------------------------------------------------------
LoopHost == { p \in SlushLoopProcess : 
               \E m \in HostMapping : 
                 /\ m["proc"] = p
                 /\ m["type"] = "loop"
                 /\ m["host"] \in Node }

QueryHost == { q \in SlushQueryProcess :
                \E m \in HostMapping :
                  /\ m["proc"] = q
                  /\ m["type"] = "query"
                  /\ m["host"] \in Node }

Loop2Node == [p \in SlushLoopProcess |-> 
                CHOOSE m \in HostMapping : 
                  /\ m["proc"] = p
                  /\ m["type"] = "loop"
                  /\ m["host"] \in Node
                  /\ m["host"]]

Node2Loop == [n \in Node |-> 
                CHOOSE m \in HostMapping :
                  /\ m["host"] = n
                  /\ m["type"] = "loop"
                  /\ m["proc"] \in SlushLoopProcess]

Query2Node == [q \in SlushQueryProcess |-> 
                CHOOSE m \in HostMapping :
                  /\ m["proc"] = q
                  /\ m["type"] = "query"
                  /\ m["host"] \in Node
                  /\ m["host"]]

Node2Query == [n \in Node |-> 
                CHOOSE m \in HostMapping :
                  /\ m["host"] = n
                  /\ m["type"] = "query"
                  /\ m["proc"] \in SlushQueryProcess]

\* -----------------------------------------------------------------
\* Types of messages
\* -----------------------------------------------------------------
MsgType == {"query", "reply", "terminate"}

Message == [type : MsgType,
            src  : SlushLoopProcess \/ SlushQueryProcess \/ {"client"},
            dst  : SlushLoopProcess \/ SlushQueryProcess \/ {"none"},
            color: NoColor \/ {"red", "blue"},
            sample : SUBSET SlushQueryProcess]  \* only used for "query" messages

\* -----------------------------------------------------------------
\* State variables
\* -----------------------------------------------------------------
VARIABLES
    nodeColor,   \* [node -> NoColor \/ {"red","blue"}]
    msgs,        \* set of Message
    pc,          \* [proc -> "client_assign" \/ "loop_wait" \/ "query_send" \/ "wait_replies" \/ "loop_done" \/ "query_wait" \/ "query_done"]
    sampleSet,   \* [proc \in SlushLoopProcess -> SUBSET SlushQueryProcess]
    iterCount    \* [proc \in SlushLoopProcess -> Nat]

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
Colors == {"red", "blue"}

NodeUncolored(n) == nodeColor[n] = NoColor

\* Clients assigns an uncolored node a random color
ClientAssign ==
    \E n \in Node : 
        /\ NodeUncolored(n)
        /\ nodeColor' = [nodeColor EXCEPT ![n] = CHOOSE c \in Colors : TRUE]
        /\ UNCHANGED <<msgs, pc, sampleSet, iterCount>>

\* Loop process waits until its host node is colored
LoopRequireColor(p) ==
    LET n == Loop2Node[p] IN
    /\ nodeColor[n] # NoColor
    /\ pc' = [pc EXCEPT ![p] = "query_send"]
    /\ UNCHANGED <<nodeColor, msgs, sampleSet, iterCount>>

\* Loop process selects a random sample of other nodes' query processes
LoopSelectSample(p) ==
    LET n == Loop2Node[p] IN
    /\ pc[p] = "query_send"
    /\ sampleSet' = [sampleSet EXCEPT ![p] = 
          CHOOSE s \in SUBSET (SlushQueryProcess \ {Node2Query[n]}) :
                Cardinality(s) = SampleSetSize]
    /\ msgs' = msgs \cup {
          [type |-> "query",
           src  |-> p,
           dst  |-> s,
           color|-> nodeColor[n],
           sample|-> {}] : s \in sampleSet'[p] }
    /\ pc' = [pc EXCEPT ![p] = "wait_replies"]
    /\ UNCHANGED <<nodeColor, iterCount>>

\* Query process handles an incoming query
QueryHandle ==
    \E q \in SlushQueryProcess, m \in msgs :
        /\ m.type = "query"
        /\ m.dst = q
        /\ LET n == Query2Node[q] IN
           IF nodeColor[n] = NoColor
              THEN nodeColor' = [nodeColor EXCEPT ![n] = m.color]
              ELSE nodeColor' = nodeColor
        /\ msgs' = (msgs \ {m}) \cup {
              [type |-> "reply",
               src  |-> q,
               dst  |-> m.src,
               color|-> nodeColor'[n],
               sample|-> {}] }
        /\ pc' = [pc EXCEPT ![q] = "query_wait"]
        /\ UNCHANGED <<sampleSet, iterCount>>

\* Loop process tallies replies
LoopTally(p) ==
    LET n == Loop2Node[p] IN
    /\ pc[p] = "wait_replies"
    /\ \A s \in sampleSet[p] :
          \E r \in msgs :
            /\ r.type = "reply"
            /\ r.src = s
            /\ r.dst = p
    /\ LET replies == { r \in msgs :
                         /\ r.type = "reply"
                         /\ r.dst = p } IN
       LET redCnt  == Cardinality({ r \in replies : r.color = "red" }) IN
       LET blueCnt == Cardinality({ r \in replies : r.color = "blue" }) IN
       /\ IF redCnt >= PickFlipThreshold
             THEN nodeColor' = [nodeColor EXCEPT ![n] = "red"]
          ELSE IF blueCnt >= PickFlipThreshold
             THEN nodeColor' = [nodeColor EXCEPT ![n] = "blue"]
          ELSE nodeColor' = nodeColor
    /\ msgs' = msgs \ { m \in msgs :
                         /\ m.type = "reply"
                         /\ m.dst = p }
    /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
    /\ iterCount' = [iterCount EXCEPT ![p] = @ + 1]
    /\ IF iterCount'[p] = SlushIterationCount
          THEN pc' = [pc EXCEPT ![p] = "loop_done"]
          ELSE pc' = [pc EXCEPT ![p] = "query_send"]
    /\ UNCHANGED <<pc, nodeColor>> 
    \* (nodeColor already updated above)

\* Loop process termination broadcasting
LoopTerminate(p) ==
    /\ pc[p] = "loop_done"
    /\ msgs' = msgs \cup {
          [type |-> "terminate",
           src  |-> p,
           dst  |-> "none",
           color|-> NoColor,
           sample|-> {}] }
    /\ pc' = [pc EXCEPT ![p] = "loop_done"] \* remain in done state
    /\ UNCHANGED <<nodeColor, sampleSet, iterCount>>

\* Query process exits when all loop processes have terminated
QueryExit(q) ==
    /\ pc[q] = "query_wait"
    /\ \A p \in SlushLoopProcess : 
          \E m \in msgs : 
            /\ m.type = "terminate"
            /\ m.src = p
    /\ pc' = [pc EXCEPT ![q] = "query_done"]
    /\ UNCHANGED <<nodeColor, msgs, sampleSet, iterCount>>

\* Stuttering step to keep model from deadlocking
Stutter ==
    UNCHANGED <<nodeColor, msgs, pc, sampleSet, iterCount>>

\* -----------------------------------------------------------------
\* Next-state relation
\* -----------------------------------------------------------------
Next ==
    \/ \E p \in SlushLoopProcess : 
           \/ LoopRequireColor(p)
           \/ LoopSelectSample(p)
           \/ LoopTally(p)
           \/ LoopTerminate(p)
    \/ \E q \in SlushQueryProcess :
           QueryHandle
           \/ QueryExit(q)
    \/ ClientAssign
    \/ Stutter

\* -----------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------
Init ==
    /\ nodeColor = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> 
            IF proc \in SlushLoopProcess THEN "loop_wait"
            ELSE IF proc \in SlushQueryProcess THEN "query_wait"
            ELSE "client_assign"]
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ iterCount = [p \in SlushLoopProcess |-> 0]

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_<<nodeColor, msgs, pc, sampleSet, iterCount>>

\* -----------------------------------------------------------------
\* Safety invariant (type correctness)
\* -----------------------------------------------------------------
TypeInvariant ==
    /\ nodeColor \in [Node -> (NoColor \/ Colors)]
    /\ msgs \subseteq Message
    /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) -> 
                {"client_assign", "loop_wait", "query_send", "wait_replies",
                 "loop_done", "query_wait", "query_done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iterCount \in [SlushLoopProcess -> Nat]
    /\ \A m \in msgs :
          /\ m.type \in MsgType
          /\ (m.type = "query" => 
                /\ m.src \in SlushLoopProcess
                /\ m.dst \in SlushQueryProcess
                /\ m.color \in (NoColor \/ Colors)
                /\ Cardinality(m.sample) = SampleSetSize)
          /\ (m.type = "reply" => 
                /\ m.src \in SlushQueryProcess
                /\ m.dst \in SlushLoopProcess
                /\ m.color \in Colors)
          /\ (m.type = "terminate" => 
                /\ m.src \in SlushLoopProcess
                /\ m.dst = "none"
                /\ m.color = NoColor)

=============================================================================