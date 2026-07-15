---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(* Constants (to be supplied in the .cfg file)                             *)
(***************************************************************************)
CONSTANTS
    Node,                \* Set of node identifiers
    SlushLoopProcess,    \* Set of loop process identifiers (one per node)
    SlushQueryProcess,   \* Set of query process identifiers (one per node)
    HostMapping,         \* Set of triples <<proc, "type", node>>
    SlushIterationCount, \* Maximum number of iterations per loop process
    SampleSetSize,       \* Number of peers sampled each round
    PickFlipThreshold,   \* Flip threshold (minimum count for a color)
    NoColor,             \* Special value meaning "uncolored"
    NoMessage            \* Special value meaning "no message" / empty

(***************************************************************************)
(* Derived sets and helper definitions                                      *)
(***************************************************************************)

Colors == {"Red", "Blue"}

ProcType == {"Loop", "Query"}

\* For readability, define the mapping from a process to its node
\* HostMapping is assumed to be a set of triples <<proc, type, node>>
HostOf[p \in SlushLoopProcess] == 
    CHOOSE n \in Node : <<p, "Loop", n>> \in HostMapping

HostOf[p \in SlushQueryProcess] == 
    CHOOSE n \in Node : <<p, "Query", n>> \in HostMapping

\* The two process families must be of equal cardinality and each node
\* must appear exactly once in each family.
NodeSet == Node
LoopProcSet == SlushLoopProcess
QueryProcSet == SlushQueryProcess

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    nodeColor,      \* [node -> Colors \cup {NoColor}]
    messages,       \* Set of in‑flight messages (see Msg structure below)
    procPC,         \* [proc -> PC]   program counter per process
    sampleSet,      \* [loopProc -> SUBSET Node]  peers sampled this round
    iterCount       \* [loopProc -> Nat]          iterations completed

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Msg == 
    [type : {"Query", "Reply", "Terminate"},
     src  : SlushLoopProcess \cup SlushQueryProcess,
     dst  : SlushLoopProcess \cup SlushQueryProcess,
     payload : (Colors \cup {NoMessage})]

\* ----------------------------------------------------------------------
\* Program‑counter (PC) values – we list all needed states
\* ----------------------------------------------------------------------
ClientPC    == {"AssignColor", "Done"}
LoopPC      == {"WaitColor", "SamplePeers", "WaitReplies", "Done"}
QueryPC     == {"ReplyLoop", "Done"}

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ nodeColor = [n \in Node |-> NoColor]
    /\ messages   = {}
    /\ procPC     = [p \in (ClientPC? No) \cup LoopPC? = "Done" \cup QueryPC? = "Done" |-> 
                       IF p \in ClientPC THEN "AssignColor"
                       ELSE IF p \in LoopPC THEN "WaitColor"
                       ELSE "ReplyLoop"]
    /\ sampleSet  = [lp \in SlushLoopProcess |-> {}]
    /\ iterCount  = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
ClientAssign ==
    /\ procPC["Client"] = "AssignColor"
    /\ \E n \in Node :
          /\ nodeColor[n] = NoColor
          /\ \E c \in Colors :
                /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
                /\ procPC'  = [procPC EXCEPT !["Client"] = 
                                    IF \A m \in Node : nodeColor'[m] # NoColor
                                    THEN "Done"
                                    ELSE "AssignColor"]
                /\ UNCHANGED <<messages, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Loop process actions
\* ----------------------------------------------------------------------
LoopWaitColor ==
    /\ \E lp \in SlushLoopProcess :
          /\ procPC[lp] = "WaitColor"
          /\ nodeColor[HostOf[lp]] # NoColor
          /\ procPC' = [procPC EXCEPT ![lp] = "SamplePeers"]
          /\ UNCHANGED <<nodeColor, messages, sampleSet, iterCount>>

LoopSamplePeers ==
    /\ \E lp \in SlushLoopProcess :
          /\ procPC[lp] = "SamplePeers"
          /\ nodeColor[HostOf[lp]] # NoColor
          /\ \E peers \in SUBSET (Node \ {HostOf[lp]}) :
                /\ Cardinality(peers) = SampleSetSize
                /\ LET newMsgs == { [type |-> "Query",
                                    src  |-> lp,
                                    dst  |-> qproc,
                                    payload |-> nodeColor[HostOf[lp]]]
                                   : qproc \in SlushQueryProcess,
                                     HostOf[qproc] \in peers } IN
                   /\ messages' = messages \cup newMsgs
                   /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
                   /\ procPC' = [procPC EXCEPT ![lp] = "WaitReplies"]
                   /\ UNCHANGED <<nodeColor, iterCount>>
          /\ UNCHANGED messages

LoopWaitReplies ==
    /\ \E lp \in SlushLoopProcess :
          /\ procPC[lp] = "WaitReplies"
          /\ \A qproc \in SlushQueryProcess :
                (HostOf[qproc] \in sampleSet[lp]) => 
                \E m \in messages :
                    /\ m.type = "Reply"
                    /\ m.dst = lp
                    /\ m.src = qproc
          /\ LET replies == { m.payload : m \in messages,
                                          m.type = "Reply",
                                          m.dst = lp,
                                          m.src \in SlushQueryProcess,
                                          HostOf[m.src] \in sampleSet[lp] } IN
             /\ CountColor(c) == Cardinality({ n \in replies : n = c })
             /\ IF \E c \in Colors : CountColor(c) >= PickFlipThreshold
                THEN 
                    /\ nodeColor' = [nodeColor EXCEPT ![HostOf[lp]] = 
                                        CHOOSE c \in Colors : CountColor(c) >= PickFlipThreshold]
                ELSE nodeColor' = nodeColor
             /\ messages' = messages \ { m \in messages :
                                             m.type = "Reply" /\ m.dst = lp }
             /\ iterCount' = [iterCount EXCEPT ![lp] = @ + 1]
             /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
             /\ IF iterCount'[lp] = SlushIterationCount
                THEN procPC' = [procPC EXCEPT ![lp] = "Done"]
                ELSE procPC' = [procPC EXCEPT ![lp] = "SamplePeers"]
             /\ UNCHANGED <<procPC, sampleSet>>

LoopTerminate ==
    /\ \E lp \in SlushLoopProcess :
          /\ procPC[lp] = "Done"
          /\ messages' = messages \cup 
                { [type |-> "Terminate",
                   src  |-> lp,
                   dst  |-> "All",
                   payload |-> NoMessage] }
          /\ UNCHANGED <<nodeColor, procPC, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Query process actions
\* ----------------------------------------------------------------------
QueryReply ==
    /\ \E qp \in SlushQueryProcess :
          /\ procPC[qp] = "ReplyLoop"
          /\ \E m \in messages :
                /\ m.type = "Query"
                /\ m.dst = qp
                /\ LET n == HostOf[qp] IN
                   IF nodeColor[n] = NoColor
                      THEN nodeColor' = [nodeColor EXCEPT ![n] = m.payload]
                      ELSE nodeColor' = nodeColor
                /\ let replyMsg == [type |-> "Reply",
                                    src  |-> qp,
                                    dst  |-> m.src,
                                    payload |-> nodeColor'[HostOf[m.src]]] in
                   messages' = (messages \ {m}) \cup {replyMsg}
                /\ UNCHANGED <<procPC, sampleSet, iterCount>>
          /\ procPC' = [procPC EXCEPT ![qp] = "ReplyLoop"]

QueryDone ==
    /\ \A qp \in SlushQueryProcess : procPC[qp] = "ReplyLoop"
    /\ \A lp \in SlushLoopProcess : procPC[lp] = "Done"
    /\ procPC' = [procPC EXCEPT ![qp] = "Done" | qp \in SlushQueryProcess]
    /\ UNCHANGED <<nodeColor, messages, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Stuttering step (allows the model to stay in a state)
\* ----------------------------------------------------------------------
Stutter ==
    UNCHANGED <<nodeColor, messages, procPC, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ LoopWaitColor
    \/ LoopSamplePeers
    \/ LoopWaitReplies
    \/ LoopTerminate
    \/ QueryReply
    \/ QueryDone
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<nodeColor, messages, procPC, sampleSet, iterCount>>

\* ----------------------------------------------------------------------
\* Safety invariant (type invariant)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ nodeColor \in [Node -> (Colors \cup {NoColor})]
    /\ messages \subseteq Msg
    /\ procPC \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) ->
                       {"AssignColor", "Done", "WaitColor", "SamplePeers",
                        "WaitReplies", "ReplyLoop", "Terminate"}]

=============================================================================