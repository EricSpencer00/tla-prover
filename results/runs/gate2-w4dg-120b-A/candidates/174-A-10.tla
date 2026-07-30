---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node,
    SlushLoopProcess,
    SlushQueryProcess,
    HostMapping,
    SlushIterationCount,
    SampleSetSize,
    PickFlipThreshold,
    NoColor,
    NoMessage

\* A message is a tuple: {kind, src, dst, ctype, content} where ctype is the
\* concrete type (query, reply, terminate) and content is the optional payload.
Message == [kind: {"loop", "query", "client"}, src: Node, dst: Node,
            ctype: {"query", "reply", "terminate"}, content: 0..PickFlipThreshold]

VARIABLES
    nodeColor,
    msgs,
    pc,
    sampleSet,
    iterations

vars == <<nodeColor, msgs, pc, sampleSet, iterations>>

TypeInvariant ==
    /\ nodeColor \in [Node -> {NoColor} \cup 0..PickFlipThreshold]
    /\ msgs \subseteq Message
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> 0..4]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ nodeColor = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> 0]
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ iterations = [p \in SlushLoopProcess |-> 0]

\* The client picks an uncolored node and assigns it a color (simulating a
\* transaction arriving to color the node).
ClientAssignColor ==
    /\ pc["client"] = 0
    /\ \E n \in Node :
         /\ nodeColor[n] = NoColor
         /\ \E col \in 0..PickFlipThreshold : nodeColor' = [nodeColor EXCEPT ![n] = col]
    /\ pc' = [pc EXCEPT !["client"] = 1]
    /\ UNCHANGED <<msgs, sampleSet, iterations>>

RequireColor ==
    /\ \E p \in SlushLoopProcess, n \in Node :
         /\ [p, n] \in HostMapping
         /\ nodeColor[n] # NoColor
         /\ pc[p] = 0
         /\ pc' = [pc EXCEPT ![p] = 1]
    /\ UNCHANGED <<nodeColor, msgs, sampleSet, iterations>>

\* The loop process opens an iteration by sampling a random fixed-size peer set
\* and sending a query message to each sampled peer's query process.
QuerySampleSet ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = 1
         /\ iterations[p] < SlushIterationCount
         /\ \E peers \in SUBSET (Node \ {CHOOSE n \in Node : [p, n] \in HostMapping}) :
              /\ Cardinality(peers) = SampleSetSize
              /\ sampleSet' = [sampleSet EXCEPT ![p] = peers]
              /\ msgs' = msgs \cup
                   { [kind |-> "loop", src |-> CHOOSE n \in Node : [p, n] \in HostMapping,
                      dst |-> q, ctype |-> "query", content |-> nodeColor[CHOOSE n \in Node : [p, n] \in HostMapping]]
                      : q \in peers }
         /\ pc' = [pc EXCEPT ![p] = 2]
    /\ UNCHANGED <<nodeColor, iterations>>

\* The query process replies to a query: it adopts the query color if uncolored,
\* then sends back a reply with its current color.
RespondToQuery ==
    /\ \E m \in msgs :
         /\ m.ctype = "query"
         /\ \E q \in SlushQueryProcess :
              /\ [q, m.dst] \in HostMapping
              /\ pc[q] = 0
              /\ nodeColor' = [nodeColor EXCEPT ![m.dst] =
                     IF nodeColor[m.dst] = NoColor THEN m.content ELSE nodeColor[m.dst]]
              /\ msgs' = (msgs \ {m}) \cup
                   {[kind |-> "query", src |-> m.dst, dst |-> m.src,
                     ctype |-> "reply", content |-> nodeColor[m.dst]]}
              /\ pc' = [pc EXCEPT ![q] = 1]
    /\ UNCHANGED <<sampleSet, iterations>>

TallyReplies ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = 2
         /\ LET ok == \A q \in sampleSet[p] : \E m \in msgs : m.ctype = "reply" /\ m.src = q
            in ok
         /\ LET cnt == [c \in 0..PickFlipThreshold |-> Cardinality(
                {q \in sampleSet[p] : \E m \in msgs : m.ctype = "reply" /\ m.src = q /\ m.content = c})]
            in nodeColor' = [nodeColor EXCEPT ![CHOOSE n \in Node : [p, n] \in HostMapping] =
                  IF \E c \in 0..PickFlipThreshold : cnt[c] >= PickFlipThreshold
                     THEN CHOOSE c \in 0..PickFlipThreshold : cnt[c] >= PickFlipThreshold
                     ELSE nodeColor[CHOOSE n \in Node : [p, n] \in HostMapping]]
         /\ msgs' = {m \in msgs : ~(m.kind = "query" /\ m.dst \in sampleSet[p])}
         /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
         /\ iterations' = [iterations EXCEPT ![p] = iterations[p] + 1]
         /\ pc' = [pc EXCEPT ![p] = 3]
    /\ UNCHANGED <<>>

LoopTermination ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = 3
         /\ pc' = [pc EXCEPT ![p] = 4]
         /\ msgs' = msgs \cup
              { [kind |-> "loop", src |-> CHOOSE n \in Node : [p, n] \in HostMapping,
                 dst |-> CHOOSE n \in Node : [p, n] \in HostMapping, ctype |-> "terminate", content |-> 0] }
    /\ UNCHANGED <<nodeColor, sampleSet, iterations>>

QueryLoopExit ==
    /\ \E q \in SlushQueryProcess :
         /\ pc[q] = 1
         /\ \A p \in SlushLoopProcess : pc[p] = 4
         /\ pc' = [pc EXCEPT ![q] = 4]
    /\ UNCHANGED <<nodeColor, msgs, sampleSet, iterations>>

Next == ClientAssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
        \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ SF_vars(ClientAssignColor) /\ SF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
        /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination)
        /\ SF_vars(QueryLoopExit)

AllDone == \A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : pc[p] = 4

Termination == <>(AllDone)

====