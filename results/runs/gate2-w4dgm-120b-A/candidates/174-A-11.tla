---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* The Slush protocol: a metastable consensus mechanism in which loop processes   *)
(* repeatedly sample peer query processes and adopt a sufficiently popular color.  *)
(* This is a language encoding of the protocol, not a probabilistic model.         *)

CONSTANTS
    Node,               \* the set of nodes
    SlushLoopProcess,   \* the set of loop processes (one per node)
    SlushQueryProcess,  \* the set of query processes (one per node)
    HostMapping,        \* set of triples <<loop, query, node>> linking a node to its  *)
    SlushIterationCount,\* max iterations per loop process
    SampleSetSize,      \* size of the sampled peer set
    PickFlipThreshold,  \* replies of this count trigger a color adoption
    NoColor,            \* the sentinel uncolored value
    NoMessage           \* the sentinel no-message value

\* Each loop and query process is tagged with the node it belongs to.
NodeOfLoop(p) == CHOOSE n \in Node : <<p, CHOOSE q \in SlushQueryProcess : <<p, q, n>> \in HostMapping, n>> \in HostMapping
NodeOfQuery(q) == CHOOSE n \in Node : CHOOSE p \in SlushLoopProcess : <<p, q, n>> \in HostMapping \in HostMapping

VARIABLES
    nodeColor,      \* [Node -> {c1, c2} \cup {NoColor}] color held at each node
    messageSet,     \* set of in-flight messages; each is a tuple whose shape is checked against MessageOK
    pc,             \* [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"wait","run","done"}] control state
    samplePeers,    \* [SlushLoopProcess -> SUBSET SlushQueryProcess] the sampled peer set per loop
    iterations      \* [SlushLoopProcess -> 0..SlushIterationCount] rounds completed

vars == <<nodeColor, messageSet, pc, samplePeers, iterations>>

MessageOK(m) ==
    \/ \E p \in SlushLoopProcess, q \in SlushQueryProcess, n \in Node, c \in {NoColor} \cup {"c1", "c2"} :
           m = <<"query", p, q, n, c>>
    \/ \E p \in SlushLoopProcess, q \in SlushQueryProcess, col \in {"c1", "c2"} :
           m = <<"reply", p, q, col>>
    \/ \E p \in SlushLoopProcess : m = <<"done", p>>

TypeOK ==
    /\ nodeColor \in [Node -> {"c1", "c2", NoColor}]
    /\ messageSet \subseteq SlushLoopProcess \cup SlushQueryProcess
    /\ \A m \in messageSet : MessageOK(m)
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"wait","run","done"}]
    /\ samplePeers \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ nodeColor = [n \in Node |-> NoColor]
    /\ messageSet = {}
    /\ pc = [x \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> "wait"]
    /\ samplePeers = [p \in SlushLoopProcess |-> {}]
    /\ iterations = [p \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node (a transaction).
ClientAssign ==
    /\ pc["client"] = "wait"
    /\ \E n \in Node, col \in {"c1", "c2"} :
        /\ nodeColor[n] = NoColor
        /\ nodeColor' = [nodeColor EXCEPT ![n] = col]
    /\ pc' = [pc EXCEPT !["client"] = "run"]
    /\ UNCHANGED <<messageSet, samplePeers, iterations>>

RequireColor(p) ==
    /\ pc[p] = "wait"
    /\ nodeColor[NodeOfLoop(p)] # NoColor
    /\ pc' = [pc EXCEPT ![p] = "run"]
    /\ UNCHANGED <<nodeColor, messageSet, samplePeers, iterations>>

\* The loop process samples a fixed-size peer set and queries each member for its color.
QueryPeers(p) ==
    /\ pc[p] = "run"
    /\ iterations[p] < SlushIterationCount
    /\ samplePeers[p] = {}
    /\ \E subset \in SUBSET SlushQueryProcess :
        /\ Cardinality(subset) = SampleSetSize
        /\ samplePeers' = [samplePeers EXCEPT ![p] = subset]
        /\ messageSet' = messageSet \cup
            {<<"query", p, q, NodeOfLoop(p), nodeColor[NodeOfLoop(p)]>> : q \in subset}
    /\ UNCHANGED <<nodeColor, pc, iterations>>

\* A query process adopts the sender's color if it is uncolored, then replies with its own.
ReplyToQuery ==
    \E q \in SlushQueryProcess :
        \E m \in messageSet :
            /\ m[1] = "query"
            /\ m[3] = q
            /\ LET p == m[2] IN
                 nodeColor' = [nodeColor EXCEPT ![NodeOfQuery(q)] =
                                 IF nodeColor[NodeOfQuery(q)] = NoColor THEN m[5] ELSE nodeColor[NodeOfQuery(q)]]
                 /\ messageSet' = (messageSet \ {m})
                     \cup {<<"reply", p, q, nodeColor[NodeOfQuery(q)]>>}
            /\ UNCHANGED <<pc, samplePeers, iterations>>

\* Once all sampled peers have replied, the node adopts a color if enough replies agree.
TallyReplies(p) ==
    /\ samplePeers[p] # {}
    /\ \A q \in samplePeers[p] : <<"reply", p, q, "c1">> \in messageSet \/ <<"reply", p, q, "c2">> \in messageSet
    /\ LET count1 == Cardinality({q \in samplePeers[p] : <<"reply", p, q, "c1">> \in messageSet})
           count2 == Cardinality({q \in samplePeers[p] : <<"reply", p, q, "c2">> \in messageSet})
       IN nodeColor' = [nodeColor EXCEPT ![NodeOfLoop(p)] =
                          IF count1 >= PickFlipThreshold THEN "c1"
                          ELSE IF count2 >= PickFlipThreshold THEN "c2"
                          ELSE nodeColor[NodeOfLoop(p)]]
    /\ messageSet' = {m \in messageSet : m[1] # "reply" \/ m[2] # p}
                        \cup {<<"done", p>>}
    /\ samplePeers' = [samplePeers EXCEPT ![p] = {}]
    /\ iterations' = [iterations EXCEPT ![p] = @ + 1]
    /\ UNCHANGED pc

\* Loop processes broadcast termination once fully done; query processes then exit.
LoopTerminate ==
    \E p \in SlushLoopProcess :
        /\ pc[p] = "run"
        /\ iterations[p] = SlushIterationCount
        /\ pc' = [pc EXCEPT ![p] = "done"]
        /\ messageSet' = messageSet \cup {<<"done", p>>}
        /\ UNCHANGED <<nodeColor, samplePeers, iterations>>

QueryLoopExit ==
    /\ \E q \in SlushQueryProcess :
        /\ pc[q] = "wait"
        /\ \A p \in SlushLoopProcess : <<"done", p>> \in messageSet
        /\ pc' = [pc EXCEPT ![q] = "done"]
    /\ UNCHANGED <<nodeColor, messageSet, samplePeers, iterations>>

Next ==
    \/ ClientAssign
    \/ \E p \in SlushLoopProcess : RequireColor(p) \/ QueryPeers(p) \/ TallyReplies(p)
    \/ ReplyToQuery
    \/ LoopTerminate
    \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ClientAssign)
        /\ \A p \in SlushLoopProcess : WF_vars(QueryPeers(p)) /\ WF_vars(TallyReplies(p))
        /\ \A q \in SlushQueryProcess : WF_vars(ReplyToQuery) /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

\* Convergence is probabilistic and not expressible in TLA+; we check only termination. *)
AllDone == <>(\A x \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : pc[x] = "done")
====