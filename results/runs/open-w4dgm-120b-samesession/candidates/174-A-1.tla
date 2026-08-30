---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

\* Nodes and their paired loop/query processes are linked by HostMapping,
\* a set of triples <node, loop, query>. All processes share one message set.
\* Slush is a metastable protocol: convergence to a single color is
\* probabilistic under real network conditions, so the spec tracks only
\* the loop-iteration, not the convergence outcome itself.

Hosts == { h[1] : h \in HostMapping }

VARIABLES color, msgs, pc, sample, loopIter

vars == << color, msgs, pc, sample, loopIter >>

MessageTypes == {"query", "queryReply", "terminate"}

TypeOK ==
    /\ color \in [Node -> (0..1) \union {NoColor}]
    /\ msgs \subseteq [mtype : MessageTypes,
                       dest : SlushLoopProcess \union SlushQueryProcess,
                       src : SlushLoopProcess \union SlushQueryProcess,
                       body : (0..1) \union {NoColor}]
    /\ pc \in [SlushLoopProcess -> {"waitingForColor", "done"}]
              \union [SlushQueryProcess -> {"replyLoop", "done"}]
              \union [SlushQueryProcess -> {"replyLoop", "done"}]
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ loopIter \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in SlushLoopProcess |-> "waitingForColor"]
             \union [q \in SlushQueryProcess |-> "replyLoop"]
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ loopIter = [p \in SlushLoopProcess |-> 0]

\* The client assigns a random initial color to some uncolored node.
ClientAssignColor ==
    /\ \E n \in Node, c \in (0..1) :
         /\ color[n] = NoColor
         /\ color' = [color EXCEPT ![n] = c]
    \/ UNCHANGED << msgs, pc, sample, loopIter >>

RequireColor ==
    /\ \E p \in SlushLoopProcess :
         /\ pc[p] = "waitingForColor"
         /\ \E n \in Node : <n, p, CHOOSE q \in SlushQueryProcess : <n, p, q> \in HostMapping>
         /\ color[n] # NoColor
         /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED << color, msgs, sample, loopIter >>

\* Loop processes pick a random peer sample each iteration; the sample
\* set is cleared once the iteration completes.
QuerySampleSet ==
    /\ \E p \in SlushLoopProcess, qset \in SUBSET SlushQueryProcess :
         /\ pc[p] = "done"
         /\ loopIter[p] < SlushIterationCount
         /\ Cardinality(qset) = SampleSetSize
         /\ sample' = [sample EXCEPT ![p] = qset]
         /\ msgs' = msgs \union
              { [mtype |-> "query", dest |-> q, src |-> p, body |-> color[CHOOSE n \in Hosts : <n, p, q> \in HostMapping]]
                : q \in qset }
    /\ UNCHANGED << color, pc, loopIter >>

RespondToQuery ==
    /\ \E m \in msgs :
         /\ m.mtype = "query"
         /\ \E col \in (0..1) : color' = [color EXCEPT ![CHOOSE n \in Hosts : <n, m.dest, m.src> \in HostMapping] = col]
         /\ msgs' = (msgs \ {m}) \union
              {[mtype |-> "queryReply", dest |-> m.src, src |-> m.dest, body |-> color[CHOOSE n \in Hosts : <n, m.dest, m.src> \in HostMapping]]}
    /\ UNCHANGED << pc, sample, loopIter >>

TallyReplies ==
    /\ \E p \in SlushLoopProcess :
         /\ sample[p] # {}
         /\ \A q \in sample[p] : \E m \in msgs : m.mtype = "queryReply" /\ m.dest = p /\ m.src = q
         /\ LET replies == { m.body : m \in msgs /\ m.mtype = "queryReply" /\ m.dest = p /\ m.src \in sample[p] } IN
              IF \E c \in (0..1) : Cardinality({ x \in replies : x = c }) >= PickFlipThreshold
                 THEN color' = [color EXCEPT ![CHOOSE n \in Hosts : <n, p, CHOOSE q \in sample[p] : TRUE> \in HostMapping]
                                    = CHOOSE c \in (0..1) : Cardinality({ x \in replies : x = c }) >= PickFlipThreshold]
                 ELSE color' = color
         /\ sample' = [sample EXCEPT ![p] = {}]
         /\ loopIter' = [loopIter EXCEPT ![p] = @ + 1]
         /\ msgs' = { m \in msgs : ~(m.mtype = "queryReply" /\ m.dest = p /\ m.src \in sample[p]) }
    /\ UNCHANGED pc

LoopTerminate ==
    /\ \E p \in SlushLoopProcess :
         /\ loopIter[p] >= SlushIterationCount
         /\ msgs' = msgs \union {[mtype |-> "terminate", dest |-> p, src |-> NoMessage, body |-> NoColor]}
    /\ UNCHANGED << color, pc, sample, loopIter >>

QueryLoopExit ==
    /\ \A q \in SlushQueryProcess :
         pc[q] = "replyLoop" => \A m \in msgs : ~(m.dest = q /\ m.mtype \in {"query", "queryReply"})
    /\ pc' = [q \in SlushQueryProcess |-> "done"]
    /\ UNCHANGED << color, msgs, sample, loopIter >>

Next ==
    \/ ClientAssignColor \/ RequireColor \/ QuerySampleSet
    \/ RespondToQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
    /\ SF_vars(RequireColor) /\ SF_vars(QuerySampleSet) /\ SF_vars(RespondToQuery)
    /\ SF_vars(TallyReplies) /\ SF_vars(LoopTerminate) /\ SF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == \A p \in SlushLoopProcess \union SlushQueryProcess : <>(pc[p] = "done")

====