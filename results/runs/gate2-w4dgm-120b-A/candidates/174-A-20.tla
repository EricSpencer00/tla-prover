---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

\* hostOf is the node a given process is attached to; each node has both a
\* loop process and a query process, and the node sends queries directly to
\* its peers' query processes (the fully-connected mesh).
HostOf(p) == CHOOSE d \in Node : <<d, p>> \in HostMapping

\* Two distinct color choices; the action space is kept minimal and the
\* convergence argument (outside the scope of this spec) is per color.
Colors == {1, 2}

\* TLA+ lacks randomness, so the queries are sent to a non-deterministic
\* sample set rather than a random one; that difference is exactly what
\* keeps this a reachable-state spec instead of a probabilistic model.
\* Messages are tuples so they can be compared set-membership style.
VARIABLES assignment, messages, pc, sampleSet, iterations

vars == <<assignment, messages, pc, sampleSet, iterations>>

TypeOK ==
    /\ assignment \in [Node -> (Colors \cup {NoColor})]
    /\ messages \subseteq [kind: {NoMessage, "query", "queryReply", "loopDone"},
                           to: (SlushLoopProcess \cup SlushQueryProcess \cup {NoMessage}),
                           from: (SlushLoopProcess \cup SlushQueryProcess),
                           color: (Colors \cup {NoColor})]
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"init", "done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ assignment = [n \in Node |-> NoColor]
    /\ messages = {}
    /\ pc = [q \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "init"]
    /\ sampleSet = [l \in SlushLoopProcess |-> {}]
    /\ iterations = [l \in SlushLoopProcess |-> 0]

\* The client can reassign uncolored nodes at any time, which is how the
\* network begins; a loop process cannot start iterating until its host
\* node has a color at all, which is what makes the sampling step safe.
AssignRandomColor(n) ==
    /\ assignment[n] = NoColor
    /\ \E c \in Colors : assignment' = [assignment EXCEPT ![n] = c]
    /\ UNCHANGED <<messages, pc, sampleSet, iterations>>

RequireColor(l) ==
    /\ assignment[HostOf(l)] # NoColor
    /\ pc[l] = "init"
    /\ pc' = [pc EXCEPT ![l] = "waiting"]
    /\ UNCHANGED <<assignment, messages, sampleSet, iterations>>

QuerySample(l) ==
    /\ pc[l] = "waiting"
    /\ iterations[l] < SlushIterationCount
    /\ sampleSet' = [sampleSet EXCEPT ![l] = {q \in SlushQueryProcess : q # HostOf(l)}]
    /\ \E msgs \in SUBSET [kind: {"query"}, to: SlushQueryProcess,
                           from: SlushLoopProcess, color: Colors] :
        /\ \A m \in msgs : m.from = l
        /\ messages' = messages \cup msgs
    /\ pc' = [pc EXCEPT ![l] = "collecting"]
    /\ UNCHANGED <<assignment, iterations>>

\* A query is answered by whatever color the node currently holds; a node
\* that is still uncolored adopts the in-flight query's color instead.
RespondToQuery(q) ==
    /\ \E m \in messages :
        /\ m.kind = "query" /\ m.to = q
        /\ LET c == IF assignment[HostOf(q)] = NoColor THEN m.color ELSE assignment[HostOf(q)] IN
            /\ assignment' = [assignment EXCEPT ![HostOf(q)] = c]
            /\ messages' = (messages \ {m}) \cup
                 {[kind |-> "queryReply", to |-> m.from, from |-> q, color |-> c]}
    /\ UNCHANGED <<pc, sampleSet, iterations>>

TallyReplies(l) ==
    /\ pc[l] = "collecting"
    /\ \A peer \in sampleSet[l] : \E m \in messages : m.kind = "queryReply" /\ m.from = peer /\ m.to = l
    /\ LET
        countColor(c) == Cardinality({peer \in sampleSet[l] :
                                     \E m \in messages : m.kind = "queryReply" /\ m.from = peer /\ m.to = l /\ m.color = c})
        newColor == CHOOSE c \in Colors : countColor(c) >= PickFlipThreshold
        in
        /\ assignment' = [assignment EXCEPT ![HostOf(l)] = newColor]
        /\ messages' = {m \in messages : ~(m.kind = "queryReply" /\ m.to = l)}
    /\ pc' = [pc EXCEPT ![l] = "iterating"]
    /\ sampleSet' = [sampleSet EXCEPT ![l] = {}]
    /\ iterations' = [iterations EXCEPT ![l] = @ + 1]

LoopTermination(l) ==
    /\ pc[l] \in {"collecting", "iterating"}
    /\ iterations[l] = SlushIterationCount
    /\ pc' = [pc EXCEPT ![l] = "done"]
    /\ messages' = messages \cup {[kind |-> "loopDone", to |-> NoMessage, from |-> l, color |-> NoColor]}
    /\ UNCHANGED <<assignment, sampleSet, iterations>>

QueryLoopExit ==
    /\ \A q \in SlushQueryProcess : pc[q] = "init"
    /\ \A l \in SlushLoopProcess : pc[l] = "done"
    /\ \A q \in SlushQueryProcess :
        pc' = [pc EXCEPT ![q] = "done"]
    /\ UNCHANGED <<assignment, messages, sampleSet, iterations>>

Next ==
    \/ \E n \in Node : AssignRandomColor(n)
    \/ \E l \in SlushLoopProcess : RequireColor(l)
    \/ \E l \in SlushLoopProcess : QuerySample(l)
    \/ \E q \in SlushQueryProcess : RespondToQuery(q)
    \/ \E l \in SlushLoopProcess : TallyReplies(l)
    \/ \E l \in SlushLoopProcess : LoopTermination(l)
    \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ \A l \in SlushLoopProcess : WF_vars(LoopTermination(l))
        /\ \A q \in SlushQueryProcess : WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

\* Every process in the mesh eventually reaches its final state, which is
\* what keeps the reachable state space bounded for TLC; convergence to
\* a single color (the property the original Snow protocols guarantee)
\* is not expressible in TLA+ and is therefore omitted by design.
Termination == <>(\A l \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) : pc[l] = "done")
====