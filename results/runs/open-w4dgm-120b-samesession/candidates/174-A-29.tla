---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANT Node
CONSTANT SlushLoopProcess
CONSTANT SlushQueryProcess
CONSTANT HostMapping
CONSTANT SlushIterationCount
CONSTANT SampleSetSize
CONSTANT PickFlipThreshold
CONSTANT NoColor
CONSTANT NoMessage

\* A message is modeled as a tuple whose shape (tag) determines its kind; the
\* NoMessage sentinel marks the client-request channel when it is idle.
Message == [tag: {"query", "reply", "done"}, from: SlushQueryProcess \cup SlushLoopProcess,
            to: SlushQueryProcess \cup SlushLoopProcess, color: {NoColor} \cup Node]

VARIABLES color, inbox, pc, sample, iterations

vars == <<color, inbox, pc, sample, iterations>>

TypeOK ==
    /\ color \in [Node -> {NoColor} \cup Node]
    /\ inbox \subseteq Message
    /\ pc \in [SlushLoopProcess -> {"waitingColor", "sampled", "tallying", "done"}]
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ inbox = {}
    /\ pc = [p \in SlushLoopProcess |-> "waitingColor"]
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iterations = [p \in SlushLoopProcess |-> 0]

\* Client assigns an initial color to an uncolored node (external request).
ClientAssignColor(c) ==
    /\ \E n \in Node : color[n] = NoColor /\ color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<inbox, pc, sample, iterations>>

RequireColor(p) ==
    /\ pc[p] = "waitingColor"
    /\ LET n == (CHOOSE e \in HostMapping : e[2] = p)[1] IN
        /\ color[n] # NoColor
        /\ pc' = [pc EXCEPT ![p] = "sampled"]
    /\ UNCHANGED <<color, inbox, sample, iterations>>

QuerySampleSet(p) ==
    /\ pc[p] = "sampled"
    /\ Cardinality(sample[p]) < SampleSetSize
    /\ LET n == (CHOOSE e \in HostMapping : e[2] = p)[1] IN
        \E q \in SlushQueryProcess :
            /\ q \notin sample[p]
            /\ sample' = [sample EXCEPT ![p] = @ \cup {q}]
            /\ inbox' = inbox \cup {[tag |-> "query", from |-> p, to |-> q, color |-> color[n]]}
    /\ UNCHANGED <<color, pc, iterations>>

\* Responding to a query: a query process adopts the query's color if it is
\* still uncolored, then replies with whatever color it holds.
RespondToQuery(m) ==
    /\ m \in inbox
    /\ m.tag = "query"
    /\ LET n == (CHOOSE e \in HostMapping : e[3] = m.to)[1] IN
        color' = IF color[n] = NoColor THEN [color EXCEPT ![n] = m.color] ELSE color
    /\ inbox' = (inbox \ {m}) \cup {[tag |-> "reply", from |-> m.to, to |-> m.from, color |-> color[(CHOOSE e \in HostMapping : e[1] = n)[1]]]}
    /\ UNCHANGED <<pc, sample, iterations>>

TallyReplies(p) ==
    /\ pc[p] = "sampled"
    /\ Cardinality(sample[p]) >= SampleSetSize
    /\ \A q \in sample[p] : \E m \in inbox : m.tag = "reply" /\ m.from = q /\ m.to = p
    /\ LET count(color) ==
            Cardinality({q \in sample[p] : \E m \in inbox : m.tag = "reply" /\ m.from = q /\ m.to = p /\ m.color = color})
         n == (CHOOSE e \in HostMapping : e[2] = p)[1] IN
        /\ IF count(color[n]) >= PickFlipThreshold
            THEN color' = [color EXCEPT ![n] = color[n]]
            ELSE color' = IF \E q \in sample[p] : count(color[q]) >= PickFlipThreshold
                            THEN color
                            ELSE color
    /\ inbox' = {m \in inbox : ~(m.tag = "reply" /\ m.to = p)}
    /\ sample' = [sample EXCEPT ![p] = {}]
    /\ iterations' = [iterations EXCEPT ![p] = IF iterations[p] < SlushIterationCount THEN @ + 1 ELSE @]
    /\ IF iterations[p] >= SlushIterationCount
        THEN pc' = [pc EXCEPT ![p] = "done"]
        ELSE pc' = [pc EXCEPT ![p] = "sampled"]

LoopTermination(p) ==
    /\ pc[p] = "done"
    /\ inbox' = inbox \cup {[tag |-> "done", from |-> p, to |-> NoMessage, color |-> NoColor]}
    /\ UNCHANGED <<color, pc, sample, iterations>>

QueryLoopExit ==
    \E q \in SlushQueryProcess :
        /\ pc[q] = "waitingColor"
        /\ \A p \in SlushLoopProcess : [tag |-> "done", from |-> p, to |-> NoMessage, color |-> NoColor] \in inbox
        /\ pc' = [pc EXCEPT ![q] = "done"]
        /\ UNCHANGED <<color, inbox, sample, iterations>>

Next ==
    \/ \E c \in Node : ClientAssignColor(c)
    \/ \E p \in SlushLoopProcess : RequireColor(p) \/ QuerySampleSet(p) \/ TallyReplies(p) \/ LoopTermination(p)
    \/ \E m \in inbox : RespondToQuery(m)
    \/ QueryLoopExit

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(QueryLoopExit)

TypeInvariant ==
    /\ color \in [Node -> {NoColor} \cup Node]
    /\ inbox \subseteq Message
    /\ \A m \in inbox : (m.tag = "done" => m.to = NoMessage /\ m.from \in SlushLoopProcess)
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"waitingColor", "sampled", "tallying", "done"}]

Termination == \A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = "done"

====