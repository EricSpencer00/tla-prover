---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush: a metastable voting protocol from the Avalanche whitepaper.  Each
\* node has a loop process that repeatedly samples random peers and adopts the
\* majority vote it observes.  Because TLA+ has no probabilistic semantics, the
\* module serves as executable pseudocode rather than a full stochastic model.
\* The invariant checks only that every message in flight is well-typed.

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

VARIABLES color, messages, pc, sample, loopIterations

vars == <<color, messages, pc, sample, loopIterations>>

MessageTypes == {NoMessage} \cup
    [msgType: {"query", "reply", "shutdown"},
     src: SlushLoopProcess \cup SlushQueryProcess,
     dst: SlushLoopProcess \cup SlushQueryProcess,
     payload: {NoColor} \cup Node]

TypeOK ==
    /\ color \in [Node -> {NoColor} \cup Node]
    /\ messages \subseteq MessageTypes
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> 0..2]
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ loopIterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ messages = {}
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> 0]
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ loopIterations = [p \in SlushLoopProcess |-> 0]

HostOf(p) == CHOOSE n \in Node : <<n, p>> \in HostMapping

\* The client process assigns an initial color to an uncolored node.
ClientAssignColor ==
    \E n \in Node :
        /\ color[n] = NoColor
        /\ \E c \in Node \ {n} : color' = [color EXCEPT ![n] = c]
        /\ UNCHANGED <<messages, pc, sample, loopIterations>>

RequireColor(p) ==
    /\ pc[p] = 0
    /\ color[HostOf(p)] # NoColor
    /\ pc' = [pc EXCEPT ![p] = 1]
    /\ UNCHANGED <<color, messages, sample, loopIterations>>

\* A loop process samples a random peer set and queries each peer's query
\* process for a reply carrying that peer's current opinion.
QuerySampleSet(p) ==
    \E sampleSet \in {s \in SUBSET Node : Cardinality(s) = SampleSetSize} :
        /\ pc[p] = 1
        /\ Cardinality(sampleSet) = SampleSetSize
        /\ sample' = [sample EXCEPT ![p] = sampleSet]
        /\ messages' = messages \cup
            {[msgType |-> "query", src |-> p, dst |-> q, payload |-> color[HostOf(p)]]
                 : q \in {qq \in SlushQueryProcess : HostOf(qq) \in sampleSet}}
        /\ pc' = [pc EXCEPT ![p] = 2]
        /\ UNCHANGED <<color, loopIterations>>

RespondToQuery(q) ==
    \E msg \in messages :
        /\ msg.msgType = "query"
        /\ msg.dst = q
        /\ color' = [color EXCEPT ![HostOf(q)] =
                        IF color[HostOf(q)] = NoColor THEN msg.payload ELSE @]
        /\ messages' = (messages \ {msg}) \cup
            {[msgType |-> "reply", src |-> q, dst |-> msg.src, payload |-> color[HostOf(q)]]}
        /\ UNCHANGED <<pc, sample, loopIterations>>

\* A loop process waits for replies from all of its sampled peers before
\* counting them and adopting the majority-aligned color, if any.
TallyReplies(p) ==
    /\ pc[p] = 2
    /\ \A n \in sample[p] : \E msg \in messages :
        /\ msg.msgType = "reply"
        /\ msg.dst = p
        /\ msg.src \in {qq \in SlushQueryProcess : HostOf(qq) = n}
    /\ \E c \in Node :
        /\ Cardinality({msg \in messages : msg.dst = p /\ msg.payload = c})
            >= PickFlipThreshold
        /\ color' = [color EXCEPT ![HostOf(p)] = c]
    /\ messages' = {msg \in messages :
                        ~(msg.dst = p /\ msg.msgType = "reply")}
    /\ sample' = [sample EXCEPT ![p] = {}]
    /\ loopIterations' = [loopIterations EXCEPT ![p] =
                            IF loopIterations[p] < SlushIterationCount
                                THEN @ + 1 ELSE @]
    /\ pc' = IF loopIterations[p] < SlushIterationCount
                THEN [pc EXCEPT ![p] = 1]
                ELSE [pc EXCEPT ![p] = 2]

LoopTermination(p) ==
    /\ pc[p] = 2
    /\ loopIterations[p] = SlushIterationCount
    /\ \A n \in sample[p] : \E msg \in messages :
        /\ msg.msgType = "reply"
        /\ msg.dst = p
        /\ msg.src \in {qq \in SlushQueryProcess : HostOf(qq) = n}
    /\ Cardinality(messages) < 2 * Cardinality(SlushLoopProcess \cup SlushQueryProcess)
    /\ messages' = messages \cup
        {[msgType |-> "shutdown", src |-> p, dst |-> NoMessage, payload |-> NoColor]}
    /\ pc' = [pc EXCEPT ![p] = 3]
    /\ UNCHANGED <<color, sample, loopIterations>>

QueryLoopExit(q) ==
    /\ pc[q] = 0
    /\ \A p \in SlushLoopProcess : pc[p] = 3
    /\ pc' = [pc EXCEPT ![q] = 3]
    /\ UNCHANGED <<color, messages, sample, loopIterations>>

Next ==
    \/ ClientAssignColor
    \/ \E p \in SlushLoopProcess : RequireColor(p) \/ QuerySampleSet(p)
                                    \/ TallyReplies(p) \/ LoopTermination(p)
    \/ \E q \in SlushQueryProcess : RespondToQuery(q) \/ QueryLoopExit(q)

Spec == Init /\ [][Next]_vars
    /\ (\A p \in SlushLoopProcess : WF_vars(RequireColor(p)))
    /\ (\A p \in SlushLoopProcess : WF_vars(QuerySampleSet(p)))
    /\ (\A q \in SlushQueryProcess : WF_vars(RespondToQuery(q)))
    /\ (\A p \in SlushLoopProcess : WF_vars(TallyReplies(p)))
    /\ (\A p \in SlushLoopProcess : WF_vars(LoopTermination(p)))

TypeInvariant == TypeOK

\* Every loop and query process eventually reaches its done state.
Termination == \A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = 3

====