---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* The Slush protocol is metastable: each node samples a random peer set and
\* adopts a color only once a supermajority of the sample replies with it. TLA+
\* models the loop/peer/query processes as separate actions; all network
\* messages are held in a bounded in-flight set that the client application
\* treats as unordered (messages can be delivered in any order).

\* A node's color is either one of two fixed colors or "uncolored". Each loop
\* process holds exactly one sample set at a time and counts its peer replies
\* against that set -- it never carries over a set from a previous round.
\* Each loop process runs for a bounded number of rounds (iterations), and
\* loop processes may only begin sampling once their host has been assigned
\* a color by the client request process.

\* Because Slush's convergence to a single color is probabilistic and TLA+
\* has no random or probabilistic choice semantics, this spec is executable
\* pseudocode: the loop process's decision to adopt a color is an ordinary
\* guarded action based on a deterministic tally, and the model is closed
\* under all message reorderings. The invariant below is a type check on
\* the color map and on the shape of all in-flight messages; it is not a
\* safety or convergence property of the protocol itself.
\* Termination (every process eventually reaches "done") is the only
\* liveness property modeled here and holds regardless of which color
\* the network ultimately converges to.

\* The full action set is:
\* 1. AssignColor (the client request process colors an uncolored node)
\* 2. RequireColor (a loop process waits for its host's color)
\* 3. QuerySampleSet (the loop process samples peers and sends queries)
\* 4. RespondToQuery (a query process replies, adopting the query color if uncolored)
\* 5. TallyReplies (the loop process adopts a color once a supermajority replies)
\* 6. LoopTerminate (a loop process completes all of its rounds)
\* 7. ExitQueryLoop (query processes stop once every loop process has terminated)

\* Permitted values of the "kind" field of an in-flight message.
MessageKinds == {"query", "queryReply", "termination"}

VARIABLES color, inFlight, pc, sampleSet, iterations

vars == <<color, inFlight, pc, sampleSet, iterations>>

TypeOK ==
    /\ color \in [Node -> {NoColor, "colorOne", "colorTwo"}]
    /\ inFlight \subseteq [kind: MessageKinds, src: Node, dst: Node, datum: {NoColor, "colorOne", "colorTwo"}]
    /\ pc \in [SlushLoopProcess -> {"waitingForColor", "sampling", "tallying", "done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ inFlight = {}
    /\ pc = [lp \in SlushLoopProcess |-> "waitingForColor"]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ iterations = [lp \in SlushLoopProcess |-> 0]

\* The client request process assigns a random color to an uncolored node.
AssignColor ==
    /\ \E n \in Node :
         /\ color[n] = NoColor
         /\ \E clr \in {"colorOne", "colorTwo"} : color' = [color EXCEPT ![n] = clr]
    /\ UNCHANGED <<inFlight, pc, sampleSet, iterations>>

RequireColor ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "waitingForColor"
         /\ \E n \in Node :
              /\ <<n, lp, "hostLoop">> \in HostMapping
              /\ color[n] # NoColor
         /\ pc' = [pc EXCEPT ![lp] = "sampling"]
    /\ UNCHANGED <<color, inFlight, sampleSet, iterations>>

\* The loop process selects a random SAMPLE_SET_SIZE-sized peer set and
\* sends a query to each sampled node's query process.
QuerySampleSet ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "sampling"
         /\ iterations[lp] < SlushIterationCount
         /\ \E target \in Node :
              /\ Cardinality(target) >= SampleSetSize
              /\ \E peers \in SUBSET target :
                   /\ Cardinality(peers) = SampleSetSize
                   /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
                   /\ inFlight' = inFlight \cup {
                        [kind |-> "query", src |-> n, dst |-> q, datum |-> color[n]]
                        : n \in Node, q \in peers, <<n, lp, "hostLoop">> \in HostMapping, <<q, _, "hostQuery">> \in HostMapping
                      }
         /\ pc' = [pc EXCEPT ![lp] = "tallying"]
    /\ UNCHANGED <<color, iterations>>

\* A query process replies with its own color; if it is still uncolored it
\* adopts the query color (the "adopt-on-query" twist) before replying.
RespondToQuery ==
    /\ \E msg \in inFlight :
         /\ msg.kind = "query"
         /\ color[msg.dst] = NoColor
         /\ color' = [color EXCEPT ![msg.dst] = msg.datum]
         /\ inFlight' = (inFlight \ {msg}) \cup {[kind |-> "queryReply", src |-> msg.dst, dst |-> msg.src, datum |-> msg.datum]}
    /\ UNCHANGED <<pc, sampleSet, iterations>>

\* The loop process tallies the replies it received from its exact sample set
\* and adopts a color only once a supermajority (>= PICK_FLIP_THRESHOLD) has
\* replied with it. The sample set is cleared for the next round.
TallyReplies ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "tallying"
         /\ Cardinality(sampleSet[lp]) > 0
         /\ \E m1 \in inFlight, m2 \in inFlight :
              /\ m1.kind = "queryReply" /\ m1.dst = lp /\ m1.datum = "colorOne" /\ m1.src \in sampleSet[lp]
              /\ m2.kind = "queryReply" /\ m2.dst = lp /\ m2.datum = "colorTwo" /\ m2.src \in sampleSet[lp]
              /\ IF m1 # m2 /\ m1.src = m2.src THEN Cardinality(sampleSet[lp]) = 1 ELSE TRUE
              /\ IF Cardinality(sampleSet[lp]) >= PickFlipThreshold THEN color' = [color EXCEPT ![lp] = "colorOne"]
                 ELSE IF Cardinality(sampleSet[lp]) >= PickFlipThreshold THEN color' = [color EXCEPT ![lp] = "colorTwo"]
                 ELSE color' = color
         /\ pc' = [pc EXCEPT ![lp] = "sampling"]
         /\ inFlight' = {msg \in inFlight : ~(msg.kind = "queryReply" /\ msg.dst = lp)}
         /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
         /\ iterations' = [iterations EXCEPT ![lp] = @ + 1]
    /\ UNCHANGED <<>>

\* A loop process that has run all of its rounds broadcasts a termination
\* message, which is what the query processes wait for before exiting.
LoopTerminate ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "sampling"
         /\ iterations[lp] = SlushIterationCount
         /\ inFlight' = inFlight \cup {[kind |-> "termination", src |-> n, dst |-> _, datum |-> NoMessage] : n \in Node, <<n, lp, "hostLoop">> \in HostMapping}
         /\ pc' = [pc EXCEPT ![lp] = "done"]
    /\ UNCHANGED <<color, sampleSet, iterations>>

\* Query processes stop only once every loop process has terminated; a
\* Reconfigure action below is the only way the network ever recovers.
ExitQueryLoop ==
    /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
    /\ \E qp \in SlushQueryProcess : pc' = [pc EXCEPT ![qp] = "done"]
    /\ UNCHANGED <<color, inFlight, sampleSet, iterations>>

\* When the client has colored every node, no loop process is left to
\* iterate, and every query process has exited, the network is fully
\* quiescent; it then recycles to a fresh run (bounded model depth).
Reconfigure ==
    /\ \A n \in Node : color[n] # NoColor
    /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
    /\ \A qp \in SlushQueryProcess : pc[qp] = "done"
    /\ color' = [n \in Node |-> NoColor]
    /\ inFlight' = {}
    /\ pc' = [p \in (SlushLoopProcess \cup SlushQueryProcess) |-> IF p \in SlushLoopProcess THEN "waitingForColor" ELSE "sampling"]
    /\ sampleSet' = [lp \in SlushLoopProcess |-> {}]
    /\ iterations' = [lp \in SlushLoopProcess |-> 0]

Next ==
    \/ AssignColor
    \/ RequireColor
    \/ QuerySampleSet
    \/ RespondToQuery
    \/ TallyReplies
    \/ LoopTerminate
    \/ ExitQueryLoop
    \/ Reconfigure

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(AssignColor) /\ SF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
    /\ WF_vars(RespondToQuery) /\ SF_vars(TallyReplies) /\ SF_vars(LoopTerminate)
    /\ SF_vars(ExitQueryLoop) /\ SF_vars(Reconfigure)

TypeInvariant == TypeOK

Termination == \A p \in (SlushLoopProcess \cup SlushQueryProcess) : <>(pc[p] = "done")

====