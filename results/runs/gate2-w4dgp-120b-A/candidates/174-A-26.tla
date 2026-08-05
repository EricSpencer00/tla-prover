---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush is a metastable consensus protocol from the Avalanche family. Nodes
\* repeatedly sample random peers and adopt a sufficiently popular color.
\* This PlusCal model expresses the deterministic control flow; the
\* probabilistic convergence guarantee (that a single color wins with high
\* probability) is a statistical property and is therefore captured as a
\* comment, not a formal TLA+ invariant. The model is parameterised over the
\* number of nodes, the number of loop iterations, the sample size, and the
\* flip threshold, and it tracks process program counters rather than
\* halting on a single final state.

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Messages: queries from a loop process to sampled peers, replies back,
\* and termination notifications once a loop process completes all its rounds.
Message == [from : SlushLoopProcess, to : SlushQueryProcess, typ : {"query", "queryReply", "termination"}, col : {NoColor} \union Node]
QueryMessage == [from : SlushLoopProcess, to : SlushQueryProcess, typ : {"query"}, col : Node]
QueryReplyMessage == [from : SlushQueryProcess, to : SlushLoopProcess, typ : {"queryReply"}, col : Node]
TerminationMessage == [from : SlushLoopProcess, to : SlushLoopProcess, typ : {"termination"}, col : NoColor]

VARIABLES color, messages, loopPC, queryPC, sampleSet, loopIter

vars == <<color, messages, loopPC, queryPC, sampleSet, loopIter>>

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ loopPC = [lp \in SlushLoopProcess |-> "waitForColor"]
  /\ queryPC = [qp \in SlushQueryProcess |-> "replyLoop"]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ loopIter = [lp \in SlushLoopProcess |-> 0]

\* A client request assigns an initial color to an uncolored node.
ClientAssignColor(n) ==
  /\ color[n] = NoColor
  /\ color' = [color EXCEPT ![n] = n]
  /\ UNCHANGED <<messages, loopPC, queryPC, sampleSet, loopIter>>

RequireColor ==
  \E lp \in SlushLoopProcess :
    /\ loopPC[lp] = "waitForColor"
    /\ color[CHOOSE n \in Node : [lp, n, NoMessage] \in HostMapping]
    /\ loopPC' = [loopPC EXCEPT ![lp] = "sample"]
    /\ UNCHANGED <<color, messages, queryPC, sampleSet, loopIter>>

\* The loop process selects a random peer set and sends out a query message to
\* each sampled peer. The sample set is recomputed each round (the "replace"
\* discipline of Slush), so a peer appears in a sample only for a single round.
QuerySampleSet ==
  \E lp \in SlushLoopProcess :
    /\ loopPC[lp] = "sample"
    /\ loopIter[lp] < SlushIterationCount
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = {CHOOSE qp \in SlushQueryProcess : [lp, qp, NoMessage] \in HostMapping}]
    /\ messages' = messages \union { [from |-> lp, to |-> qp, typ |-> "query", col |-> color[CHOOSE n \in Node : [lp, n, NoMessage] \in HostMapping]] : qp \in sampleSet[lp] }
    /\ loopPC' = [loopPC EXCEPT ![lp] = "waitReplies"]
    /\ UNCHANGED <<color, queryPC, loopIter>>

\* A query process adopts the query color if it is still uncolored, then sends
\* back a reply carrying its current color. Every query is answered exactly once.
RespondToQuery ==
  \E m \in messages :
    /\ m.typ = "query"
    /\ queryPC[m.to] = "replyLoop"
    /\ color' = IF color[CHOOSE n \in Node : [m.to, n, NoMessage] \in HostMapping] = NoColor
                 THEN [color EXCEPT ![CHOOSE n \in Node : [m.to, n, NoMessage] \in HostMapping] = m.col]
                 ELSE color
    /\ messages' = (messages \ {m}) \union {[from |-> m.to, to |-> m.from, typ |-> "queryReply", col |-> color[CHOOSE n \in Node : [m.to, n, NoMessage] \in HostMapping]]}
    /\ UNCHANGED <<loopPC, queryPC, sampleSet, loopIter>>

\* The loop process tallies replies; a color that reaches the flip threshold
\* wins this round and is adopted by the node.
TallyReplies ==
  \E lp \in SlushLoopProcess :
    /\ loopPC[lp] = "waitReplies"
    /\ Cardinality({m \in messages : m.typ = "queryReply" /\ m.to = lp}) = Cardinality(sampleSet[lp])
    /\ LET replies == {m \in messages : m.typ = "queryReply" /\ m.to = lp} IN
         /\ color' = IF 2 * Cardinality({m \in replies : m.col = CHOOSE n \in Node : [lp, n, NoMessage] \in HostMapping}) >= PickFlipThreshold
                     THEN [color EXCEPT ![CHOOSE n \in Node : [lp, n, NoMessage] \in HostMapping] = CHOOSE n \in Node : [lp, n, NoMessage] \in HostMapping]
                     ELSE color
    /\ loopIter' = [loopIter EXCEPT ![lp] = @ + 1]
    /\ messages' = messages \ {m \in messages : m.typ = "queryReply" /\ m.to = lp}
    /\ loopPC' = [loopPC EXCEPT ![lp] = "sample"]
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
    /\ UNCHANGED <<queryPC>>

\* After completing all iterations the loop process broadcasts termination.
LoopTerminate ==
  \E lp \in SlushLoopProcess :
    /\ loopIter[lp] = SlushIterationCount
    /\ loopPC[lp] # "done"
    /\ loopPC' = [loopPC EXCEPT ![lp] = "done"]
    /\ messages' = messages \union {[from |-> lp, to |-> lp, typ |-> "termination", col |-> NoColor]}
    /\ UNCHANGED <<color, queryPC, sampleSet, loopIter>>

\* Query processes exit once every loop process has terminated.
QueryLoopExit ==
  \E qp \in SlushQueryProcess :
    /\ queryPC[qp] = "replyLoop"
    /\ \A lp \in SlushLoopProcess : loopPC[lp] = "done"
    /\ queryPC' = [queryPC EXCEPT ![qp] = "done"]
    /\ UNCHANGED <<color, messages, loopPC, sampleSet, loopIter>>

Next == \E n \in Node : ClientAssignColor(n) \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit
        \/ RequireColor

\* Slush's safety property is type-correctness of the shared color assignment.

TypeInvariant ==
  /\ color \in [Node -> {NoColor} \union Node]
  /\ messages \subseteq {m \in Message : m.typ = "query" \/ m.typ = "queryReply" \/ m.typ = "termination"}

Spec == Init /\ [][Next]_vars

\* Liveness: every process eventually reaches its done state (termination of
\* all loops and all query processes). Convergence to a single color is a
\* statistical property and is captured as a comment rather than a formal
\* TLA+ invariant, since TLA+ cannot express probabilistic guarantees.
Termination == <>(\A lp \in SlushLoopProcess : loopPC[lp] = "done" /\ (\A qp \in SlushQueryProcess : queryPC[qp] = "done"))

====