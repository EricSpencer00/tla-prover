---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Slush is the simplest member of the Snow family of probabilistic consensus
   protocols.  It is metastable: a node repeatedly polls a random peer sample
   and adopts a sufficiently popular color, causing the network to converge
   on one color.  TLA+ cannot model the random sampling itself, so this
   specification serves as executable pseudocode for the protocol.  It tracks
   node colors, in-flight messages, process program counters, sampled peers,
   and iteration counters.  The only property it can verify is a type
   invariant over the shared state; convergence to a single color is a
   probabilistic guarantee outside TLA+'s expressiveness. *)

CONSTANTS
  Node,               \* set of nodes in the network
  SlushLoopProcess,   \* set of loop processes, one per node
  SlushQueryProcess,  \* set of query processes, one per node
  HostMapping,        \* HostMapping == { <<n, lp, qp>> : n \in Node }
  SlushIterationCount,\* number of iteration rounds per loop process
  SampleSetSize,      \* size of the random peer sample a loop process queries
  PickFlipThreshold,  \* votes required for a loop process to flip its node's color
  NoColor,            \* sentinel meaning "no color assigned"
  NoMessage           \* sentinel meaning "no message in flight"

\* Persistent message types; always present even when the message set is empty
QueryMessage == [kind: "query", from: SlushLoopProcess, to: SlushQueryProcess, color: NoColor \cup (Node \X {"c1", "c2"})]
ReplyMessage == [kind: "reply", from: SlushQueryProcess, to: SlushLoopProcess, color: NoColor \cup (Node \X {"c1", "c2"})]
TerminateMessage == [kind: "terminate", from: SlushLoopProcess]

ColorDomain == (Node \X {"c1", "c2"}) \cup {NoColor}

VARIABLES nodeColor, messages, pcp, sampleSet, loopsDone

vars == <<nodeColor, messages, pcp, sampleSet, loopsDone>>

TypeInvariant ==
  /\ nodeColor \in [Node -> ColorDomain]
  /\ messages \subseteq (QueryMessage \cup ReplyMessage \cup TerminateMessage \cup {NoMessage})
  /\ pcp \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"idle", "waiting", "querying", "tallying", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopsDone \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pcp = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "idle"]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ loopsDone = [lp \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node (an external
\* transaction arriving at the network).
ClientAssignColor ==
  /\ pcp["client"] = "idle"
  /\ pcp' = [pcp EXCEPT !["client"] = "waiting"]
  /\ \E n \in Node, col \in {"c1", "c2"} :
       /\ nodeColor[n] = NoColor
       /\ nodeColor' = [nodeColor EXCEPT ![n] = <<n, col>>]
  /\ UNCHANGED <<messages, sampleSet, loopsDone>>

RequireColor(lp) ==
  /\ pcp[lp] = "idle"
  /\ \E n \in Node : <<n, lp, CHOOSE qp \in SlushQueryProcess : TRUE>> \in HostMapping
  /\ nodeColor[n] # NoColor
  /\ pcp' = [pcp EXCEPT ![lp] = "waiting"]
  /\ UNCHANGED <<nodeColor, messages, sampleSet, loopsDone>>

QuerySampleSet(lp) ==
  /\ pcp[lp] = "waiting"
  /\ loopsDone[lp] < SlushIterationCount
  /\ \E peers \in SUBSET SlushQueryProcess :
       /\ Cardinality(peers) = SampleSetSize
       /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
  /\ messages' = messages \union
       {[kind |-> "query", from |-> lp, to |-> qp, color |-> nodeColor[n] :
           /\ <<n, lp, qp>> \in HostMapping
           /\ pcp[lp] = "waiting"] : qp \in sampleSet[lp]}
  /\ pcp' = [pcp EXCEPT ![lp] = "querying"]
  /\ UNCHANGED <<nodeColor, loopsDone>>

RespondToQuery(qp) ==
  /\ pcp[qp] = "idle"
  /\ \E m \in messages :
       /\ m.kind = "query" /\ m.to = qp /\ m.from \in SlushLoopProcess
       /\ LET n == CHOOSE n \in Node : <<n, m.from, qp>> \in HostMapping IN
            /\ IF nodeColor[n] = NoColor
               THEN nodeColor' = [nodeColor EXCEPT ![n] = m.color]
               ELSE nodeColor' = nodeColor
            /\ messages' = (messages \ {m}) \union
                 {[kind |-> "reply", from |-> qp, to |-> m.from, color |-> nodeColor[n]]}
  /\ pcp' = [pcp EXCEPT ![qp] = "replying"]
  /\ UNCHANGED <<sampleSet, loopsDone>>

TallyReplies(lp) ==
  /\ pcp[lp] = "querying"
  /\ \A qp \in sampleSet[lp] : \E m \in messages : m.kind = "reply" /\ m.from = qp /\ m.to = lp
  /\ LET colorCounts ==
         [col \in {"c1", "c2"} |-> Cardinality({qp \in sampleSet[lp] :
           \E m \in messages : m.kind = "reply" /\ m.from = qp /\ m.to = lp /\ m.color = col})]
     n == CHOOSE n \in Node : <<n, lp, CHOOSE qp \in SlushQueryProcess : TRUE>> \in HostMapping
     col == CHOOSE c \in {"c1", "c2"} : colorCounts[c] >= PickFlipThreshold
     newColor == IF \E c \in {"c1", "c2"} : colorCounts[c] >= PickFlipThreshold
                   THEN <<n, col>> ELSE nodeColor[n]
     msgs == {m \in messages : m.kind = "reply" /\ m.to = lp}
  IN /\ nodeColor' = [nodeColor EXCEPT ![n] = newColor]
     /\ messages' = (messages \ msgs)
     /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
     /\ loopsDone' = [loopsDone EXCEPT ![lp] = loopsDone[lp] + 1]
     /\ pcp' = [pcp EXCEPT ![lp] = "tallying"]

LoopTerminate(lp) ==
  /\ pcp[lp] = "tallying"
  /\ loopsDone[lp] = SlushIterationCount
  /\ messages' = messages \union {[kind |-> "terminate", from |-> lp]}
  /\ pcp' = [pcp EXCEPT ![lp] = "done"]
  /\ UNCHANGED <<nodeColor, sampleSet, loopsDone>>

QueryLoopExit(qp) ==
  /\ pcp[qp] \in {"idle", "replying"}
  /\ \A lp \in SlushLoopProcess : pcp[lp] = "done"
  /\ pcp' = [pcp EXCEPT ![qp] = "done"]
  /\ UNCHANGED <<nodeColor, messages, sampleSet, loopsDone>>

Next ==
  \/ ClientAssignColor
  \/ \E lp \in SlushLoopProcess : RequireColor(lp) \/ QuerySampleSet(lp) \/ TallyReplies(lp) \/ LoopTerminate(lp)
  \/ \E qp \in SlushQueryProcess : RespondToQuery(qp) \/ QueryLoopExit(qp)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ClientAssignColor)
        /\ \A lp \in SlushLoopProcess : SF_vars(RequireColor(lp)) /\ SF_vars(QuerySampleSet(lp))
                                          /\ SF_vars(TallyReplies(lp)) /\ SF_vars(LoopTerminate(lp))
        /\ \A qp \in SlushQueryProcess : WF_vars(RespondToQuery(qp)) /\ WF_vars(QueryLoopExit(qp))

AllProcessesDone == \A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) : pcp[p] = "done"

Termination == TypeInvariant /\ AllProcessesDone

====