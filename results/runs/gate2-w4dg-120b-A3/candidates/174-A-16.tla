---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

ASSUME /\ HostMapping \in [SlushLoopProcess -> [proc : SlushQueryProcess, node : Node]]
         /\ Cardinality(SlushLoopProcess) = Cardinality(Node)
         /\ Cardinality(SlushQueryProcess) = Cardinality(Node)

\* The protocol's messages.  A query carries the loop's current color so
\* the queried node may adopt it if it is still uncolored.  The reply
\* carries the respondent's current color, which the loop tallies.
Message ==
  [kind : {"query", "reply", "term"},
   sender : Node, target : Node, payload : {NoMessage} \cup {NoColor, "c1", "c2"}]

VARIABLES color, msgq, pc, sample, iters
vars == <<color, msgq, pc, sample, iters>>

TypeOK ==
  /\ color \in [Node -> {NoColor, "c1", "c2"}]
  /\ msgq \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"idle","waitColor","querying","tallying","quitting","done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgq = {}
  /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "idle"]
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ iters = [lp \in SlushLoopProcess |-> 0]

\* Client assigns a random initial color to an uncolored node.  Repeats until
\* every node is colored; this is the only source of colors in the system.
AssignColor ==
  /\ pc["client"] = "idle"
  /\ \E n \in Node, c \in {"c1", "c2"} :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
       /\ pc' = [pc EXCEPT !["client"] = "done"]
  /\ UNCHANGED <<msgq, sample, iters>>

RequireColor ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "idle"
       /\ color[HostMapping[lp].node] # NoColor
       /\ pc' = [pc EXCEPT ![lp] = "querying"]
       /\ UNCHANGED <<color, msgq, sample, iters>>

QuerySampleSet ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "querying"
       /\ iters[lp] < SlushIterationCount
       /\ \E s \in (SUBSET (Node \ {HostMapping[lp].node})) :
            /\ Cardinality(s) = SampleSetSize
            /\ sample' = [sample EXCEPT ![lp] = s]
       /\ msgq' = msgq \union {
            [kind |-> "query", sender |-> HostMapping[lp].node,
              target |-> n, payload |-> color[HostMapping[lp].node]] : n \in sample[lp]}
       /\ pc' = [pc EXCEPT ![lp] = "tallying"]
  /\ UNCHANGED <<color, iters>>

RespondToQuery ==
  /\ \E qp \in SlushQueryProcess :
       /\ pc[qp] = "idle"
       /\ \E m \in msgq :
            /\ m.kind = "query"
            /\ m.target = HostMapping[qp].node
            /\ (color[HostMapping[qp].node] = NoColor => color' = [color EXCEPT ![HostMapping[qp].node] = m.payload])
            /\ msgq' = (msgq \ {m}) \union {[kind |-> "reply", sender |-> m.target,
                                            target |-> m.sender, payload |-> color[HostMapping[qp].node]]}
       /\ pc' = [pc EXCEPT ![qp] = "replying"]
  /\ UNCHANGED <<sample, iters>>

TallyReplies ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "tallying"
       /\ \A n \in sample[lp] : [kind |-> "reply", sender |-> n, target |-> HostMapping[lp].node, payload |-> color[n]] \in msgq
       /\ LET tallied == [c \in {"c1", "c2"} |-> Cardinality({n \in sample[lp] : color[n] = c})] IN
            /\ IF tallied["c1"] >= PickFlipThreshold
               THEN color' = [color EXCEPT ![HostMapping[lp].node] = "c1"]
               ELSE IF tallied["c2"] >= PickFlipThreshold
                    THEN color' = [color EXCEPT ![HostMapping[lp].node] = "c2"]
                    ELSE color' = color
            /\ msgq' = msgq \ {m \in msgq : m.kind = "reply" /\ m.target = HostMapping[lp].node}
            /\ sample' = [sample EXCEPT ![lp] = {}]
            /\ iters' = [iters EXCEPT ![lp] = IF iters[lp] < SlushIterationCount THEN iters[lp] + 1 ELSE iters[lp]]
            /\ pc' = [pc EXCEPT ![lp] = "querying"]
  /\ UNCHANGED <<>>

LoopQuits ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "querying"
       /\ iters[lp] >= SlushIterationCount
       /\ msgq' = msgq \union {[kind |-> "term", sender |-> HostMapping[lp].node, target |-> NoMessage, payload |-> NoMessage]}
       /\ pc' = [pc EXCEPT ![lp] = "quitting"]
  /\ UNCHANGED <<color, sample, iters>>

QueryLoopExit ==
  /\ \E qp \in SlushQueryProcess :
       /\ pc[qp] = "replying"
       /\ \A lp \in SlushLoopProcess : pc[lp] = "quitting"
       /\ pc' = [pc EXCEPT ![qp] = "done"]
  /\ UNCHANGED <<color, msgq, sample, iters>>

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopQuits \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
         /\ SF_vars(AssignColor) /\ SF_vars(RequireColor)
         /\ SF_vars(TallyReplies) /\ SF_vars(QueryLoopExit)

\* All processes eventually settle, which is the strongest termination claim
\* TLA+ can make about this protocol; convergence to one color is
\* probabilistic and deliberately left out of the model.
AllDone ==
  /\ pc["client"] = "done"
  /\ \A lp \in SlushLoopProcess : pc[lp] = "quitting"
  /\ \A qp \in SlushQueryProcess : pc[qp] = "done"

====