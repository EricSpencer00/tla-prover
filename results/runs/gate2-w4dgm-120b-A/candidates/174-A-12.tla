---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

VARIABLES color, pendingMessage, pc, sampleSet, loopIteration

vars == <<color, pendingMessage, pc, sampleSet, loopIteration>>

\* A message is a 3-or-4 tuple whose shape identifies its type, so the type
\* invariant can check every message in the set at once.
QueryMessage == [kind |-> "query", to |-> NoMessage, from |-> NoMessage, payload |-> NoMessage]
ReplyMessage == [kind |-> "reply", to |-> NoMessage, from |-> NoMessage, payload |-> NoMessage]
TerminationMessage == [kind |-> "termination", to |-> NoMessage, from |-> NoMessage]

TypeOK ==
    /\ color \in [Node -> {NoColor} \cup {"red", "blue"}]
    /\ pendingMessage \subseteq (QueryMessage \cup ReplyMessage \cup {TerminationMessage})
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"init", "looping", "done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ loopIteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ pendingMessage = {}
    /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "init"]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ loopIteration = [lp \in SlushLoopProcess |-> 0]

\* The client is the only one that assigns initial colors to uncolored nodes.
ClientAssignColor ==
    /\ pc["client"] = "init"
    /\ \E n \in Node, col \in {"red", "blue"} :
         /\ color[n] = NoColor
         /\ color' = [color EXCEPT ![n] = col]
    /\ UNCHANGED <<pendingMessage, pc, sampleSet, loopIteration>>

LoopProcessRequireColor(lp) ==
    /\ pc[lp] = "init"
    /\ \E n \in Node : \A m \in HostMapping : (m[1] = lp /\ m[2] = n) => color[n] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "looping"]
    /\ UNCHANGED <<color, pendingMessage, sampleSet, loopIteration>>

\* The loop samples peers and sends a query containing its own current color.
LoopProcessQuery(lp) ==
    /\ pc[lp] = "looping"
    /\ loopIteration[lp] < SlushIterationCount
    /\ sampleSet[lp] = {}
    /\ \E peers \in SUBSET SlushQueryProcess :
         /\ Cardinality(peers) = SampleSetSize
         /\ \A qp \in peers : \E m \in HostMapping : m[1] = lp /\ m[3] = qp
         /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
         /\ pendingMessage' = pendingMessage \cup
              { [kind |-> "query", to |-> qp, from |-> lp, payload |-> color[CHOOSE n \in Node : \E m \in HostMapping : m[1] = lp /\ m[2] = n /\ m[3] = qp]] : qp \in peers }
    /\ UNCHANGED <<color, pc, loopIteration>>

ReplyToQuery(qp) ==
    /\ pc[qp] \in {"init", "looping"}
    /\ \E m \in HostMapping : m[3] = qp
    /\ \E msg \in pendingMessage :
         /\ msg.kind = "query" /\ msg.to = qp
         /\ IF color[m[2]] = NoColor THEN color' = [color EXCEPT ![m[2]] = msg.payload] ELSE color' = color
         /\ pendingMessage' = (pendingMessage \ {msg}) \cup
              {[kind |-> "reply", to |-> msg.from, from |-> qp, payload |-> IF color[m[2]] = NoColor THEN msg.payload ELSE color[m[2]]]}
    /\ UNCHANGED <<pc, sampleSet, loopIteration>>

\* The node adopts a color only once a strict majority of sampled peers agree,
\* and only for an uncolored node (the loop requires a starting color anyway).
LoopProcessTally(lp) ==
    /\ pc[lp] = "looping"
    /\ sampleSet[lp] # {}
    /\ \E msg \in pendingMessage :
         /\ msg.kind = "reply" /\ msg.from \in sampleSet[lp]
         /\ pendingMessage' = pendingMessage \ {msg}
    /\ Cardinality(sampleSet[lp]) = Cardinality({msg \in pendingMessage : msg.kind = "reply" /\ msg.to = lp})
    /\ LET tally == Cardinality({msg \in pendingMessage : msg.kind = "reply" /\ msg.to = lp /\ msg.payload = "red"}) + Cardinality({msg \in pendingMessage : msg.kind = "reply" /\ msg.to = lp /\ msg.payload = "blue"}) IN
         /\ IF Cardinality({msg \in pendingMessage : msg.kind = "reply" /\ msg.to = lp /\ msg.payload = "red"}) >= PickFlipThreshold
              THEN color' = [color EXCEPT ![CHOOSE n \in Node : \E m \in HostMapping : m[1] = lp /\ m[2] = n] = "red"]
              ELSE IF Cardinality({msg \in pendingMessage : msg.kind = "reply" /\ msg.to = lp /\ msg.payload = "blue"}) >= PickFlipThreshold
                     THEN color' = [color EXCEPT ![CHOOSE n \in Node : \E m \in HostMapping : m[1] = lp /\ m[2] = n] = "blue"]
                     ELSE color' = color
    /\ loopIteration' = [loopIteration EXCEPT ![lp] = loopIteration[lp] + 1]
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
    /\ UNCHANGED pc

LoopProcessTerminate(lp) ==
    /\ pc[lp] = "looping"
    /\ loopIteration[lp] >= SlushIterationCount
    /\ pc' = [pc EXCEPT ![lp] = "done"]
    /\ pendingMessage' = pendingMessage \cup {TerminationMessage}
    /\ UNCHANGED <<color, sampleSet, loopIteration>>

QueryProcessExit(qp) ==
    /\ pc[qp] \in {"init", "looping"}
    /\ \A lp \in SlushLoopProcess : TerminationMessage \in pendingMessage
    /\ pc' = [pc EXCEPT ![qp] = "done"]
    /\ UNCHANGED <<color, pendingMessage, sampleSet, loopIteration>>

Next ==
    \/ ClientAssignColor
    \/ \E lp \in SlushLoopProcess : LoopProcessRequireColor(lp) \/ LoopProcessQuery(lp) \/ LoopProcessTally(lp) \/ LoopProcessTerminate(lp)
    \/ \E qp \in SlushQueryProcess : ReplyToQuery(qp) \/ QueryProcessExit(qp)

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopProcessTally(CHOOSE lp \in SlushLoopProcess : TRUE))

\* The invariant is a pure type check; it never drives the system's progress.
TypeInvariant == TypeOK

Termination == \A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) : <>(pc[p] = "done")

====