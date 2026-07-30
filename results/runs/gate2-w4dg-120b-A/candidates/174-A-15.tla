---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

VARIABLES
    color, msgs, pc, sample, iteration

MsgTypes == {"SlushQuery", "SlushQueryReply", "SlushTermination"}

TypeOK ==
    /\ color \in [Node -> {NoColor} \cup {"color1", "color2"}]
    /\ msgs \subseteq [kind: MsgTypes,
                       from: SlushLoopProcess \cup SlushQueryProcess,
                       to: SlushLoopProcess \cup SlushQueryProcess,
                       color: {NoColor} \cup {"color1", "color2"}]
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"SlushClient"} ->
                 {"waitColor", "querying", "tallying", "done"}]
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"SlushClient"} |-> "waitColor"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iteration = [lp \in SlushLoopProcess |-> 0]

LoopProcessFor(lp) == CHOOSE n \in Node : <<n, lp, "lp">> \in HostMapping

AssignColor ==
    /\ pc["SlushClient"] = "waitColor"
    /\ \E n \in Node, c \in {"color1", "color2"} :
         /\ color[n] = NoColor
         /\ color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, pc, sample, iteration>>

RequireColor ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "waitColor"
         /\ var n \in Node
         /\ LoopProcessFor(lp) = n
         /\ color[n] # NoColor
         /\ pc' = [pc EXCEPT ![lp] = "querying"]
    /\ UNCHANGED <<color, msgs, sample, iteration>>

QuerySample ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "querying"
         /\ iteration[lp] < SlushIterationCount
         /\ \E subset \in SUBSET SlushQueryProcess :
              /\ Cardinality(subset) = SampleSetSize
              /\ subset \cap {lp} = {}
              /\ sample' = [sample EXCEPT ![lp] = subset]
              /\ msgs' = msgs \cup
                   {[kind |-> "SlushQuery", from |-> lp,
                     to |-> q, color |-> color[LoopProcessFor(lp])]}
         /\ UNCHANGED <<color, pc, iteration>>
    /\ UNCHANGED <<color, msgs, pc, sample, iteration>>

RespondToQuery ==
    /\ \E msg \in msgs :
         /\ msg.kind = "SlushQuery"
         /\ \E q \in SlushQueryProcess :
              /\ msg.to = q
              /\ LET n == CHOOSE n \in Node : <<n, q, "qp">> \in HostMapping IN
                   msgs' = (msgs \ {msg}) \cup
                     {[kind |-> "SlushQueryReply", from |-> q, to |-> msg.from,
                       color |-> IF color[n] = NoColor THEN msg.color ELSE color[n]]}
    /\ UNCHANGED <<color, pc, sample, iteration>>

TallyReplies ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "tallying"
         /\ Cardinality(sample[lp]) = SampleSetSize
         /\ \E replies \in [SlushQueryProcess -> {NoColor} \cup {"color1", "color2"}] :
              /\ \A q \in sample[lp] :
                   \E msg \in msgs :
                     /\ msg.kind = "SlushQueryReply"
                     /\ msg.from = q
                     /\ msg.to = lp
                     /\ replies[q] = msg.color
                     /\ msgs' = msgs \ {msg}
              /\ LET c1 == Cardinality({q \in sample[lp] : replies[q] = "color1"})
                 IN
                 LET c2 == Cardinality({q \in sample[lp] : replies[q] = "color2"})
                 IN
                 color' = [color EXCEPT ![LoopProcessFor(lp)] =
                            IF c1 >= PickFlipThreshold THEN "color1"
                            ELSE IF c2 >= PickFlipThreshold THEN "color2"
                            ELSE color[LoopProcessFor(lp)]]
              /\ pc' = [pc EXCEPT ![lp] = "querying"]
              /\ iteration' = [iteration EXCEPT ![lp] = iteration[lp] + 1]
              /\ sample' = [sample EXCEPT ![lp] = {}]
    /\ UNCHANGED <<msgs>>

LoopTermination ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "querying"
         /\ iteration[lp] = SlushIterationCount
         /\ pc' = [pc EXCEPT ![lp] = "done"]
         /\ msgs' = msgs \cup [kind |-> "SlushTermination", from |-> lp, to |-> "SlushClient", color |-> NoColor]
    /\ UNCHANGED <<color, sample, iteration>>

QueryLoopExit ==
    /\ \E q \in SlushQueryProcess :
         /\ pc[q] = "waitColor"
         /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
         /\ pc' = [pc EXCEPT ![q] = "done"]
    /\ UNCHANGED <<color, msgs, sample, iteration>>

Next ==
    \/ AssignColor
    \/ RequireColor
    \/ QuerySample
    \/ RespondToQuery
    \/ TallyReplies
    \/ LoopTermination
    \/ QueryLoopExit

Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iteration>>

Termination ==
    /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
    /\ \A q \in SlushQueryProcess : pc[q] = "done"
    /\ pc["SlushClient"] = "done"

====