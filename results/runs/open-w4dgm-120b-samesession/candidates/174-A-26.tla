---- MODULE Slush ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

ASSUME Cardinality(SlushLoopProcess) = Cardinality(Node)
ASSUME Cardinality(SlushQueryProcess) = Cardinality(Node)
ASSUME SlushIterationCount \in Nat
ASSUME SampleSetSize \in Nat
ASSUME PickFlipThreshold \in Nat

\* Each loop/query process is linked to exactly one node via HostMapping.
\* The spec does not use the mapping except to look up a process' host node.
\* Types of in-flight messages; a message is a tuple whose shape is checked
\* against the three legal forms in TypeInvariant below.
Message == SlushLoopProcess \X Node \X (Node \cup {NoColor})
\* (_sender, _receiver, _queryColor) -- a query or reply naming its payload.
QueryReply(m) == /\ Cardinality(m) = 3
                 /\ (m[3] \in Node \cup {NoColor})
ReplyBody(m) == m[3]

Variable color, messages, pc, sample, iteration

vars == <<color, messages, pc, sample, iteration>>

COMPUTED == {m \in messages : Cardinality(m) = 3 /\ m[3] \in Node}

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ messages = {}
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {NoMessage} |-> "idle"]
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iteration = 0

AllLoopProcessesDone == \A p \in SlushLoopProcess : pc[p] = "done"

\* The client process assigns an initial color to an uncolored node.
ClientAssignColor(c) ==
    /\ \E n \in Node :
        /\ color[n] = NoColor
        /\ color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<messages, pc, sample, iteration>>

RequireColor(p) ==
    /\ pc[p] = "idle"
    /\ color[HostMapping[p][1]] # NoColor
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<color, messages, sample, iteration>>

\* The loop process samples a subset of peers and queries each of them.
QuerySampleSet(p) ==
    /\ pc[p] = "waiting"
    /\ sample' = [sample EXCEPT ![p] = Node \ {HostMapping[p][1]}]
    /\ messages' = messages \cup {<<p, q, color[HostMapping[p][1]]>> : q \in sample[p]}
    /\ UNCHANGED <<color, pc, iteration>>

\* A query process replies with its own node's color (adopting the query
\* color first if its node is still uncolored).
RespondToQuery(m) ==
    /\ m \in messages
    /\ pc[m[2]] = "idle"
    /\ pc' = [pc EXCEPT ![m[2]] = "replying"]
    /\ color' = [color EXCEPT ![HostMapping[m[2]][1]] = IF color[HostMapping[m[2]][1]] = NoColor THEN m[3] ELSE color[HostMapping[m[2]][1]]]
    /\ messages' = (messages \ {m}) \cup {<<m[2], m[1], color[HostMapping[m[2]][1]]>>}
    /\ UNCHANGED <<sample, iteration>>

TallyReplies(p) ==
    /\ pc[p] = "replying"
    /\ \A q \in sample[p] : <<q, p, NoMessage>> \in COMPUTED
    /\ LET cCount[x \in Node] ==
           Cardinality({q \in sample[p] : ReplyBody(<<q, p, NoMessage>>) = x})
       IN
          /\ \E x \in Node : cCount[x] >= PickFlipThreshold
             /\ color' = [color EXCEPT ![HostMapping[p][1]] = x]
          /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ sample' = [sample EXCEPT ![p] = {}]
    /\ iteration' = IF iteration < SlushIterationCount THEN iteration + 1 ELSE iteration
    /\ UNCHANGED messages

LoopTermination(p) ==
    /\ pc[p] = "done"
    /\ iteration >= SlushIterationCount
    /\ messages' = messages \cup {<<p, p, NoMessage>>}
    /\ pc' = [pc EXCEPT ![p] = "terminating"]
    /\ UNCHANGED <<color, sample, iteration>>

ExitQueryLoop ==
    /\ AllLoopProcessesDone
    /\ \A q \in SlushQueryProcess : pc[q] # "idle"
    /\ pc' = [q \in SlushQueryProcess |-> "done"]
    /\ UNCHANGED <<color, messages, sample, iteration>>

Next ==
    \/ \E c \in {NoColor} \cup Node : ClientAssignColor(c)
    \/ \E p \in SlushLoopProcess : RequireColor(p)
    \/ \E p \in SlushLoopProcess : QuerySampleSet(p)
    \/ \E m \in messages : RespondToQuery(m)
    \/ \E p \in SlushLoopProcess : TallyReplies(p)
    \/ \E p \in SlushLoopProcess : LoopTermination(p)
    \/ ExitQueryLoop

Spec == Init /\ [][Next]_vars
        /\ \A m \in messages : WF_vars(RespondToQuery(m))
        /\ \A p \in SlushLoopProcess : WF_vars(TallyReplies(p))
        /\ \A p \in SlushLoopProcess : WF_vars(LoopTermination(p))
        /\ WF_vars(ExitQueryLoop)

TypeInvariant ==
    /\ color \in [Node -> Node \cup {NoColor}]
    /\ \A m \in messages :
         /\ (Cardinality(m) = 2) \/ (Cardinality(m) = 3)
         /\ (Cardinality(m) = 3 => m[3] \in Node \cup {NoColor})

EventualTermination == AllLoopProcessesDone /\ \A q \in SlushQueryProcess : pc[q] = "done"

====