---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount,
  SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Nodes are paired with their loop and query processes through HostMapping.
\* The system tracks the color of each node and a set of in-flight messages.
\* Slush is a metastable consensus protocol: nodes repeatedly poll random peers
\* and adopt a color that reaches a threshold in the current sample. Since
\* TLA+ has no probabilistic modeling, convergence cannot be proved here; the
\* spec is a straightforward operational model instead.

VARIABLES color, messages, pc, sample, iterCount

vars == <<color, messages, pc, sample, iterCount>>

Message == [msg : {"query", "queryReply", "termination"},
  src : SlushLoopProcess \cup SlushQueryProcess,
  dst : SlushLoopProcess \cup SlushQueryProcess, val : {NoColor} \cup {"blue", "red"}]

HostsFor(n) == { p \in HostMapping : p[1] = n }

TypeOK ==
  /\ color \in [Node -> {NoColor} \cup {"blue", "red"}]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess -> {"waiting", "waitingForColor",
        "querying", "counting", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [lp \in SlushLoopProcess |-> "waiting"]
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ iterCount = [lp \in SlushLoopProcess |-> 0]

AllDone == \A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] = "done"

\* Client assigns a random color to an uncolored node (an external request).
AssignColor(n) ==
  /\ color[n] = NoColor
  /\ \E c \in {"blue", "red", "green"} : color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, pc, sample, iterCount>>

RequireColor(lp) ==
  /\ pc[lp] = "waiting"
  /\ color[HostsFor(lp)[1]] # NoColor
  /\ pc' = [pc EXCEPT ![lp] = "querying"]
  /\ UNCHANGED <<color, messages, sample, iterCount>>

SendQuery(lp, qp) ==
  /\ pc[lp] = "querying"
  /\ qp \notin sample[lp]
  /\ Cardinality(sample[lp]) < SampleSetSize
  /\ sample' = [sample EXCEPT ![lp] = @ \cup {qp}]
  /\ messages' = messages \cup {[msg |-> "query", src |-> lp, dst |-> qp,
        val |-> color[HostsFor(lp)[1]]]}
  /\ pc' = [pc EXCEPT ![lp] = "counting"]
  /\ UNCHANGED <<color, iterCount>>

\* Query processes adopt a color on behalf of an uncolored host the first time
\* they are sampled, then always reply with the host's current color.
ReplyToQuery(qp) ==
  /\ \E q \in messages :
        /\ q.msg = "query" /\ q.dst = qp /\ q.src \in SlushLoopProcess
        /\ (color[HostsFor(qp)[1]] = NoColor => color' = [color EXCEPT ![HostsFor(qp)[1]] = q.val])
        /\ messages' = (messages \ {q}) \cup
              {[msg |-> "queryReply", src |-> qp, dst |-> q.src, val |->
                  IF color[HostsFor(qp)[1]] = NoColor THEN q.val ELSE color[HostsFor(qp)[1]]]}
  /\ UNCHANGED <<pc, sample, iterCount>>

TallyReplies(lp) ==
  /\ pc[lp] = "counting"
  /\ \A qp \in sample[lp] : [msg |-> "queryReply", src |-> qp, dst |-> lp,
        val |-> "blue"] \in messages \/ [msg |-> "queryReply", src |-> qp, dst |-> lp,
        val |-> "red"] \in messages
  /\ \E c \in {"blue", "red"} :
        /\ Cardinality({ qp \in sample[lp] :
              [msg |-> "queryReply", src |-> qp, dst |-> lp, val |-> c] \in messages })
              >= PickFlipThreshold
        /\ color' = [color EXCEPT ![HostsFor(lp)[1]] = c]
  /\ messages' = messages \ {[msg |-> "queryReply", src |-> qp, dst |-> lp, val |-> v] :
        qp \in sample[lp] /\ v \in {"blue", "red"}}
  /\ sample' = [sample EXCEPT ![lp] = {}]
  /\ iterCount' = [iterCount EXCEPT ![lp] = @ + 1]
  /\ pc' = IF iterCount[lp] + 1 >= SlushIterationCount THEN "done" ELSE "querying"

Terminate(lp) ==
  /\ pc[lp] = "done"
  /\ messages' = messages \cup {[msg |-> "termination", src |-> lp, dst |-> NoMessage, val |-> NoColor]}
  /\ UNCHANGED <<color, pc, sample, iterCount>>

QueryLoopExit(qp) ==
  /\ pc[qp] = "waiting"
  /\ AllDone
  /\ pc' = [pc EXCEPT ![qp] = "done"]
  /\ UNCHANGED <<color, messages, sample, iterCount>>

Next ==
  \/ \E n \in Node : AssignColor(n)
  \/ \E lp \in SlushLoopProcess : RequireColor(lp) \/ TallyReplies(lp) \/ Terminate(lp)
  \/ \E qp \in SlushQueryProcess : ReplyToQuery(qp) \/ QueryLoopExit(qp)
  \/ \E lp \in SlushLoopProcess, qp \in SlushQueryProcess : SendQuery(lp, qp)

Spec == Init /\ [][Next]_vars /\ (\A lp \in SlushLoopProcess : WF_vars(TallyReplies(lp)))

TypeInvariant == TypeOK

Termination == AllDone

====