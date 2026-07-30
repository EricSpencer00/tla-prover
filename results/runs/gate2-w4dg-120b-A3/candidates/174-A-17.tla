---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node,
  SlushLoopProcess,
  SlushQueryProcess,
  HostMapping,
  SlushIterationCount,
  SampleSetSize,
  PickFlipThreshold,
  NoColor,
  NoMessage

\* Procedure identifiers (RunLoop, RunQuery) are tied to processes rather than
\* being global constants, so the spec declares their current step for each
\* process instead of a single shared PC.
Steps == {"idle", "runLoop", "runQuery", "done"}

MsgKinds == {"query", "reply", "done"}

VARIABLES
  nodeColor,
  messages,
  loopStep,
  queryStep,
  sampleSet,
  iteration

vars == <<nodeColor, messages, loopStep, queryStep, sampleSet, iteration>>

TypeInvariant ==
  /\ nodeColor \in [Node -> {NoColor} \cup {"red", "blue"}]
  /\ messages \subseteq [kind: MsgKinds, from: SlushLoopProcess \cup SlushQueryProcess,
                         to: SlushLoopProcess \cup SlushQueryProcess, color: {NoMessage} \cup {"red", "blue"}]
  /\ loopStep \in [SlushLoopProcess -> Steps]
  /\ queryStep \in [SlushQueryProcess -> Steps]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ loopStep = [lp \in SlushLoopProcess |-> "idle"]
  /\ queryStep = [qp \in SlushQueryProcess |-> "runQuery"]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ iteration = [lp \in SlushLoopProcess |-> 0]

ClientAssignsColor(n, c) ==
  /\ nodeColor[n] = NoColor
  /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, loopStep, queryStep, sampleSet, iteration>>

RequireColor(lp) ==
  /\ loopStep[lp] = "idle"
  /\ \E n \in Node : (lp, n) \in HostMapping /\ nodeColor[n] # NoColor
  /\ loopStep' = [loopStep EXCEPT ![lp] = "runLoop"]
  /\ UNCHANGED <<nodeColor, messages, queryStep, sampleSet, iteration>>

SelectSample(lp) ==
  /\ loopStep[lp] = "runLoop"
  /\ iteration[lp] < SlushIterationCount
  /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
  /\ \E peers \in SUBSET SlushQueryProcess :
       /\ Cardinality(peers) = SampleSetSize
       /\ sampleSet' = [sampleSet EXCEPT ![lp] = peers]
  /\ messages' = [m \in messages :
       m.kind = "query" /\ m.from = lp /\ ~ (m.to \in sampleSet[lp])]
  /\ messages' = messages \cup
       { [kind |-> "query", from |-> lp, to |-> qp,
          color |-> nodeColor[CHOOSE n \in Node : (lp, n) \in HostMapping]]
         : qp \in sampleSet[lp] }
  /\ UNCHANGED <<nodeColor, loopStep, queryStep, iteration>>

RespondToQuery(qp, m) ==
  /\ m \in messages
  /\ m.kind = "query" /\ m.to = qp
  /\ LET n == CHOOSE x \in Node : (CHOOSE p \in SlushLoopProcess : (p, x) \in HostMapping) = qp
     ev == IF nodeColor[n] = NoColor THEN m.color ELSE nodeColor[n]
  IN
    /\ nodeColor' = [nodeColor EXCEPT ![n] = ev]
    /\ messages' = (messages \ {m}) \cup
         {[kind |-> "reply", from |-> qp, to |-> m.from, color |-> ev]}
  /\ UNCHANGED <<loopStep, queryStep, sampleSet, iteration>>

TallyReplies(lp) ==
  /\ loopStep[lp] = "runLoop"
  /\ \E rp \in SlushLoopProcess \ sampleSet[lp] :
       [kind |-> "reply", from |-> rp, to |-> lp, color |-> "red"] \in messages
  /\ LET counts ==
         ([c \in {"red", "blue"} |-> Cardinality(
            {m \in messages : m.kind = "reply" /\ m.to = lp /\ m.color = c})])
       nv == IF counts["red"] >= PickFlipThreshold
             THEN "red" ELSE IF counts["blue"] >= PickFlipThreshold THEN "blue" ELSE NoColor
  IN
    /\ nodeColor' = IF nv = NoColor THEN nodeColor
                    ELSE [nodeColor EXCEPT ![CHOOSE n \in Node : (lp, n) \in HostMapping] = nv]
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
    /\ iteration' = [iteration EXCEPT ![lp] = iteration[lp] + 1]
    /\ loopStep' = [loopStep EXCEPT ![lp] = "runLoop"]
    /\ messages' = messages \ {[kind |-> "reply", from |-> rp, to |-> lp, color |-> "red"}
                                : rp \in sampleSet[lp]}
  /\ UNCHANGED queryStep

LoopTerminates(lp) ==
  /\ loopStep[lp] \in {"runLoop", "idle"}
  /\ iteration[lp] = SlushIterationCount
  /\ loopStep' = [loopStep EXCEPT ![lp] = "done"]
  /\ messages' = messages \cup
       {[kind |-> "done", from |-> lp, to |-> lp, color |-> NoMessage]}
  /\ UNCHANGED <<nodeColor, queryStep, sampleSet, iteration>>

QueryLoopExits(qp) ==
  /\ queryStep[qp] = "runQuery"
  /\ \A lp \in SlushLoopProcess : [kind |-> "done", from |-> lp, to |-> lp, color |-> NoMessage] \in messages
  /\ queryStep' = [queryStep EXCEPT ![qp] = "done"]
  /\ UNCHANGED <<nodeColor, messages, loopStep, sampleSet, iteration>>

Next ==
  \/ \E n \in Node, c \in {"red", "blue"} : ClientAssignsColor(n, c)
  \/ \E lp \in SlushLoopProcess : RequireColor(lp)
  \/ \E lp \in SlushLoopProcess : SelectSample(lp)
  \/ \E qp \in SlushQueryProcess, m \in messages : RespondToQuery(qp, m)
  \/ \E lp \in SlushLoopProcess : TallyReplies(lp)
  \/ \E lp \in SlushLoopProcess : LoopTerminates(lp)
  \/ \E qp \in SlushQueryProcess : QueryLoopExits(qp)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E n \in Node, c \in {"red", "blue"} : ClientAssignsColor(n, c))
  /\ WF_vars(\E lp \in SlushLoopProcess : RequireColor(lp))
  /\ WF_vars(\E lp \in SlushLoopProcess : SelectSample(lp))
  /\ WF_vars(\E qp \in SlushQueryProcess, m \in messages : RespondToQuery(qp, m))
  /\ WF_vars(\E lp \in SlushLoopProcess : TallyReplies(lp))
  /\ WF_vars(\E lp \in SlushLoopProcess : LoopTerminates(lp))
  /\ WF_vars(\E qp \in SlushQueryProcess : QueryLoopExits(qp))

Termination == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess : loopStep[p] = "done")

====