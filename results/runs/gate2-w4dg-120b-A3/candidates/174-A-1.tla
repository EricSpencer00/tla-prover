---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush (the simplest Snow protocol) expressed as a PlusCal recipe.  The
\* spec is fully deterministic and exhaustive in its actions; it cannot
\* model the probabilistic convergence of Snow, only the protocol's
\* message-passing steps and structural safety.

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

\* LoopProcess[k] and QueryProcess[k] are the two processes attached to
\* node k in the paired mapping HostMapping.  They are the ones that
\* send and receive Slush's query/reply messages.
Process == SlushLoopProcess \cup SlushQueryProcess

MessageType == {
  [kind |-> "query", sender |-> NoMessage, target |-> NoMessage, c |-> NoMessage],
  [kind |-> "reply", sender |-> NoMessage, target |-> NoMessage, c |-> NoMessage],
  [kind |-> "termination", sender |-> NoMessage, target |-> NoMessage]
}

Variable == <<color, messages, pc, sampleSet, iterCount>>
vars == <<color, messages, pc, sampleSet, iterCount>>

TypeOK ==
  /\ color \in [Node -> {NoColor, "red", "blue"}]
  /\ messages \subseteq MessageType
  /\ pc \in [Process -> {"init", "loop", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterCount \in [SlushLoopProcess -> 0..SlushIterationCount]

\* Every SlushLoopProcess must pair with a SlushQueryProcess for the
\* same node -- that pairing is the invariant, not an artifact of the
\* recipe, so it is checked alongside the other structural properties.
LoopsMatchQueries ==
  /\ Cardinality(SlushLoopProcess) = Cardinality(SlushQueryProcess)
  /\ \A k \in SlushLoopProcess : k \in SlushQueryProcess

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in Process |-> IF p \in SlushQueryProcess THEN "loop" ELSE "init"]
  /\ sampleSet = [k \in SlushLoopProcess |-> {}]
  /\ iterCount = [k \in SlushLoopProcess |-> 0]

\* The client process (not modelled as a separate TLA+ actor; its one
\* action is folded into the recipe) colors every uncolored node.
AssignColor ==
  /\ \E n \in Node, c \in {"red", "blue"} :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, pc, sampleSet, iterCount>>

RequireColor ==
  /\ \E k \in SlushLoopProcess :
       /\ pc[k] = "init"
       /\ \E n \in Node : <<SlushLoopProcess, SlushQueryProcess, n>> \in HostMapping
       /\ LET n == CHOOSE x \in Node : <<SlushLoopProcess, SlushQueryProcess, x>> \in HostMapping
          IN color[n] # NoColor /\ pc' = [pc EXCEPT ![k] = "loop"]
  /\ UNCHANGED <<color, messages, sampleSet, iterCount>>

QuerySampleSet ==
  /\ \E k \in SlushLoopProcess :
       /\ pc[k] = "loop"
       /\ iterCount[k] < SlushIterationCount
       /\ \E peers \in SUBSET SlushQueryProcess :
            /\ peers \subseteq SlushQueryProcess
            /\ Cardinality(peers) = SampleSetSize
            /\ LET n == CHOOSE x \in Node : <<SlushLoopProcess, SlushQueryProcess, x>> \in HostMapping
               IN \A q \in peers :
                    messages' = messages \cup {[kind |-> "query", sender |-> k, target |-> q, c |-> color[n]]}
            /\ sampleSet' = [sampleSet EXCEPT ![k] = peers]
  /\ UNCHANGED <<color, pc, iterCount>>

ReplyToQuery ==
  /\ \E q \in SlushQueryProcess :
       /\ \E m \in messages :
            /\ m.kind = "query" /\ m.target = q
            /\ LET n == CHOOSE x \in Node : <<SlushLoopProcess, SlushQueryProcess, x>> \in HostMapping
               IN /\ color' = [color EXCEPT ![n] = IF color[n] = NoColor THEN m.c ELSE color[n]]
                  /\ messages' = (messages \ {m}) \cup
                                  {[kind |-> "reply", sender |-> q, target |-> m.sender, c |-> IF color[n] = NoColor THEN m.c ELSE color[n]]}
  /\ UNCHANGED <<pc, sampleSet, iterCount>>

TallyReplies ==
  /\ \E k \in SlushLoopProcess :
       /\ sampleSet[k] # {}
       /\ \E cs \in [SlushQueryProcess -> {"red", "blue"}] :
            /\ \A q \in sampleSet[k] : \E m \in messages : m.kind = "reply" /\ m.sender = q /\ m.c = cs[q]
            /\ iterCount' = [iterCount EXCEPT ![k] = IF iterCount[k] < SlushIterationCount THEN iterCount[k] + 1 ELSE iterCount[k]]
            /\ LET c == IF Cardinality({q \in sampleSet[k] : cs[q] = "red"}) >= PickFlipThreshold THEN "red"
                        ELSE IF Cardinality({q \in sampleSet[k] : cs[q] = "blue"}) >= PickFlipThreshold THEN "blue"
                        ELSE "red"
               IN color' = [color EXCEPT ![CHOOSE x \in Node : <<SlushLoopProcess, SlushQueryProcess, x>> \in HostMapping] = c]
            /\ sampleSet' = [sampleSet EXCEPT ![k] = {}]
            /\ messages' = {m \in messages : m.kind # "reply" \/ m.target # k}
  /\ UNCHANGED pc

BroadcastTermination ==
  /\ \E k \in SlushLoopProcess :
       /\ iterCount[k] = SlushIterationCount
       /\ sampleSet[k] = {}
       /\ pc[k] = "loop"
       /\ messages' = messages \cup
            {[kind |-> "termination", sender |-> k, target |-> NoMessage]}
       /\ pc' = [pc EXCEPT ![k] = "done"]
  /\ UNCHANGED <<color, sampleSet, iterCount>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "loop"
       /\ \A m \in messages : ~(m.kind = "query" /\ m.target = q)
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<color, messages, sampleSet, iterCount>>

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ ReplyToQuery
        \/ TallyReplies \/ BroadcastTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
        /\ WF_vars(ReplyToQuery) /\ WF_vars(TallyReplies)
        /\ WF_vars(BroadcastTermination) /\ WF_vars(QueryLoopExit)

AllDone == \A p \in Process : pc[p] = "done"

Quiescence == <>(AllDone) /\ (AllDone ~> AllDone)
====