---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold,
          NoColor, NoMessage

MessageTypes == {"query", "queryReply", "termination"}
Colors == {"colorOne", "colorTwo"}
LoopProcessOf(p) == p[1]
QueryProcessOf(q) == q[1]

VARIABLES color, messages, pc, sampleSet, loopsCompleted

vars == <<color, messages, pc, sampleSet, loopsCompleted>>

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ messages = {}
    /\ pc = [p \in SlushLoopProcess |-> "waitingForColor"]
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ loopsCompleted = [p \in SlushLoopProcess |-> 0]

ClientAssignsColor(n) ==
    /\ color[n] = NoColor
    /\ \E c \in Colors : color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<messages, pc, sampleSet, loopsCompleted>>

RequireColor(p) ==
    /\ pc[p] = "waitingForColor"
    /\ (color[LoopProcessOf(p)] # NoColor \/ SlushIterationCount = 0)
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<color, messages, sampleSet, loopsCompleted>>

QuerySampleSet(p) ==
    /\ pc[p] = "idle"
    /\ loopsCompleted[p] < SlushIterationCount
    /\ \E peers \in (SlushQueryProcess \ {p}) :
         sampleSet' = [sampleSet EXCEPT ![p] = peers]
    /\ color[LoopProcessOf(p)] # NoColor
    /\ messages' = messages \cup
         {<<q, "query", LoopProcessOf(p), color[LoopProcessOf(p)]>>
            : q \in sampleSet[p]}
    /\ pc' = [pc EXCEPT ![p] = "collecting"]
    /\ UNCHANGED <<color, loopsCompleted>>

RespondToQuery(q) ==
    /\ \E p \in SlushLoopProcess, c \in Colors :
         /\ <<q, "query", LoopProcessOf(p), c>> \in messages
         /\ color' = IF color[QueryProcessOf(q)] = NoColor
                      THEN [color EXCEPT ![QueryProcessOf(q)] = c]
                      ELSE color
         /\ messages' = (messages \ {<<q, "query", LoopProcessOf(p), c>>})
                         \cup {<<q, "queryReply", LoopProcessOf(p),
                                IF color[QueryProcessOf(q)] = NoColor
                                THEN c ELSE color[QueryProcessOf(q)]>>}
    /\ UNCHANGED <<pc, sampleSet, loopsCompleted>>

TallyReplies(p) ==
    /\ pc[p] = "collecting"
    /\ \A q \in sampleSet[p] : <<q, "queryReply", LoopProcessOf(p), NoColor>> \notin messages
    /\ LET count(c) ==
            Cardinality({q \in sampleSet[p] :
                <<q, "queryReply", LoopProcessOf(p), c>> \in messages})
         n = count(NoColor)
         maxc = CHOOSE c \in Colors : \A d \in Colors : count(c) >= count(d)
      IN color' = IF n = 0 /\ count(maxc) >= PickFlipThreshold
                  THEN [color EXCEPT ![LoopProcessOf(p)] = maxc]
                  ELSE color
    /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
    /\ loopsCompleted' = [loopsCompleted EXCEPT ![p] = loopsCompleted[p] + 1]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED messages

LoopTermination(p) ==
    /\ pc[p] = "idle"
    /\ loopsCompleted[p] = SlushIterationCount
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ messages' = messages \cup {<<p, "termination", NoMessage, NoMessage>>}
    /\ UNCHANGED <<color, sampleSet, loopsCompleted>>

QueryLoopExit(q) ==
    /\ pc[q] \in {"idle", "collecting"}
    /\ \A p \in SlushLoopProcess : <<p, "termination", NoMessage, NoMessage>> \in messages
    /\ pc' = [pc EXCEPT ![q] = "done"]
    /\ UNCHANGED <<color, messages, sampleSet, loopsCompleted>>

Next ==
    \/ \E n \in Node : ClientAssignsColor(n)
    \/ \E p \in SlushLoopProcess : RequireColor(p) \/ TallyReplies(p) \/ LoopTermination(p)
    \/ \E q \in SlushQueryProcess : RespondToQuery(q) \/ QueryLoopExit(q)

Spec == Init /\ [][Next]_vars
        /\ \A p \in SlushLoopProcess : WF_vars(QuerySampleSet(p))
        /\ \A p \in SlushLoopProcess : SF_vars(TallyReplies(p))
        /\ WF_vars(LoopTermination(CHOICE SlushLoopProcess))
        /\ WF_vars(QueryLoopExit(CHOICE SlushQueryProcess))

TypeInvariant ==
    /\ color \in [Node -> Colors \cup {NoColor}]
    /\ messages \subseteq (SlushQueryProcess \X MessageTypes \X SlushLoopProcess \X (Colors \cup {NoColor}))

Termination == <>(\A p \in SlushLoopProcess : pc[p] = "done")
====