---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

ASSUME /\ \* Every process is linked to exactly one node, and each node has
       /\ Cardinality(HostMapping) = Cardinality(Node)
       /\ \A n \in Node : Cardinality({p \in HostMapping : p[1] = n}) = 1

VARIABLES
    color, messages, pc, sampleSet, iterationsCompleted

vars == <<color, messages, pc, sampleSet, iterationsCompleted>>

ReplyMessages == [toThis : SlushLoopProcess, color : {NoColor} \union (Node \ {NoColor})]

QueryMessages == [fromThis : SlushLoopProcess, color : {NoColor} \union (Node \ {NoColor})]

Init == [toThis |-> l, color |-> NoColor] \in ReplyMessages

TerminationMessages == [fromThis : SlushLoopProcess]

TypeOK ==
    /\ color \in [Node -> {NoColor} \union (Node \ {NoColor})]
    /\ messages \subseteq (ReplyMessages \union QueryMessages \union TerminationMessages)
    /\ pc \in [SlushLoopProcess \union SlushQueryProcess \union {"client"} -> 0..3]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iterationsCompleted \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ messages = {}
    /\ pc = [p \in (SlushLoopProcess \union SlushQueryProcess \union {"client"}) |-> 0]
    /\ sampleSet = [l \in SlushLoopProcess |-> {}]
    /\ iterationsCompleted = [l \in SlushLoopProcess |-> 0]

AssignClientColor ==
    /\ pc["client"] < 2
    /\ \E n \in Node :
         /\ color[n] = NoColor
         /\ color' = [color EXCEPT ![n] = n]
    /\ pc' = [pc EXCEPT !["client"] = 2]
    /\ UNCHANGED <<messages, sampleSet, iterationsCompleted>>

RequireLoopColor ==
    /\ \E l \in SlushLoopProcess :
         /\ pc[l] = 0
         /\ color[CHOOSE n \in Node : <<l, n>> \in HostMapping] # NoColor
         /\ pc' = [pc EXCEPT ![l] = 1]
    /\ UNCHANGED <<color, messages, sampleSet, iterationsCompleted>>

\* The loop process sends a query to a random sample of peers; the sample
\* size is fixed here, but which peers land in the sample changes each round.
QuerySampleSet ==
    /\ \E l \in SlushLoopProcess :
         /\ pc[l] = 1
         /\ LET spoons \in SUBSET SlushQueryProcess :
                spoons = {p \in SlushQueryProcess : p[2] = CHOOSE n \in Node : <<l, n>> \in HostMapping}
                /\ Cardinality(spoons) = SampleSetSize
              msgs == { [fromThis |-> l, color |-> color[CHOOSE n \in Node : <<l, n>> \in HostMapping]] : p \in spoons }
         /\ messages' = messages \union msgs
         /\ sampleSet' = [sampleSet EXCEPT ![l] = spoons]
         /\ pc' = [pc EXCEPT ![l] = 2]
    /\ UNCHANGED <<color, iterationsCompleted>>

\* A query process adopts the query's color if it is still uncolored.
RespondToQuery ==
    /\ \E m \in messages :
         /\ m \in QueryMessages
         /\ pc[m.fromThis] = 2
         /\ LET hostNode == CHOOSE n \in Node : <<m.fromThis, n>> \in HostMapping
              hostQuery == CHOOSE p \in SlushQueryProcess : p[1] = hostNode
         /\ color' = IF color[hostNode] = NoColor
                     THEN [color EXCEPT ![hostNode] = m.color]
                     ELSE color
         /\ messages' = (messages \ {m}) \union {[toThis |-> m.fromThis, color |-> color[hostNode]]}
    /\ UNCHANGED <<pc, sampleSet, iterationsCompleted>>

TallyReplies ==
    /\ \E l \in SlushLoopProcess :
         /\ pc[l] = 2
         /\ Cardinality({p \in messages : p \in ReplyMessages /\ p.toThis = l}) = SampleSetSize
         /\ LET replies == {p \in messages : p \in ReplyMessages /\ p.toThis = l}
                colorTally(c) == Cardinality({p \in replies : p.color = c})
                winner == CHOOSE c \in Node : colorTally(c) >= PickFlipThreshold
                hostNode == CHOOSE n \in Node : <<l, n>> \in HostMapping
         /\ color' = [color EXCEPT ![hostNode] = winner]
         /\ messages' = messages \ {p \in replies}
         /\ sampleSet' = [sampleSet EXCEPT ![l] = {}]
         /\ iterationsCompleted' = [iterationsCompleted EXCEPT ![l] = @ + 1]
         /\ pc' = [pc EXCEPT ![l] = 3]
    /\ UNCHANGED <<pc>>

LoopTerminate ==
    /\ \E l \in SlushLoopProcess :
         /\ pc[l] = 3
         /\ iterationsCompleted[l] = SlushIterationCount
         /\ messages' = messages \union {[fromThis |-> l]}
         /\ pc' = [pc EXCEPT ![l] = 4]
    /\ UNCHANGED <<color, sampleSet, iterationsCompleted>>

QueryLoopExit ==
    /\ \E p \in SlushQueryProcess :
         /\ pc[p] = 0
         /\ \A l \in SlushLoopProcess : [fromThis |-> l] \in messages
         /\ pc' = [pc EXCEPT ![p] = 4]
    /\ UNCHANGED <<color, messages, sampleSet, iterationsCompleted>>

Next == AssignClientColor \/ RequireLoopColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

AllProcessesDone == \A p \in (SlushLoopProcess \union SlushQueryProcess \union {"client"}) : pc[p] = 4

TerminationProperty == <>AllProcessesDone

====