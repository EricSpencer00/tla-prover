---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush is the simplest member of the Snow family: nodes keep flipping their
\* opinion to whatever color a strict majority of a sampled peer set says.
\* This is a PlusCal spec, so the identifiers below must be emitted exactly as
\* they appear in the reference .cfg file -- constants, init, next, spec, etc.

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

ASSUME /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
       /\ Cardinality(Node) = Cardinality(SlushQueryProcess)

\* Each node has one host process per role; HostMapping ties it together.
\* The full set of message types the network may carry.
MessageType == {"SlushQuery", "SlushQueryReply", "SlushTerminate"}

VARIABLES colorOf, messages, pc, sampleSet, loopIters

vars == <<colorOf, messages, pc, sampleSet, loopIters>>

TypeOK ==
  /\ colorOf \in [Node -> {NoColor} \union ("color" \union {})]
  /\ messages \subseteq [type: MessageType, from: SlushLoopProcess \union SlushQueryProcess,
                          to: SlushLoopProcess \union SlushQueryProcess, node: Node]
  /\ pc \in [SlushLoopProcess \union SlushQueryProcess \union {"clientRequest"} ->
              {"waitColor", "sampleSet", "tally", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ colorOf = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in SlushLoopProcess \union SlushQueryProcess \union {"clientRequest"} |-> "waitColor"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ loopIters = [p \in SlushLoopProcess |-> 0]

\* Client process assigns initial colors to uncolored nodes, one at a time.
ClientAssignsColor ==
  /\ pc["clientRequest"] = "waitColor"
  /\ \E n \in Node : colorOf[n] = NoColor
        /\ \E c \in {"color"} : colorOf' = [colorOf EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, pc, sampleSet, loopIters>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "waitColor"
       /\ \E n \in Node : <<p, n>> \in HostMapping
       /\ colorOf[n] # NoColor
       /\ pc' = [pc EXCEPT ![p] = "sampleSet"]
  /\ UNCHANGED <<colorOf, messages, sampleSet, loopIters>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "sampleSet"
       /\ \E n \in Node : <<p, n>> \in HostMapping
       /\ loopIters[p] < SlushIterationCount
       /\ \E qs \in SUBSET SlushQueryProcess :
            /\ Cardinality(qs) = SampleSetSize
            /\ \A q \in qs : \A n \in Node : <<q, n>> \in HostMapping
            /\ sampleSet' = [sampleSet EXCEPT ![p] = qs]
       /\ \E m \in qs : messages' = messages \union {[type |-> "SlushQuery",
                            from |-> p, to |-> m, node |-> n]}
       /\ pc' = [pc EXCEPT ![p] = "tally"]
  /\ UNCHANGED <<colorOf, loopIters>>

RespondToQuery ==
  /\ \E q \in SlushQueryProcess :
       /\ \E m \in SlushLoopProcess :
            \E msg \in messages :
              /\ msg.type = "SlushQuery"
              /\ msg.from = m /\ msg.to = q
              /\ LET n == msg.node IN
                   /\ colorOf' = IF colorOf[n] = NoColor
                                 THEN [colorOf EXCEPT ![n] = "color"]
                                 ELSE colorOf
                   /\ messages' = (messages \ {msg})
                                      \union {[type |-> "SlushQueryReply", from |-> q,
                                               to |-> m, node |-> n]}
  /\ UNCHANGED <<pc, sampleSet, loopIters>>

\* The loop process counts replies and flips its host node if the majority flips.
TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "tally"
       /\ \E n \in Node : <<p, n>> \in HostMapping
       /\ sampleSet[p] # {}
       /\ \A q \in sampleSet[p] : Cardinality({msg \in messages :
              /\ msg.type = "SlushQueryReply" /\ msg.from = q /\ msg.node = n}) = 1
       /\ LET count == Cardinality({q \in sampleSet[p] :
              colorOf[(CHOOSE n \in Node : <<q, n>> \in HostMapping)] = "color"}) IN
            \A q \in sampleSet[p] :
              colorOf[(CHOOSE n \in Node : <<q, n>> \in HostMapping)] = "color"
              \/ count < PickFlipThreshold
            /\ colorOf' = IF count >= PickFlipThreshold THEN [colorOf EXCEPT ![n] = "color"]
                          ELSE colorOf
       /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
       /\ loopIters' = [loopIters EXCEPT ![p] = @ + 1]
       /\ pc' = [pc EXCEPT ![p] = "sampleSet"]
  /\ UNCHANGED messages

\* A loop that has run all its iterations broadcasts termination.
LoopTerminate ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "sampleSet"
       /\ loopIters[p] = SlushIterationCount
       /\ \E n \in Node : <<p, n>> \in HostMapping
       /\ messages' = messages \union {[type |-> "SlushTerminate", from |-> p, to |-> p, node |-> n]}
       /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<colorOf, sampleSet, loopIters>>

QueryLoopExit ==
  /\ \A q \in SlushQueryProcess :
        \/ pc[q] = "waitColor"
           /\ \A m \in SlushLoopProcess :
                \A msg \in messages : ~(msg.type = "SlushTerminate" /\ msg.from = m)
        \/ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<colorOf, messages, sampleSet, loopIters>>

Next ==
  \/ ClientAssignsColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
  \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

\* SAFETY: only well-typed colors, replies and messages appear anywhere.
TypeInvariant == TypeOK

Spec == Init /\ [][Next]_vars

\* Progress: every process must eventually finish its role.
Progress ==
  /\ <> (\A p \in SlushLoopProcess : pc[p] = "done")
  /\ <> (\A q \in SlushQueryProcess : pc[q] = "done")

====