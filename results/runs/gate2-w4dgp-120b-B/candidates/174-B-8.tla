---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Node,
  SlushLoopProcess,
  SlushQueryProcess,
  HostMapping,
  SlushIterationCount,
  SampleSetSize,
  PickFlipThreshold

ASSUME /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
       /\ Cardinality(Node) = Cardinality(SlushQueryProcess)
       /\ SlushIterationCount \in Nat
       /\ SampleSetSize \in Nat
       /\ PickFlipThreshold \in Nat

ASSUME HostMappingType ==
  /\ Cardinality(Node) = Cardinality(HostMapping)
  /\ \A mapping \in HostMapping :
       /\ Cardinality(mapping) = 3
       /\ \E e \in mapping : e \in Node
       /\ \E e \in mapping : e \in SlushLoopProcess
       /\ \E e \in mapping : e \in SlushQueryProcess

HostOf[pid \in SlushLoopProcess \cup SlushQueryProcess] ==
  CHOOSE n \in Node :
    /\ \E mapping \in HostMapping :
         /\ n \in mapping /\ pid \in mapping
    /\ UNCHANGED n

Red == "Red"
Blue == "Blue"
Color == {Red, Blue}
NoColor == CHOOSE c : c \notin Color
QueryMessageType == "QueryMessageType"
QueryReplyMessageType == "QueryReplyMessageType"
TerminationMessageType == "TerminationMessageType"

QueryMessage == [
  type  : {QueryMessageType},
  src   : SlushLoopProcess,
  dst   : SlushQueryProcess,
  color : Color
]

QueryReplyMessage == [
  type  : {QueryReplyMessageType},
  src   : SlushQueryProcess,
  dst   : SlushLoopProcess,
  color : Color
]

TerminationMessage == [
  type : {TerminationMessageType},
  pid  : SlushLoopProcess
]

Message == QueryMessage \cup QueryReplyMessage \cup TerminationMessage
NoMessage == CHOOSE m : m \notin Message

Define ==
  /\ Pick(pid) == pick[HostOf[pid]]
  /\ TypeInvariant ==
      /\ pick \in [Node -> Color \cup {NoColor}]
      /\ message \subseteq Message
  /\ PendingQueryMessage(pid) ==
       {m \in message : /\ m.type = QueryMessageType /\ m.dst = pid}
  /\ PendingQueryReplyMessage(pid) ==
       {m \in message : /\ m.type = QueryReplyMessageType /\ m.dst = pid}
  /\ Terminate == message = TerminationMessage

VARIABLES pick, message, pc, sampleSet, loopVariant

vars == << pick, message, pc, sampleSet, loopVariant >>

Init ==
  /\ pick = [n \in Node |-> NoColor]
  /\ message = {}
  /\ sampleSet = [l \in SlushLoopProcess |-> {}]
  /\ loopVariant = [l \in SlushLoopProcess |-> 0]
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"ClientRequest"}
           |-> CASE p \in SlushQueryProcess -> "QueryReplyLoop"
                   [] p \in SlushLoopProcess -> "RequireColorAssignment"
                   [] p = "ClientRequest" -> "ClientRequestLoop"]

\* SlushLoop: Create a query message, then tally replies and possibly flip.
QuerySampleSet(self) ==
  /\ pc[self] = "QuerySampleSet"
  /\ \E possibleSampleSet \in
        LET otherNodes == Node \ {HostOf[self]}
            otherQueryProcesses == {q \in SlushQueryProcess : HostOf[q] \in otherNodes}
        IN {S \subseteq otherQueryProcesses : Cardinality(S) = SampleSetSize} :
        /\ sampleSet' = [sampleSet EXCEPT ![self] = possibleSampleSet]
        /\ message' = message \cup
                        {[type  |-> QueryMessageType,
                          src   |-> self,
                          dst   |-> q,
                          color |-> Pick(self)] : q \in possibleSampleSet}
  /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
  /\ UNCHANGED << pick, loopVariant >>

TallyQueryReplies(self) ==
  /\ pc[self] = "TallyQueryReplies"
  /\ \A pid \in sampleSet[self] :
       \E msg \in PendingQueryReplyMessage(self) : msg.src = pid
  /\ LET redTally == Cardinality(
         {msg \in PendingQueryReplyMessage(self) :
            /\ msg.src \in sampleSet[self] /\ msg.color = Red})
       blueTally == Cardinality(
         {msg \in PendingQueryReplyMessage(self) :
            /\ msg.src \in sampleSet[self] /\ msg.color = Blue})
       newPick == IF redTally >= PickFlipThreshold THEN Red
                  ELSE IF blueTally >= PickFlipThreshold THEN Blue
                  ELSE pick[HostOf[self]]
  /\ pick' = [pick EXCEPT ![HostOf[self]] = newPick]
  /\ message' = message \ {msg \in message :
         /\ msg.type = QueryReplyMessageType /\ msg.src \in sampleSet[self] /\ msg.dst = self}
  /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
  /\ loopVariant' = [loopVariant EXCEPT ![self] = loopVariant[self] + 1]
  /\ pc' = [pc EXCEPT ![self] = IF loopVariant[self] + 1 < SlushIterationCount
                                  THEN "QuerySampleSet" ELSE "SlushLoopTermination"]

SlushLoopTermination(self) ==
  /\ pc[self] = "SlushLoopTermination"
  /\ message' = message \cup {[type |-> TerminationMessageType, pid |-> self]}
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED << pick, sampleSet, loopVariant >>

\* SlushQuery: A single loop that replies to a query message.
RespondToQueryMessage(self) ==
  /\ pc[self] = "RespondToQueryMessage"
  /\ \E msg \in PendingQueryMessage(self) :
       LET c == IF Pick(self) = NoColor THEN msg.color ELSE Pick(self) IN
         /\ pick' = [pick EXCEPT ![HostOf[self]] = c]
         /\ message' = (message \ {msg}) \cup
                         {[type |-> QueryReplyMessageType,
                           src  |-> self,
                           dst  |-> msg.src,
                           color |-> c]}
  /\ pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
  /\ UNCHANGED << sampleSet, loopVariant >>

RequireColorAssignment(self) ==
  /\ pc[self] = "RequireColorAssignment"
  /\ Pick(self) # NoColor
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

ExecuteSlushLoop(self) ==
  /\ pc[self] = "ExecuteSlushLoop"
  /\ pc' = [pc EXCEPT ![self] = IF loopVariant[self] < SlushIterationCount
                                  THEN "QuerySampleSet" ELSE "SlushLoopTermination"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

QueryReplyLoop(self) ==
  /\ pc[self] = "QueryReplyLoop"
  /\ IF ~Terminate
       THEN pc' = [pc EXCEPT ![self] = "RespondToQueryMessage"]
       ELSE pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

QueryReply(self) == QueryReplyLoop(self) \/ RespondToQueryMessage(self)

SlushLoop(self) == RequireColorAssignment(self) \/ ExecuteSlushLoop(self)
                     \/ QuerySampleSet(self) \/ TallyQueryReplies(self)
                     \/ SlushLoopTermination(self)

\* ClientRequest: Assign every node a color so the protocol makes progress.
ClientRequestLoop ==
  /\ pc["ClientRequest"] = "ClientRequestLoop"
  /\ IF \E n \in Node : pick[n] = NoColor
       THEN pc' = [pc EXCEPT !["ClientRequest"] = "AssignColorToNode"]
       ELSE pc' = [pc EXCEPT !["ClientRequest"] = "Done"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

AssignColorToNode ==
  /\ pc["ClientRequest"] = "AssignColorToNode"
  /\ \E n \in Node : \E c \in Color :
        pick' = [pick EXCEPT ![n] = IF pick[n] = NoColor THEN c ELSE pick[n]]
  /\ pc' = [pc EXCEPT !["ClientRequest"] = "ClientRequestLoop"]
  /\ UNCHANGED << message, sampleSet, loopVariant >>

ClientRequest == ClientRequestLoop \/ AssignColorToNode

Terminating == /\ \A p \in pc : pc[p] = "Done"
               /\ UNCHANGED vars

Next == ClientRequest \/ (\E s \in SlushQueryProcess : QueryReply(s))
            \/ (\E l \in SlushLoopProcess : SlushLoop(l)) \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A p \in pc : pc[p] = "Done")

====