---- MODULE Slush ------------------------------------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Node,
  SlushLoopProcess,
  SlushQueryProcess,
  HostMapping,
  SlushIterationCount,
  SampleSetSize,
  PickFlipThreshold

ASSUME Cardinality(Node) = Cardinality(SlushLoopProcess)
ASSUME Cardinality(Node) = Cardinality(SlushQueryProcess)
ASSUME SlushIterationCount \in Nat
ASSUME SampleSetSize \in Nat
ASSUME PickFlipThreshold \in Nat
ASSUME Cardinality(Node) = Cardinality(HostMapping)
ASSUME \A mapping \in HostMapping :
  /\ Cardinality(mapping) = 3
  /\ \E e \in mapping : e \in Node
  /\ \E e \in mapping : e \in SlushLoopProcess
  /\ \E e \in mapping : e \in SlushQueryProcess

HostOf[pid \in SlushLoopProcess \cup SlushQueryProcess] ==
  CHOOSE n \in Node :
    /\ \E mapping \in HostMapping : /\ n \in mapping /\ pid \in mapping

VARIABLES pick, message, pc, sampleSet, loopVariant

vars == << pick, message, pc, sampleSet, loopVariant >>
ProcSet == (SlushQueryProcess) \cup (SlushLoopProcess) \cup {"ClientRequest"}

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
  type  : {TerminationMessageType},
  pid   : SlushLoopProcess
]
Message == QueryMessage \cup QueryReplyMessage \cup TerminationMessage
NoMessage == CHOOSE m : m \notin Message
Terminate == message = TerminationMessage
Pick(pid) == pick[HostOf[pid]]

TypeInvariant ==
  /\ pick \in [Node -> Color \cup {NoColor}]
  /\ message \subseteq Message

PendingQueryMessage(pid) == {
  m \in message : /\ m.type = QueryMessageType /\ m.dst = pid
}
PendingQueryReplyMessage(pid) == {
  m \in message : /\ m.type = QueryReplyMessageType /\ m.dst = pid
}

Init ==
  /\ pick = [node \in Node |-> NoColor]
  /\ message = {}
  /\ sampleSet = [self \in SlushLoopProcess |-> {}]
  /\ loopVariant = [self \in SlushLoopProcess |-> 0]
  /\ pc = [self \in ProcSet |-> CASE
        self \in SlushQueryProcess -> "QueryReplyLoop"
        [] self \in SlushLoopProcess -> "RequireColorAssignment"
        [] self = "ClientRequest" -> "ClientRequestLoop"]

QueryReplyLoop(self) ==
  /\ pc[self] = "QueryReplyLoop"
  /\ pc' = [pc EXCEPT ![self] = IF ~Terminate THEN "WaitForQueryMessageOrTermination" ELSE "Done"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

WaitForQueryMessageOrTermination(self) ==
  /\ pc[self] = "WaitForQueryMessageOrTermination"
  /\ PendingQueryMessage(self) /= {} \/ Terminate
  /\ pc' = [pc EXCEPT ![self] = IF Terminate THEN "QueryReplyLoop" ELSE "RespondToQueryMessage"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

RespondToQueryMessage(self) ==
  /\ pc[self] = "RespondToQueryMessage"
  /\ \E msg \in PendingQueryMessage(self) :
       LET color == IF Pick(self) = NoColor THEN msg.color ELSE Pick(self) IN
         /\ pick' = [pick EXCEPT ![HostOf[self]] = color]
         /\ message' = (message \ {msg}) \cup {[type |-> QueryReplyMessageType,
                            src  |-> self, dst |-> msg.src, color |-> color]}
  /\ pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
  /\ UNCHANGED << sampleSet, loopVariant >>

SlushQuery(self) == QueryReplyLoop(self) \/ WaitForQueryMessageOrTermination(self)
                      \/ RespondToQueryMessage(self)

RequireColorAssignment(self) ==
  /\ pc[self] = "RequireColorAssignment"
  /\ Pick(self) /= NoColor
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

ExecuteSlushLoop(self) ==
  /\ pc[self] = "ExecuteSlushLoop"
  /\ pc' = [pc EXCEPT ![self] = IF loopVariant[self] < SlushIterationCount
                                        THEN "QuerySampleSet" ELSE "SlushLoopTermination"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

QuerySampleSet(self) ==
  /\ pc[self] = "QuerySampleSet"
  /\ \E possibleSampleSet \in
        LET otherNodes == Node \ {HostOf[self]}
            otherQueryProcesses == {pid \in SlushQueryProcess : HostOf[pid] \in otherNodes}
        IN {pidSet \in SUBSET otherQueryProcesses : Cardinality(pidSet) = SampleSetSize} :
         /\ sampleSet' = [sampleSet EXCEPT ![self] = possibleSampleSet]
         /\ message' = message \cup {[type |-> QueryMessageType, src |-> self,
                         dst |-> pid, color |-> Pick(self)] : pid \in possibleSampleSet}
  /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
  /\ UNCHANGED loopVariant

TallyQueryReplies(self) ==
  /\ pc[self] = "TallyQueryReplies"
  /\ \A pid \in sampleSet[self] :
       \E msg \in PendingQueryReplyMessage(self) : msg.src = pid
  /\ LET redTally ==  Cardinality({msg \in PendingQueryReplyMessage(self) :
                        /\ msg.src \in sampleSet[self] /\ msg.color = Red})
         blueTally == Cardinality({msg \in PendingQueryReplyMessage(self) :
                        /\ msg.src \in sampleSet[self] /\ msg.color = Blue})
     IN pick' = IF redTally >= PickFlipThreshold THEN [pick EXCEPT ![HostOf[self]] = Red]
               ELSE IF blueTally >= PickFlipThreshold THEN [pick EXCEPT ![HostOf[self]] = Blue]
               ELSE pick
  /\ message' = message \ {msg \in message : /\ msg.type = QueryReplyMessageType
                                        /\ msg.src \in sampleSet[self] /\ msg.dst = self}
  /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
  /\ loopVariant' = [loopVariant EXCEPT ![self] = loopVariant[self] + 1]
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]

SlushLoopTermination(self) ==
  /\ pc[self] = "SlushLoopTermination"
  /\ message' = message \cup {[type |-> TerminationMessageType, pid |-> self]}
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED << pick, sampleSet, loopVariant >>

SlushLoop(self) == RequireColorAssignment(self) \/ ExecuteSlushLoop(self)
                    \/ QuerySampleSet(self) \/ TallyQueryReplies(self)
                    \/ SlushLoopTermination(self)

ClientRequestLoop ==
  /\ pc["ClientRequest"] = "ClientRequestLoop"
  /\ pc' = [pc EXCEPT !["ClientRequest"] = IF \E n \in Node : pick[n] = NoColor
                                                THEN "AssignColorToNode" ELSE "Done"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

AssignColorToNode ==
  /\ pc["ClientRequest"] = "AssignColorToNode"
  /\ \E node \in Node : \E color \in Color :
       pick' = IF pick[node] = NoColor THEN [pick EXCEPT ![node] = color] ELSE pick
  /\ pc' = [pc EXCEPT !["ClientRequest"] = "ClientRequestLoop"]
  /\ UNCHANGED << message, sampleSet, loopVariant >>

ClientRequest == ClientRequestLoop \/ AssignColorToNode
Terminating == \A self \in ProcSet : pc[self] = "Done"

Next ==
  ClientRequest \/ (\E self \in SlushQueryProcess : SlushQuery(self))
                   \/ (\E self \in SlushLoopProcess : SlushLoop(self))
                   \/ Terminating

Spec == Init /\ [][Next]_vars
Termination == <>(\A self \in ProcSet : pc[self] = "Done")

====