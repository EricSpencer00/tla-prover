---- MODULE Slush ----------------------------------------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold

ASSUME /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
       /\ Cardinality(Node) = Cardinality(SlushQueryProcess)
       /\ SlushIterationCount \in Nat
       /\ SampleSetSize \in Nat /\ PickFlipThreshold \in Nat
       /\ Cardinality(Node) = Cardinality(HostMapping)
       /\ \A mapping \in HostMapping :
            /\ Cardinality(mapping) = 3
            /\ \E e \in mapping : e \in Node
            /\ \E e \in mapping : e \in SlushLoopProcess
            /\ \E e \in mapping : e \in SlushQueryProcess

HostOf[pid \in SlushLoopProcess \cup SlushQueryProcess] ==
  CHOOSE n \in Node : \E mapping \in HostMapping : n \in mapping /\ pid \in mapping

Red == "Red"   Blue == "Blue"
Color == {Red, Blue}
NoColor == CHOOSE c : c \notin Color
QueryMessageType == "QueryMessageType"
QueryReplyMessageType == "QueryReplyMessageType"
TerminationMessageType == "TerminationMessageType"

QueryMessage == [type : {QueryMessageType}, src : SlushLoopProcess,
                 dst : SlushQueryProcess, color : Color]
QueryReplyMessage == [type : {QueryReplyMessageType},
                      src : SlushQueryProcess, dst : SlushLoopProcess,
                      color : Color]
TerminationMessage == [type : {TerminationMessageType}, pid : SlushLoopProcess]

Message == QueryMessage \cup QueryReplyMessage \cup TerminationMessage
NoMessage == CHOOSE m : m \notin Message

Pick(pid) == pick[HostOf[pid]]
Terminate == message = TerminationMessage
PendingQueryMessage(pid) == {m \in message : m.type = QueryMessageType /\ m.dst = pid}
PendingQueryReplyMessage(pid) == {m \in message : m.type = QueryReplyMessageType /\ m.dst = pid}

VARIABLES pick, message, pc, sampleSet, loopVariant
vars == << pick, message, pc, sampleSet, loopVariant >>
ProcSet == SlushLoopProcess \cup SlushQueryProcess \cup {"ClientRequest"}

Init ==
  /\ pick = [n \in Node |-> NoColor]
  /\ message = {}
  /\ pc = [self \in ProcSet |->
           IF self \in SlushQueryProcess THEN "QueryReplyLoop"
           ELSE IF self \in SlushLoopProcess THEN "RequireColorAssignment"
           ELSE "ClientRequestLoop"]
  /\ sampleSet = [self \in SlushLoopProcess |-> {}]
  /\ loopVariant = [self \in SlushLoopProcess |-> 0]

SlushQuery(self) ==
  \/ /\ pc[self] = "QueryReplyLoop"
     /\ IF ~Terminate THEN pc' = [pc EXCEPT ![self] = "WaitForQueryMessageOrTermination"]
        ELSE pc' = [pc EXCEPT ![self] = "Done"]
     /\ UNCHANGED << pick, message, sampleSet, loopVariant >>
  \/ /\ pc[self] = "WaitForQueryMessageOrTermination"
     /\ (PendingQueryMessage(self) # {} \/ Terminate)
     /\ IF Terminate THEN pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
        ELSE pc' = [pc EXCEPT ![self] = "RespondToQueryMessage"]
     /\ UNCHANGED << pick, message, sampleSet, loopVariant >>
  \/ /\ pc[self] = "RespondToQueryMessage"
     /\ \E msg \in PendingQueryMessage(self) :
          LET color == IF Pick(self) = NoColor THEN msg.color ELSE Pick(self) IN
            /\ pick' = [pick EXCEPT ![HostOf[self]] = color]
            /\ message' = (message \ {msg}) \cup
                 {[type |-> QueryReplyMessageType, src |-> self,
                   dst |-> msg.src, color |-> color]}
     /\ pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
     /\ UNCHANGED << sampleSet, loopVariant >>

RequireColorAssignment(self) ==
  /\ pc[self] = "RequireColorAssignment" /\ Pick(self) # NoColor
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

ExecuteSlushLoop(self) ==
  /\ pc[self] = "ExecuteSlushLoop"
  /\ IF loopVariant[self] < SlushIterationCount
       THEN pc' = [pc EXCEPT ![self] = "QuerySampleSet"]
       ELSE pc' = [pc EXCEPT ![self] = "SlushLoopTermination"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

QuerySampleSet(self) ==
  /\ pc[self] = "QuerySampleSet"
  /\ \E possibleSampleSet \in
       LET otherNodes == Node \ {HostOf[self]}
           otherQuery == {p \in SlushQueryProcess : HostOf[p] \in otherNodes}
       IN {S \in SUBSET otherQuery : Cardinality(S) = SampleSetSize}:
        sampleSet' = [sampleSet EXCEPT ![self] = possibleSampleSet]
        /\ message' = message \cup
             {[type |-> QueryMessageType, src |-> self, dst |-> pid,
               color |-> Pick(self)] : pid \in possibleSampleSet}
  /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
  /\ UNCHANGED << pick, loopVariant >>

TallyQueryReplies(self) ==
  /\ pc[self] = "TallyQueryReplies"
  /\ \A pid \in sampleSet[self] : \E msg \in PendingQueryReplyMessage(self) : msg.src = pid
  /\ LET red == Cardinality({msg \in PendingQueryReplyMessage(self) :
                              /\ msg.src \in sampleSet[self] /\ msg.color = Red})
         blue == Cardinality({msg \in PendingQueryReplyMessage(self) :
                               /\ msg.src \in sampleSet[self] /\ msg.color = Blue})
     IN pick' = IF red >= PickFlipThreshold
                   THEN [pick EXCEPT ![HostOf[self]] = Red]
                   ELSE IF blue >= PickFlipThreshold
                     THEN [pick EXCEPT ![HostOf[self]] = Blue] ELSE pick
  /\ message' = message \ {msg \in message :
                            /\ msg.type = QueryReplyMessageType
                            /\ msg.src \in sampleSet[self] /\ msg.dst = self}
  /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
  /\ loopVariant' = [loopVariant EXCEPT ![self] = loopVariant[self] + 1]
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]

SlushLoopTermination(self) ==
  /\ pc[self] = "SlushLoopTermination"
  /\ message' = message \cup {[type |-> TerminationMessageType, pid |-> self]}
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED << pick, sampleSet, loopVariant >>

SlushLoop(self) ==
  RequireColorAssignment(self) \/ ExecuteSlushLoop(self) \/ QuerySampleSet(self)
    \/ TallyQueryReplies(self) \/ SlushLoopTermination(self)

ClientRequest ==
  \/ /\ pc["ClientRequest"] = "ClientRequestLoop" /\ \E n \in Node : pick[n] = NoColor
       /\ pc' = [pc EXCEPT !["ClientRequest"] = "AssignColorToNode"] /\ UNCHANGED vars
  \/ /\ pc["ClientRequest"] = "ClientRequestLoop" /\ ~\E n \in Node : pick[n] = NoColor
       /\ pc' = [pc EXCEPT !["ClientRequest"] = "Done"] /\ UNCHANGED vars
  \/ /\ pc["ClientRequest"] = "AssignColorToNode"
       /\ pc' = [pc EXCEPT !["ClientRequest"] = "ClientRequestLoop"]
       /\ \E n \in Node, c \in Color :
            pick' = IF pick[n] = NoColor THEN [pick EXCEPT ![n] = c] ELSE pick
       /\ UNCHANGED << message, sampleSet, loopVariant >>

Terminating == \A self \in ProcSet : pc[self] = "Done" /\ UNCHANGED vars
Next == ClientRequest \/ (\E self \in SlushLoopProcess : SlushLoop(self))
            \/ (\E self \in SlushQueryProcess : SlushQuery(self)) \/ Terminating

Spec == Init /\ [][Next]_vars
Termination == <>(\A self \in ProcSet : pc[self] = "Done")
====