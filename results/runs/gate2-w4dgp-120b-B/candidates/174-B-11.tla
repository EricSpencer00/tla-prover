---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess,
  HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold

ASSUME /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
       /\ Cardinality(Node) = Cardinality(SlushQueryProcess)
       /\ SlushIterationCount \in Nat /\ SampleSetSize \in Nat
       /\ PickFlipThreshold \in Nat
       /\ Cardinality(Node) = Cardinality(HostMapping)
       /\ \A m \in HostMapping :
            /\ Cardinality(m) = 3
            /\ \E e \in m : e \in Node
            /\ \E e \in m : e \in SlushLoopProcess
            /\ \E e \in m : e \in SlushQueryProcess

HostOf[pid \in SlushLoopProcess \cup SlushQueryProcess] ==
  CHOOSE n \in Node : \E m \in HostMapping : n \in m /\ pid \in m

Red == "Red"   Blue == "Blue"
Color == {Red, Blue}   NoColor == CHOOSE c : c \notin Color

QueryMessageType == "QueryMessageType"
QueryReplyMessageType == "QueryReplyMessageType"
TerminationMessageType == "TerminationMessageType"

QueryMessage == [type : {QueryMessageType}, src : SlushLoopProcess,
                 dst : SlushQueryProcess, color : Color]
QueryReplyMessage == [type : {QueryReplyMessageType}, src : SlushQueryProcess,
                      dst : SlushLoopProcess, color : Color]
TerminationMessage == [type : {TerminationMessageType}, pid : SlushLoopProcess]

Message == QueryMessage \cup QueryReplyMessage \cup TerminationMessage
NoMessage == CHOOSE m : m \notin Message

TypeInvariant ==
  /\ pick \in [Node -> Color \cup {NoColor}]
  /\ message \subseteq Message

PendingQueryMessage(pid) ==
  {m \in message : m.type = QueryMessageType /\ m.dst = pid}
PendingQueryReplyMessage(pid) ==
  {m \in message : m.type = QueryReplyMessageType /\ m.dst = pid}
Terminate == message = TerminationMessage
Pick(pid) == pick[HostOf[pid]]

VARIABLES pick, message, pc, sampleSet, loopVariant
vars == << pick, message, pc, sampleSet, loopVariant >>

Init ==
  /\ pick = [n \in Node |-> NoColor]
  /\ message = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"ClientRequest"} |
           IF p \in SlushQueryProcess THEN "QueryReplyLoop"
           ELSE IF p \in SlushLoopProcess THEN "RequireColorAssignment"
           ELSE "ClientRequestLoop"]
  /\ sampleSet = [self \in SlushLoopProcess |-> {}]
  /\ loopVariant = [self \in SlushLoopProcess |-> 0]

QueryReplyLoop(self) ==
  /\ pc[self] = "QueryReplyLoop"
  /\ pc' = [pc EXCEPT ![self] = IF ~Terminate THEN "WaitForQueryMessageOrTermination" ELSE "Done"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

WaitForQueryMessageOrTermination(self) ==
  /\ pc[self] = "WaitForQueryMessageOrTermination"
  /\ (PendingQueryMessage(self) # {} \/ Terminate)
  /\ pc' = [pc EXCEPT ![self] = IF Terminate THEN "QueryReplyLoop" ELSE "RespondToQueryMessage"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

RespondToQueryMessage(self) ==
  /\ pc[self] = "RespondToQueryMessage"
  /\ \E msg \in PendingQueryMessage(self) :
       LET color == IF Pick(self) = NoColor THEN msg.color ELSE Pick(self) IN
         /\ pick' = [pick EXCEPT ![HostOf[self]] = color]
         /\ message' = (message \ {msg}) \cup
                         {[type |-> QueryReplyMessageType, src |-> self, dst |-> msg.src,
                           color |-> color]}
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

QuerySampleSet(self) ==
  /\ pc[self] = "QuerySampleSet"
  /\ \E poss \in LET
                    others == Node \ {HostOf[self]}
                    qp == {q \in SlushQueryProcess : HostOf[q] \in others}
                  IN {s \in SUBSET qp : Cardinality(s) = SampleSetSize} :
       /\ sampleSet' = [sampleSet EXCEPT ![self] = poss]
       /\ message' = message \cup
            {[type |-> QueryMessageType, src |-> self, dst |-> pid, color |-> Pick(self)]
              : pid \in poss}
  /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
  /\ UNCHANGED << pick, loopVariant >>

TallyQueryReplies(self) ==
  /\ pc[self] = "TallyQueryReplies"
  /\ \A pid \in sampleSet[self] :
        \E msg \in PendingQueryReplyMessage(self) : msg.src = pid
  /\ LET redTally == Cardinality({msg \in PendingQueryReplyMessage(self) :
                                   msg.src \in sampleSet[self] /\ msg.color = Red})
         blueTally == Cardinality({msg \in PendingQueryReplyMessage(self) :
                                   msg.src \in sampleSet[self] /\ msg.color = Blue})
     IN pick' = [pick EXCEPT ![HostOf[self]] =
                    IF redTally >= PickFlipThreshold THEN Red
                    ELSE IF blueTally >= PickFlipThreshold THEN Blue
                    ELSE pick[HostOf[self]]]
  /\ message' = message \ {msg \in message : msg.type = QueryReplyMessageType
                            /\ msg.src \in sampleSet[self] /\ msg.dst = self}
  /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
  /\ loopVariant' = [loopVariant EXCEPT ![self] = loopVariant[self] + 1]
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]

SlushLoopTermination(self) ==
  /\ pc[self] = "SlushLoopTermination"
  /\ message' = message \cup {[type |-> TerminationMessageType, pid |-> self]}
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED << pick, sampleSet, loopVariant >>

ClientRequestLoop ==
  /\ pc["ClientRequest"] = "ClientRequestLoop"
  /\ pc' = [pc EXCEPT !["ClientRequest"] =
              IF \E n \in Node : pick[n] = NoColor THEN "AssignColorToNode" ELSE "Done"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

AssignColorToNode ==
  /\ pc["ClientRequest"] = "AssignColorToNode"
  /\ \E n \in Node, c \in Color :
       pick' = [pick EXCEPT ![n] = IF pick[n] = NoColor THEN c ELSE pick[n]]
  /\ pc' = [pc EXCEPT !["ClientRequest"] = "ClientRequestLoop"]
  /\ UNCHANGED << message, sampleSet, loopVariant >>

Terminating ==
  /\ \A self \in SlushLoopProcess \cup SlushQueryProcess \cup {"ClientRequest"} : pc[self] = "Done"
  /\ UNCHANGED vars

Next == (\E self \in SlushQueryProcess : QueryReplyLoop(self) \/ WaitForQueryMessageOrTermination(self) \/ RespondToQueryMessage(self))
        \/ (\E self \in SlushLoopProcess : RequireColorAssignment(self) \/ ExecuteSlushLoop(self)
                                         \/ QuerySampleSet(self) \/ TallyQueryReplies(self)
                                         \/ SlushLoopTermination(self))
        \/ ClientRequestLoop \/ AssignColorToNode \/ Terminating

Spec == Init /\ [][Next]_vars
Termination == <>(\A self \in SlushLoopProcess \cup SlushQueryProcess : pc[self] = "Done")
====