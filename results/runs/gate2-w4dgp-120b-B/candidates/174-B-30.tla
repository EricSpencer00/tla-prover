---- MODULE Slush ----------------------------------------------------------------
(**************************************************************************)
(* A specification of the Slush protocol, a very simple probabilistic     *)
(* consensus algorithm in the Avalanche family. Because TLA⁺ has no        *)
(* probabilistic modeling capabilities, this spec is of limited utility    *)
(* beyond serving as executable pseudocode. It models the basic steps of   *)
(* Slush -- sampling, polling, and quorum vote-flipping -- but it cannot    *)
(* model the probability distribution of outcomes directly.                *)
(**************************************************************************)

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
       /\ Cardinality(Node) = Cardinality(HostMapping)
       /\ \A mapping \in HostMapping :
            /\ Cardinality(mapping) = 3
            /\ \E e \in mapping : e \in Node
            /\ \E e \in mapping : e \in SlushLoopProcess
            /\ \E e \in mapping : e \in SlushQueryProcess

HostOf[pid \in SlushLoopProcess \cup SlushQueryProcess] ==
  CHOOSE n \in Node :
    /\ \E mapping \in HostMapping :
         /\ n \in mapping
         /\ pid \in mapping

Red == "Red"
Blue == "Blue"
Color == {Red, Blue}
NoColor == CHOOSE c \in Color : FALSE
QueryMessageType == "QueryMessageType"
QueryReplyMessageType == "QueryReplyMessageType"
TerminationMessageType == "TerminationMessageType"

QueryMessage == [type : {QueryMessageType}, src : SlushLoopProcess,
                 dst : SlushQueryProcess, color : Color]
QueryReplyMessage == [type : {QueryReplyMessageType}, src : SlushQueryProcess,
                      dst : SlushLoopProcess, color : Color]
TerminationMessage == [type : {TerminationMessageType}, pid : SlushLoopProcess]

Message == QueryMessage \cup QueryReplyMessage \cup TerminationMessage
NoMessage == CHOOSE m \in Message : FALSE

Pick(pid) == pick[HostOf[pid]]

TypeInvariant ==
  /\ pick \in [Node -> Color \cup {NoColor}]
  /\ message \subseteq Message

PendingQueryMessage(pid) ==
  {m \in message : m.type = QueryMessageType /\ m.dst = pid}
PendingQueryReplyMessage(pid) ==
  {m \in message : m.type = QueryReplyMessageType /\ m.dst = pid}
Terminate == message = TerminationMessage

VARIABLES pick, message, pc, sampleSet, loopVariant
vars == << pick, message, pc, sampleSet, loopVariant >>
ProcSet == SlushQueryProcess \cup SlushLoopProcess \cup {"ClientRequest"}

Init ==
  /\ pick = [node \in Node |-> NoColor]
  /\ message = {}
  /\ sampleSet = [self \in SlushLoopProcess |-> {}]
  /\ loopVariant = [self \in SlushLoopProcess |-> 0]
  /\ pc = [self \in ProcSet |-> CASE self \in SlushQueryProcess -> "QueryReplyLoop"
                                 [] self \in SlushLoopProcess -> "RequireColorAssignment"
                                 [] self = "ClientRequest" -> "ClientRequestLoop"]

QueryReplyLoop(self) ==
  /\ pc[self] = "QueryReplyLoop"
  /\ IF ~Terminate
       THEN /\ pc' = [pc EXCEPT ![self] = "WaitForQueryMessageOrTermination"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

\* Await a request from a loop process or a termination broadcast.
WaitForQueryMessageOrTermination(self) ==
  /\ pc[self] = "WaitForQueryMessageOrTermination"
  /\ PendingQueryMessage(self) /= {} \/ Terminate
  /\ IF Terminate
       THEN /\ pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "RespondToQueryMessage"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

\* Reply to a query with our own pick if set, else repeat the queryer's.
RespondToQueryMessage(self) ==
  /\ pc[self] = "RespondToQueryMessage"
  /\ \E msg \in PendingQueryMessage(self) :
       LET color == IF Pick(self) = NoColor THEN msg.color ELSE Pick(self) IN
         /\ pick' = [pick EXCEPT ![HostOf[self]] = color]
         /\ message' = (message \ {msg}) \cup
                       {[type |-> QueryReplyMessageType, src |-> self,
                         dst |-> msg.src, color |-> color]}
  /\ pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
  /\ UNCHANGED << sampleSet, loopVariant >>

\* A loop process may only begin after it has chosen a color.
RequireColorAssignment(self) ==
  /\ pc[self] = "RequireColorAssignment"
  /\ Pick(self) /= NoColor
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

ExecuteSlushLoop(self) ==
  /\ pc[self] = "ExecuteSlushLoop"
  /\ IF loopVariant[self] < SlushIterationCount
       THEN /\ pc' = [pc EXCEPT ![self] = "QuerySampleSet"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "SlushLoopTermination"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

QuerySampleSet(self) ==
  /\ pc[self] = "QuerySampleSet"
  /\ \E possibleSampleSet \in
        {pidSet \in SUBSET SlushQueryProcess :
           /\ \A pid \in pidSet : HostOf[pid] # HostOf[self]
           /\ Cardinality(pidSet) = SampleSetSize} :
         /\ sampleSet' = [sampleSet EXCEPT ![self] = possibleSampleSet]
         /\ message' = message \cup
                       {[type |-> QueryMessageType, src |-> self,
                         dst |-> pid, color |-> Pick(self)] :
                         pid \in sampleSet'[self]}
  /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
  /\ UNCHANGED << pick, loopVariant >>

\* Await and tally replies from the sample set; flip our own pick if a quorum is reached.
TallyQueryReplies(self) ==
  /\ pc[self] = "TallyQueryReplies"
  /\ \A pid \in sampleSet[self] :
       \E msg \in PendingQueryReplyMessage(self) : msg.src = pid
  /\ LET redTally ==
         Cardinality({msg \in PendingQueryReplyMessage(self) :
                        /\ msg.src \in sampleSet[self] /\ msg.color = Red})
       blueTally ==
         Cardinality({msg \in PendingQueryReplyMessage(self) :
                        /\ msg.src \in sampleSet[self] /\ msg.color = Blue})
     IN pick' = IF redTally >= PickFlipThreshold
                   THEN [pick EXCEPT ![HostOf[self]] = Red]
                   ELSE IF blueTally >= PickFlipThreshold
                          THEN [pick EXCEPT ![HostOf[self]] = Blue]
                          ELSE pick
  /\ message' = message \ {msg \in message :
         /\ msg.type = QueryReplyMessageType
         /\ msg.src \in sampleSet[self]
         /\ msg.dst = self}
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
  /\ IF \E n \in Node : pick[n] = NoColor
       THEN pc' = [pc EXCEPT !["ClientRequest"] = "AssignColorToNode"]
       ELSE pc' = [pc EXCEPT !["ClientRequest"] = "Done"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

AssignColorToNode ==
  /\ pc["ClientRequest"] = "AssignColorToNode"
  /\ \E node \in Node, color \in Color :
       pick' = IF pick[node] = NoColor
                 THEN [pick EXCEPT ![node] = color]
                 ELSE pick
  /\ pc' = [pc EXCEPT !["ClientRequest"] = "ClientRequestLoop"]
  /\ UNCHANGED << message, sampleSet, loopVariant >>

\* Allow infinite stuttering once every process has settled.
Terminating == (\A self \in ProcSet : pc[self] = "Done") /\ UNCHANGED vars

Next == ClientRequestLoop \/ AssignColorToNode
        \/ (\E self \in SlushQueryProcess : QueryReplyLoop(self)
                                      \/ WaitForQueryMessageOrTermination(self)
                                      \/ RespondToQueryMessage(self))
        \/ (\E self \in SlushLoopProcess : RequireColorAssignment(self)
                                         \/ ExecuteSlushLoop(self)
                                         \/ QuerySampleSet(self)
                                         \/ TallyQueryReplies(self)
                                         \/ SlushLoopTermination(self))
        \/ Terminating

Spec == Init /\ [][Next]_vars
Termination == <>(\A self \in ProcSet : pc[self] = "Done")
====