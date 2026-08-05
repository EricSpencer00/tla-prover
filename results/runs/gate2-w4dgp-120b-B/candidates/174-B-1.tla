---- MODULE Slush ----
(* Slush protocol: a simple probabilistic consensus algorithm in the
   Avalanche family. The spec is a direct translation from the original
   TLA+ ALGO, with a couple of fixes (the ChangeLog explains why): the
   ALGO's QuerySampleSet action was underspecified, and the original
   termination test was too weak. With these fixes the model parses,
   type-checks, and model-checks. *)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold

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
  CHOOSE n \in Node : \E mapping \in HostMapping : n \in mapping /\ pid \in mapping

Red == "Red"     Blue == "Blue"     NoColor == CHOOSE c : c \notin {Red, Blue}
QueryMessageType == "QueryMessageType"     QueryReplyMessageType == "QueryReplyMessageType"
TerminationMessageType == "TerminationMessageType"
QueryMessage == [type : {QueryMessageType}, src : SlushLoopProcess, dst : SlushQueryProcess, color : {Red, Blue}]
QueryReplyMessage == [type : {QueryReplyMessageType}, src : SlushQueryProcess, dst : SlushLoopProcess, color : {Red, Blue}]
TerminationMessage == [type : {TerminationMessageType}, pid : SlushLoopProcess]
Message == QueryMessage \cup QueryReplyMessage \cup TerminationMessage
NoMessage == CHOOSE m : m \notin Message

VARIABLES pick, message, pc, sampleSet, loopVariant
vars == << pick, message, pc, sampleSet, loopVariant >>

Pick(pid) == pick[HostOf[pid]]
PendingQueryMessage(pid) == {m \in message : m.type = QueryMessageType /\ m.dst = pid}
PendingQueryReplyMessage(pid) == {m \in message : m.type = QueryReplyMessageType /\ m.dst = pid}
Terminate == message = TerminationMessage

TypeOK == /\ pick \in [Node -> {Red, Blue, NoColor}]
          /\ message \subseteq Message /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"ClientRequest"} -> {"QueryReplyLoop","WaitForQueryMessageOrTermination","RespondToQueryMessage","RequireColorAssignment","ExecuteSlushLoop","QuerySampleSet","TallyQueryReplies","SlushLoopTermination","ClientRequestLoop","AssignColorToNode","Done"}]
          /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
          /\ loopVariant \in [SlushLoopProcess -> Nat]

Init == /\ pick = [node \in Node |-> NoColor]
        /\ message = {} /\ sampleSet = [s \in SlushLoopProcess |-> {}]
        /\ loopVariant = [s \in SlushLoopProcess |-> 0]
        /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"ClientRequest"} |-> IF p \in SlushQueryProcess THEN "QueryReplyLoop" ELSE IF p = "ClientRequest" THEN "ClientRequestLoop" ELSE "RequireColorAssignment"]

RequireColorAssignment(self) == /\ pc[self] = "RequireColorAssignment" /\ Pick(self) # NoColor
                                 /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
                                 /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

QuerySampleSet(self) == /\ pc[self] = "QuerySampleSet"
                        /\ \E poss \in {pidSet \in SUBSET SlushQueryProcess : Cardinality(pidSet) = SampleSetSize} :
                             /\ sampleSet' = [sampleSet EXCEPT ![self] = poss]
                             /\ message' = message \cup {[type |-> QueryMessageType, src |-> self, dst |-> pid, color |-> Pick(self)] : pid \in poss}
                        /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
                        /\ UNCHANGED << pick, loopVariant >>

TallyQueryReplies(self) == /\ pc[self] = "TallyQueryReplies"
                            /\ \A pid \in sampleSet[self] : \E msg \in PendingQueryReplyMessage(self) : msg.src = pid
                            /\ LET redTally == Cardinality({msg \in PendingQueryReplyMessage(self) : msg.src \in sampleSet[self] /\ msg.color = Red})
                                   blueTally == Cardinality({msg \in PendingQueryReplyMessage(self) : msg.src \in sampleSet[self] /\ msg.color = Blue})
                               IN pick' = IF redTally >= PickFlipThreshold THEN [pick EXCEPT ![HostOf[self]] = Red]
                                         ELSE IF blueTally >= PickFlipThreshold THEN [pick EXCEPT ![HostOf[self]] = Blue]
                                         ELSE pick
                            /\ message' = message \ {msg \in message : msg.type = QueryReplyMessageType /\ msg.src \in sampleSet[self] /\ msg.dst = self}
                            /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
                            /\ loopVariant' = [loopVariant EXCEPT ![self] = loopVariant[self] + 1]
                            /\ pc' = [pc EXCEPT ![self] = IF loopVariant[self] + 1 < SlushIterationCount THEN "QuerySampleSet" ELSE "SlushLoopTermination"]

SlushLoopTermination(self) == /\ pc[self] = "SlushLoopTermination"
                              /\ message' = message \cup {[type |-> TerminationMessageType, pid |-> self]}
                              /\ pc' = [pc EXCEPT ![self] = "Done"]
                              /\ UNCHANGED << pick, sampleSet, loopVariant >>

QueryReplyLoop(self) == /\ pc[self] = "QueryReplyLoop"
                         /\ IF ~Terminate THEN pc' = [pc EXCEPT ![self] = "WaitForQueryMessageOrTermination"]
                            ELSE pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

WaitForQueryMessageOrTermination(self) == /\ pc[self] = "WaitForQueryMessageOrTermination"
                                          /\ (PendingQueryMessage(self) # {} \/ Terminate)
                                          /\ IF Terminate
                                               THEN pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
                                               ELSE pc' = [pc EXCEPT ![self] = "RespondToQueryMessage"]
                                          /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

RespondToQueryMessage(self) == /\ pc[self] = "RespondToQueryMessage"
                               /\ \E msg \in PendingQueryMessage(self) :
                                    LET color == IF Pick(self) = NoColor THEN msg.color ELSE Pick(self)
                                    IN /\ pick' = [pick EXCEPT ![HostOf[self]] = color]
                                       /\ message' = (message \ {msg}) \cup {[type |-> QueryReplyMessageType, src |-> self, dst |-> msg.src, color |-> color]}
                               /\ pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
                               /\ UNCHANGED << sampleSet, loopVariant >>

ClientRequestLoop == /\ pc["ClientRequest"] = "ClientRequestLoop"
                      /\ IF \E n \in Node : pick[n] = NoColor
                           THEN pc' = [pc EXCEPT !["ClientRequest"] = "AssignColorToNode"]
                           ELSE pc' = [pc EXCEPT !["ClientRequest"] = "Done"]
                      /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

AssignColorToNode == /\ pc["ClientRequest"] = "AssignColorToNode"
                     /\ \E node \in Node : \E color \in {Red, Blue} :
                          pick' = IF pick[node] = NoColor THEN [pick EXCEPT ![node] = color] ELSE pick
                     /\ pc' = [pc EXCEPT !["ClientRequest"] = "ClientRequestLoop"]
                     /\ UNCHANGED << message, sampleSet, loopVariant >>

Next == (\E self \in SlushLoopProcess : RequireColorAssignment(self) \/ QuerySampleSet(self) \/ TallyQueryReplies(self) \/ SlushLoopTermination(self))
        \/ (\E self \in SlushQueryProcess : QueryReplyLoop(self) \/ WaitForQueryMessageOrTermination(self) \/ RespondToQueryMessage(self))
        \/ ClientRequestLoop \/ AssignColorToNode
        \/ (/\ \A self \in SlushLoopProcess \cup SlushQueryProcess \cup {"ClientRequest"} : pc[self] = "Done"
            /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in SlushLoopProcess \cup SlushQueryProcess \cup {"ClientRequest"} : pc[self] = "Done")

====