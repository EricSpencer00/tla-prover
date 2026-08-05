---- MODULE Slush ----
(**************************************************************************)
(* A specification of the Slush protocol, a simple probabilistic consensus   *)
(* algorithm in the Avalanche family.  TLA⁺ has no probabilistic modeling  *)
(* capability, so this spec is of limited utility -- it cannot answer      *)
(* questions like "what is the probability of not converging after N       *)
(* iterations?"  Those are answered in a language like PRISM.  This module  *)
(* exists merely as executable pseudocode.                                  *)
(**************************************************************************)

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

(*--algorithm Slush
variables pick = [node \in Node |-> NoColor], message = {};

define
  Red == "Red"
  Blue == "Blue"
  Color == {Red, Blue}
  NoColor == CHOOSE c : c \notin Color
  QueryMessageType == "QueryMessageType"
  QueryReplyMessageType == "QueryReplyMessageType"
  TerminationMessageType == "TerminationMessageType"
  QueryMessage == [type |-> QueryMessageType, src |-> SlushLoopProcess,
                   dst |-> SlushQueryProcess, color |-> Color]
  QueryReplyMessage == [type |-> QueryReplyMessageType, src |-> SlushQueryProcess,
                        dst |-> SlushLoopProcess, color |-> Color]
  TerminationMessage == [type |-> TerminationMessageType, pid |-> SlushLoopProcess]
  Message == QueryMessage \cup QueryReplyMessage \cup TerminationMessage
  NoMessage == CHOOSE m : m \notin Message
  TypeInvariant == /\ pick \in [Node -> Color \cup {NoColor}]
                    /\ message \subseteq Message
  PendingQueryMessage(pid) == {m \in message : m.type = QueryMessageType /\ m.dst = pid}
  PendingQueryReplyMessage(pid) == {m \in message : m.type = QueryReplyMessageType /\ m.dst = pid}
  Terminate == message = TerminationMessage
  Pick(pid) == pick[HostOf[pid]]
end define

process SlushQuery \in SlushQueryProcess begin
  QueryReplyLoop: while ~Terminate do
    WaitForQueryMessageOrTermination:
      await PendingQueryMessage(self) /= {} \/ Terminate;
      IF Terminate THEN goto QueryReplyLoop END;
    RespondToQueryMessage:
      with msg \in PendingQueryMessage(self), color = IF Pick(self) = NoColor THEN msg.color ELSE Pick(self) DO
        pick[HostOf[self]] := color;
        message := (message \ {msg}) \cup {[type |-> QueryReplyMessageType,
                                          src |-> self, dst |-> msg.src, color |-> color]}
      END WITH;
  END WHILE;
end process;

process SlushLoop \in SlushLoopProcess
variables sampleSet = {}, loopVariant = 0 begin
  RequireColorAssignment: await Pick(self) /= NoColor;
  ExecuteSlushLoop: while loopVariant < SlushIterationCount do
    QuerySampleSet: with possibleSampleSet \in
                      LET otherNodes == Node \ {HostOf[self]}
                          otherQueryProcesses == {pid \in SlushQueryProcess :
                                                   HostOf[pid] \in otherNodes}
                      IN {pidSet \in SUBSET otherQueryProcesses : Cardinality(pidSet) = SampleSetSize}
                    DO sampleSet := possibleSampleSet;
                       message := message \cup
                         {[type |-> QueryMessageType, src |-> self, dst |-> pid,
                           color |-> Pick(self)] : pid \in sampleSet} END;
    TallyQueryReplies: await /\ \A pid \in sampleSet : \E msg \in PendingQueryReplyMessage(self) : msg.src = pid
                         /\ LET redTally == Cardinality({msg \in PendingQueryReplyMessage(self) :
                                                         msg.src \in sampleSet /\ msg.color = Red})
                                blueTally == Cardinality({msg \in PendingQueryReplyMessage(self) :
                                                          msg.src \in sampleSet /\ msg.color = Blue})
                          IN IF redTally >= PickFlipThreshold THEN pick[HostOf[self]] := Red
                             ELSE IF blueTally >= PickFlipThreshold THEN pick[HostOf[self]] := Blue
                                  ELSE TRUE END;
                         message := message \ {msg \in PendingQueryReplyMessage(self) :
                                                 msg.src \in sampleSet /\ msg.dst = self};
                         sampleSet := {}; loopVariant := loopVariant + 1;
  END WHILE;
  SlushLoopTermination: message := message \cup {[type |-> TerminationMessageType, pid |-> self]}
end process;

process ClientRequest = "ClientRequest" begin
  ClientRequestLoop: while \E n \in Node : pick[n] = NoColor do
    AssignColorToNode: with node \in Node, color \in Color DO
                         IF pick[node] = NoColor THEN pick[node] := color END
                       END WITH
  END WHILE;
end process;
end algorithm;*)

\* BEGIN TRANSLATION

VARIABLES pick, message, pc, sampleSet, loopVariant

vars == << pick, message, pc, sampleSet, loopVariant >>

(* Shared definitions *)
Red == "Red"
Blue == "Blue"
Color == {Red, Blue}
NoColor == CHOOSE c : c \notin Color
QueryMessageType == "QueryMessageType"
QueryReplyMessageType == "QueryReplyMessageType"
TerminationMessageType == "TerminationMessageType"
QueryMessage == [type |-> QueryMessageType, src |-> SlushLoopProcess,
                 dst |-> SlushQueryProcess, color |-> Color]
QueryReplyMessage == [type |-> QueryReplyMessageType, src |-> SlushQueryProcess,
                      dst |-> SlushLoopProcess, color |-> Color]
TerminationMessage == [type |-> TerminationMessageType, pid |-> SlushLoopProcess]
Message == QueryMessage \cup QueryReplyMessage \cup TerminationMessage
NoMessage == CHOOSE m : m \notin Message
TypeInvariant == /\ pick \in [Node -> Color \cup {NoColor}]
                  /\ message \subseteq Message
PendingQueryMessage(pid) == {m \in message : m.type = QueryMessageType /\ m.dst = pid}
PendingQueryReplyMessage(pid) == {m \in message : m.type = QueryReplyMessageType /\ m.dst = pid}
Terminate == message = TerminationMessage
Pick(pid) == pick[HostOf[pid]]

ProcSet == SlushQueryProcess \cup SlushLoopProcess \cup {"ClientRequest"}

Init == /\ pick = [node \in Node |-> NoColor]
        /\ message = {}
        /\ sampleSet = [self \in SlushLoopProcess |-> {}]
        /\ loopVariant = [self \in SlushLoopProcess |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in SlushQueryProcess -> "QueryReplyLoop"
                                      [] self \in SlushLoopProcess -> "RequireColorAssignment"
                                      [] self = "ClientRequest" -> "ClientRequestLoop"]

(* SlushQuery ----------------------------------------------------------- *)
QueryReplyLoop(self) == /\ pc[self] = "QueryReplyLoop"
                         /\ IF ~Terminate THEN pc' = [pc EXCEPT ![self] = "WaitForQueryMessageOrTermination"]
                                                ELSE pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

WaitForQueryMessageOrTermination(self) == /\ pc[self] = "WaitForQueryMessageOrTermination"
                                          /\ PendingQueryMessage(self) /= {} \/ Terminate
                                          /\ IF Terminate
                                                THEN pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
                                                ELSE pc' = [pc EXCEPT ![self] = "RespondToQueryMessage"]
                                          /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

RespondToQueryMessage(self) == /\ pc[self] = "RespondToQueryMessage"
                               /\ \E msg \in PendingQueryMessage(self) :
                                    LET color == IF Pick(self) = NoColor THEN msg.color ELSE Pick(self) IN
                                      /\ pick' = [pick EXCEPT ![HostOf[self]] = color]
                                      /\ message' = (message \ {msg}) \cup
                                          {[type |-> QueryReplyMessageType, src |-> self,
                                            dst |-> msg.src, color |-> color]}
                               /\ pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
                               /\ UNCHANGED << sampleSet, loopVariant >>

SlushQuery(self) == QueryReplyLoop(self) \/ WaitForQueryMessageOrTermination(self) \/ RespondToQueryMessage(self)

(* SlushLoop ------------------------------------------------------------ *)
RequireColorAssignment(self) == /\ pc[self] = "RequireColorAssignment"
                                /\ Pick(self) /= NoColor
                                /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
                                /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

ExecuteSlushLoop(self) == /\ pc[self] = "ExecuteSlushLoop"
                          /\ IF loopVariant[self] < SlushIterationCount
                               THEN pc' = [pc EXCEPT ![self] = "QuerySampleSet"]
                               ELSE pc' = [pc EXCEPT ![self] = "SlushLoopTermination"]
                          /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

QuerySampleSet(self) == /\ pc[self] = "QuerySampleSet"
                         /\ \E possibleSampleSet \in LET otherNodes == Node \ {HostOf[self]}
                                                       otherQueryProcesses == {pid \in SlushQueryProcess : HostOf[pid] \in otherNodes}
                                                   IN {pidSet \in SUBSET otherQueryProcesses : Cardinality(pidSet) = SampleSetSize} :
                              /\ sampleSet' = [sampleSet EXCEPT ![self] = possibleSampleSet]
                              /\ message' = message \cup {[type |-> QueryMessageType, src |-> self,
                                                          dst |-> pid, color |-> Pick(self)] : pid \in possibleSampleSet}
                         /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
                         /\ UNCHANGED << pick, loopVariant >>

TallyQueryReplies(self) == /\ pc[self] = "TallyQueryReplies"
                            /\ \A pid \in sampleSet[self] :
                                 \E msg \in PendingQueryReplyMessage(self) : msg.src = pid
                            /\ LET redTally == Cardinality({msg \in PendingQueryReplyMessage(self) :
                                                             msg.src \in sampleSet[self] /\ msg.color = Red})
                                   blueTally == Cardinality({msg \in PendingQueryReplyMessage(self) :
                                                              msg.src \in sampleSet[self] /\ msg.color = Blue})
                               IN IF redTally >= PickFlipThreshold
                                      THEN pick' = [pick EXCEPT ![HostOf[self]] = Red]
                                      ELSE IF blueTally >= PickFlipThreshold
                                             THEN pick' = [pick EXCEPT ![HostOf[self]] = Blue]
                                             ELSE pick' = pick
                            /\ message' = message \ {msg \in PendingQueryReplyMessage(self) :
                                                      msg.src \in sampleSet[self] /\ msg.dst = self}
                            /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
                            /\ loopVariant' = [loopVariant EXCEPT ![self] = loopVariant[self] + 1]
                            /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]

SlushLoopTermination(self) == /\ pc[self] = "SlushLoopTermination"
                              /\ message' = message \cup {[type |-> TerminationMessageType, pid |-> self]}
                              /\ pc' = [pc EXCEPT ![self] = "Done"]
                              /\ UNCHANGED << pick, sampleSet, loopVariant >>

SlushLoop(self) == RequireColorAssignment(self) \/ ExecuteSlushLoop(self)
                       \/ QuerySampleSet(self) \/ TallyQueryReplies(self)
                       \/ SlushLoopTermination(self)

(* ClientRequest -------------------------------------------------------- *)
ClientRequestLoop == /\ pc["ClientRequest"] = "ClientRequestLoop"
                      /\ IF \E n \in Node : pick[n] = NoColor
                            THEN pc' = [pc EXCEPT !["ClientRequest"] = "AssignColorToNode"]
                            ELSE pc' = [pc EXCEPT !["ClientRequest"] = "Done"]
                      /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

AssignColorToNode == /\ pc["ClientRequest"] = "AssignColorToNode"
                     /\ \E node \in Node, color \in Color :
                          /\ IF pick[node] = NoColor THEN pick' = [pick EXCEPT ![node] = color] ELSE pick' = pick
                          /\ pc' = [pc EXCEPT !["ClientRequest"] = "ClientRequestLoop"]
                     /\ UNCHANGED << message, sampleSet, loopVariant >>

ClientRequest == ClientRequestLoop \/ AssignColorToNode

(* Allow infinite stuttering on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars
Next == ClientRequest \/ (\E self \in SlushQueryProcess : SlushQuery(self))
                      \/ (\E self \in SlushLoopProcess : SlushLoop(self)) \/ Terminating
Spec == Init /\ [][Next]_vars

(* Termination is reachable; the model need not explore to a deadlock. *)
Termination == <>(\A self \in ProcSet : pc[self] = "Done")
====