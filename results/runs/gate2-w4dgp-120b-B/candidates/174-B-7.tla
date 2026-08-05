---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold

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
  CHOOSE n \in Node : \E mapping \in HostMapping : n \in mapping /\ pid \in mapping

(*--algorithm Slush
variables pick = [n \in Node |-> NoColor];
message = {};

define
  Red == "Red"
  Blue == "Blue"
  Color == {Red, Blue}
  NoColor == CHOOSE c : c \notin Color
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
  PendingQueryMessage(pid) == {m \in message : m.type = QueryMessageType /\ m.dst = pid}
  PendingQueryReplyMessage(pid) == {m \in message : m.type = QueryReplyMessageType /\ m.dst = pid}
  Terminate == message = TerminationMessage
  Pick(pid) == pick[HostOf[pid]]
end define

process SlushQuery \in SlushQueryProcess begin
  QueryReplyLoop: while ~Terminate do
    WaitForQueryMessageOrTermination: await PendingQueryMessage(self) /= {} \/ Terminate;
      IF Terminate THEN goto QueryReplyLoop END IF;
    RespondToQueryMessage: with msg \in PendingQueryMessage(self),
      color = IF Pick(self) = NoColor THEN msg.color ELSE Pick(self) DO
        pick[HostOf[self]] := color;
        message := (message \ {msg}) \cup {[type |-> QueryReplyMessageType, src |-> self,
                                          dst |-> msg.src, color |-> color]}
      END WITH
  end while;
end process;

process SlushLoop \in SlushLoopProcess variables sampleSet = {}, loopVariant = 0 begin
  RequireColorAssignment: await Pick(self) /= NoColor;
  ExecuteSlushLoop: while loopVariant < SlushIterationCount do
    QuerySampleSet: with possibleSampleSet \in
        {ps \in SUBSET SlushQueryProcess :
          Cardinality(ps) = SampleSetSize /\ \A pid \in ps : HostOf[pid] # HostOf[self]} DO
          sampleSet := possibleSampleSet;
          message := message \cup {[type |-> QueryMessageType, src |-> self, dst |-> pid,
                                    color |-> Pick(self)] : pid \in sampleSet}
      END WITH;
    TallyQueryReplies: await \A pid \in sampleSet :
        \E msg \in PendingQueryReplyMessage(self) : msg.src = pid;
      with redTally = Cardinality({msg \in PendingQueryReplyMessage(self) :
                                     msg.src \in sampleSet /\ msg.color = Red}),
           blueTally = Cardinality({msg \in PendingQueryReplyMessage(self) :
                                      msg.src \in sampleSet /\ msg.color = Blue}) DO
           IF redTally >= PickFlipThreshold THEN pick[HostOf[self]] := Red
           ELSE IF blueTally >= PickFlipThreshold THEN pick[HostOf[self]] := Blue
           ELSE UNCHANGED pick
           END IF
      END WITH;
      message := message \ {msg \in message : msg.type = QueryReplyMessageType
                                  /\ msg.src \in sampleSet /\ msg.dst = self};
      sampleSet := {}; loopVariant := loopVariant + 1;
  end while;
  SlushLoopTermination: message := message \cup {[type |-> TerminationMessageType, pid |-> self]}
end process;

process ClientRequest = "ClientRequest" begin
  ClientRequestLoop: while \E n \in Node : pick[n] = NoColor DO
    AssignColorToNode: with node \in Node, color \in Color DO IF pick[node] = NoColor
                          THEN pick := [pick EXCEPT ![node] = color] END IF END WITH
  end while
end process;
end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES pick, message, pc, sampleSet, loopVariant

Red == "Red"
Blue == "Blue"
Color == {Red, Blue}
NoColor == CHOOSE c : c \notin Color
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
TypeInvariant == /\ pick \in [Node -> Color \cup {NoColor}]
                  /\ message \subseteq Message
PendingQueryMessage(pid) == {m \in message : m.type = QueryMessageType /\ m.dst = pid}
PendingQueryReplyMessage(pid) == {m \in message : m.type = QueryReplyMessageType /\ m.dst = pid}
Terminate == message = TerminationMessage
Pick(pid) == pick[HostOf[pid]]

vars == << pick, message, pc, sampleSet, loopVariant >>
ProcSet == SlushQueryProcess \cup SlushLoopProcess \cup {"ClientRequest"}

Init == /\ pick = [n \in Node |-> NoColor]
        /\ message = {}
        /\ sampleSet = [s \in SlushLoopProcess |-> {}]
        /\ loopVariant = [s \in SlushLoopProcess |-> 0]
        /\ pc = [p \in ProcSet |-> CASE p \in SlushQueryProcess -> "QueryReplyLoop"
                                      [] p \in SlushLoopProcess -> "RequireColorAssignment"
                                      [] p = "ClientRequest" -> "ClientRequestLoop"]

QueryReplyLoop(s) == /\ pc[s] = "QueryReplyLoop"
                      /\ IF ~Terminate THEN pc' = [pc EXCEPT ![s] = "WaitForQueryMessageOrTermination"]
                                           ELSE pc' = [pc EXCEPT ![s] = "Done"]
                      /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

WaitForQueryMessageOrTermination(s) == /\ pc[s] = "WaitForQueryMessageOrTermination"
                                      /\ PendingQueryMessage(s) /= {} \/ Terminate
                                      /\ pc' = [pc EXCEPT ![s] = IF Terminate THEN "QueryReplyLoop"
                                                                     ELSE "RespondToQueryMessage"]
                                      /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

RespondToQueryMessage(s) == /\ pc[s] = "RespondToQueryMessage"
                            /\ \E msg \in PendingQueryMessage(s) :
                                 LET col == IF Pick(s) = NoColor THEN msg.color ELSE Pick(s) IN
                                   /\ pick' = [pick EXCEPT ![HostOf[s]] = col]
                                   /\ message' = (message \ {msg}) \cup {[type |-> QueryReplyMessageType,
                                                                        src |-> s, dst |-> msg.src,
                                                                        color |-> col]}
                            /\ pc' = [pc EXCEPT ![s] = "QueryReplyLoop"]
                            /\ UNCHANGED << sampleSet, loopVariant >>

SlushQuery(s) == QueryReplyLoop(s) \/ WaitForQueryMessageOrTermination(s)
                 \/ RespondToQueryMessage(s)

RequireColorAssignment(s) == /\ pc[s] = "RequireColorAssignment"
                             /\ Pick(s) /= NoColor
                             /\ pc' = [pc EXCEPT ![s] = "ExecuteSlushLoop"]
                             /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

ExecuteSlushLoop(s) == /\ pc[s] = "ExecuteSlushLoop"
                        /\ pc' = [pc EXCEPT ![s] = IF loopVariant[s] < SlushIterationCount
                                                       THEN "QuerySampleSet" ELSE "SlushLoopTermination"]
                        /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

QuerySampleSet(s) == /\ pc[s] = "QuerySampleSet"
                      /\ \E ps \in {ps \in SUBSET SlushQueryProcess :
                                      Cardinality(ps) = SampleSetSize /\ \A pid \in ps : HostOf[pid] # HostOf[s]} :
                         /\ sampleSet' = [sampleSet EXCEPT ![s] = ps]
                         /\ message' = message \cup {[type |-> QueryMessageType, src |-> s,
                                                      dst |-> pid, color |-> Pick(s)] : pid \in ps}
                      /\ pc' = [pc EXCEPT ![s] = "TallyQueryReplies"]
                      /\ UNCHANGED << pick, loopVariant >>

TallyQueryReplies(s) == /\ pc[s] = "TallyQueryReplies"
                         /\ \A pid \in sampleSet[s] :
                            \E msg \in PendingQueryReplyMessage(s) : msg.src = pid
                         /\ LET red == Cardinality({msg \in PendingQueryReplyMessage(s) :
                                                    msg.src \in sampleSet[s] /\ msg.color = Red})
                                blue == Cardinality({msg \in PendingQueryReplyMessage(s) :
                                                     msg.src \in sampleSet[s] /\ msg.color = Blue})
                                nps == IF red >= PickFlipThreshold THEN Red
                                       ELSE IF blue >= PickFlipThreshold THEN Blue
                                       ELSE "NoPick"
                            IN pick' = IF nps = "NoPick" THEN pick
                                       ELSE [pick EXCEPT ![HostOf[s]] = nps]
                         /\ message' = message \ {msg \in message :
                                                     msg.type = QueryReplyMessageType /\ msg.src \in sampleSet[s]
                                                     /\ msg.dst = s}
                         /\ sampleSet' = [sampleSet EXCEPT ![s] = {}]
                         /\ loopVariant' = [loopVariant EXCEPT ![s] = loopVariant[s] + 1]
                         /\ pc' = [pc EXCEPT ![s] = "ExecuteSlushLoop"]

SlushLoopTermination(s) == /\ pc[s] = "SlushLoopTermination"
                            /\ message' = message \cup {[type |-> TerminationMessageType, pid |-> s]}
                            /\ pc' = [pc EXCEPT ![s] = "Done"]
                            /\ UNCHANGED << pick, sampleSet, loopVariant >>

SlushLoop(s) == RequireColorAssignment(s) \/ ExecuteSlushLoop(s) \/ QuerySampleSet(s)
                \/ TallyQueryReplies(s) \/ SlushLoopTermination(s)

ClientRequestLoop == /\ pc["ClientRequest"] = "ClientRequestLoop"
                      /\ pc' = IF \E n \in Node : pick[n] = NoColor
                               THEN [pc EXCEPT !["ClientRequest"] = "AssignColorToNode"]
                               ELSE [pc EXCEPT !["ClientRequest"] = "Done"]
                      /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

AssignColorToNode == /\ pc["ClientRequest"] = "AssignColorToNode"
                     /\ \E node \in Node, color \in Color :
                          pick' = IF pick[node] = NoColor THEN [pick EXCEPT ![node] = color] ELSE pick
                     /\ pc' = [pc EXCEPT !["ClientRequest"] = "ClientRequestLoop"]
                     /\ UNCHANGED << message, sampleSet, loopVariant >>

ClientRequest == ClientRequestLoop \/ AssignColorToNode

Terminating == /\ \A p \in ProcSet : pc[p] = "Done"
               /\ UNCHANGED vars

Next == ClientRequest
        \/ (\E s \in SlushQueryProcess : SlushQuery(s))
        \/ (\E s \in SlushLoopProcess : SlushLoop(s))
        \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A p \in ProcSet : pc[p] = "Done")
====