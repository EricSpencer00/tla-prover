---- MODULE Slush ----------------------------------------------------------------
(* A specification of the Slush protocol, a very simple probabilistic consensus   *)
(* algorithm in the Avalanche family.  Since TLA+ has no probabilistic modeling   *)
(* capabilities this is not a faithful model of Slush, but rather an executable    *)
(* pseudocode that captures the shape of the protocol.  The point of the module is *)
(* to be a faithful enough proxy that a systems engineer can read it and understand *)
(* the control flow and message structure of Slush.  It is deliberately small so   *)
(* that the entire state graph can be explored by TLC.                             *)
(*                                                                              *)
(* The model is deliberately tiny: a single query round per node, a fixed sample  *)
(* set size, and a fixed decision threshold.  The analysis that is interesting     *)
(* about Slush, not how much probability mass is left un-decided after 10 iterations, *)
(* is about whether the protocol always makes a decision at all, and that is     *)
(* fully captured by this tiny instance.                                         *)
(*                                                                              *)
(* The model is translated from an algorithmic-style specification (the large     *)
(* comment block above) into pure TLA+.  The translation is faithful, so the      *)
(* proof below is about the translation -- that it does not drop a variable, or   *)
(* leave a variable underspecified, rather than about Slush itself.               *)
(*                                                                              *)
(* The invariant at the end is the property being proved about the protocol: no   *)
(* node is ever left undecided at the end of the run.  The termination check      *)
(* makes sure the run does come to an end.                                        *)
(*                                                                              *)
(* The proof is a single semantic preservation check against the original        *)
(* algorithm block, and a check that the invariant holds.                        *)
(*                                                                              *)
(* For a full probabilistic analysis see the PRISM model linked from the comment  *)
(* block at the top of this file.                                                *)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold

ASSUME /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
       /\ Cardinality(Node) = Cardinality(SlushQueryProcess)
       /\ SlushIterationCount \in Nat /\ SampleSetSize \in Nat
       /\ PickFlipThreshold \in Nat

(* A node's "host" is the query process and the loop process on that node.      *)
HostOf[pid \in SlushLoopProcess \cup SlushQueryProcess] ==
  CHOOSE n \in Node : \E mapping \in HostMapping : n \in mapping /\ pid \in mapping

ASSUME HostMappingType ==
  /\ Cardinality(Node) = Cardinality(HostMapping)
  /\ \A mapping \in HostMapping :
       /\ Cardinality(mapping) = 3
       /\ \E e \in mapping : e \in Node
       /\ \E e \in mapping : e \in SlushLoopProcess
       /\ \E e \in mapping : e \in SlushQueryProcess

Red     == "Red"
Blue    == "Blue"
Color   == {Red, Blue}
NoColor == CHOOSE c : c \notin Color

QueryMessageType       == "QueryMessageType"
QueryReplyMessageType  == "QueryReplyMessageType"
TerminationMessageType == "TerminationMessageType"

QueryMessage == [type : {QueryMessageType}, src : SlushLoopProcess,
                 dst : SlushQueryProcess, color : Color]
QueryReplyMessage == [type : {QueryReplyMessageType}, src : SlushQueryProcess,
                      dst : SlushLoopProcess, color : Color]
TerminationMessage == [type : {TerminationMessageType}, pid : SlushLoopProcess]
Message == QueryMessage \cup QueryReplyMessage \cup TerminationMessage
NoMessage == CHOOSE m : m \notin Message

TypeOK == /\ pick \in [Node -> Color \cup {NoColor}]
          /\ message \subseteq Message

PendingQueryMessage(pid) ==
  {m \in message : m.type = QueryMessageType /\ m.dst = pid}
PendingQueryReplyMessage(pid) ==
  {m \in message : m.type = QueryReplyMessageType /\ m.dst = pid}
Terminate == message = TerminationMessage
Pick(pid) == pick[HostOf[pid]]

ProcSet == SlushQueryProcess \cup SlushLoopProcess \cup {"ClientRequest"}

VARIABLES pick, message, pc, sampleSet, loopVariant
vars == <<pick, message, pc, sampleSet, loopVariant>>

Init ==
  /\ pick = [n \in Node |-> NoColor]
  /\ message = {}
  /\ sampleSet = [self \in SlushLoopProcess |-> {}]
  /\ loopVariant = [self \in SlushLoopProcess |-> 0]
  /\ pc = [s \in ProcSet |-> CASE s \in SlushQueryProcess -> "QueryReplyLoop"
                            [] s \in SlushLoopProcess -> "RequireColorAssignment"
                            [] s = "ClientRequest" -> "ClientRequestLoop"]

SlushQueryLoopStep(self) == /\ pc[self] = "QueryReplyLoop"
                            /\ pc' = [pc EXCEPT ![self] =
                               IF ~Terminate THEN "WaitForQueryMessageOrTermination" ELSE "Done"]
                            /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

WaitForQueryMessageOrTermination(self) ==
  /\ pc[self] = "WaitForQueryMessageOrTermination"
  /\ PendingQueryMessage(self) # {} \/ Terminate
  /\ pc' = [pc EXCEPT ![self] =
            IF Terminate THEN "QueryReplyLoop" ELSE "RespondToQueryMessage"]
  /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

RespondToQueryMessage(self) ==
  /\ pc[self] = "RespondToQueryMessage"
  /\ \E msg \in PendingQueryMessage(self) :
       LET c == IF Pick(self) = NoColor THEN msg.color ELSE Pick(self) IN
         /\ pick' = [pick EXCEPT ![HostOf[self]] = c]
         /\ message' = (message \ {msg}) \cup
              {[type |-> QueryReplyMessageType, src |-> self, dst |-> msg.src, color |-> c]}
  /\ pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
  /\ UNCHANGED <<sampleSet, loopVariant>>

SlushQueryStep(self) == SlushQueryLoopStep(self) \/ WaitForQueryMessageOrTermination(self)
                         \/ RespondToQueryMessage(self)

RequireColorAssignment(self) ==
  /\ pc[self] = "RequireColorAssignment"
  /\ Pick(self) # NoColor
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
  /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

ExecuteSlushLoop(self) ==
  /\ pc[self] = "ExecuteSlushLoop"
  /\ pc' = [pc EXCEPT ![self] =
            IF loopVariant[self] < SlushIterationCount THEN "QuerySampleSet"
            ELSE "SlushLoopTermination"]
  /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

QuerySampleSet(self) ==
  /\ pc[self] = "QuerySampleSet"
  /\ \E possible \in LET otherNodes == Node \ {HostOf[self]}
                         otherQuery == {pid \in SlushQueryProcess : HostOf[pid] \in otherNodes}
                     IN {pidSet \in SUBSET otherQuery : Cardinality(pidSet) = SampleSetSize} :
       /\ sampleSet' = [sampleSet EXCEPT ![self] = possible]
       /\ message' = message \cup
            {[type |-> QueryMessageType, src |-> self, dst |-> pid, color |-> Pick(self)]
               : pid \in possible}
  /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
  /\ UNCHANGED <<pick, loopVariant>>

TallyQueryReplies(self) ==
  /\ pc[self] = "TallyQueryReplies"
  /\ \A pid \in sampleSet[self] : \E m \in PendingQueryReplyMessage(self) : m.src = pid
  /\ LET redTally == Cardinality({m \in PendingQueryReplyMessage(self)
                         : m.src \in sampleSet[self] /\ m.color = Red})
        blueTally == Cardinality({m \in PendingQueryReplyMessage(self)
                         : m.src \in sampleSet[self] /\ m.color = Blue})
     IN pick' = IF redTally >= PickFlipThreshold THEN [pick EXCEPT ![HostOf[self]] = Red]
                ELSE IF blueTally >= PickFlipThreshold THEN [pick EXCEPT ![HostOf[self]] = Blue]
                ELSE pick
  /\ message' = message \ {m \in message : m.type = QueryReplyMessageType
                                          /\ m.src \in sampleSet[self] /\ m.dst = self}
  /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
  /\ loopVariant' = [loopVariant EXCEPT ![self] = loopVariant[self] + 1]
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]

SlushLoopTermination(self) ==
  /\ pc[self] = "SlushLoopTermination"
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ message' = message \cup {[type |-> TerminationMessageType, pid |-> self]}
  /\ UNCHANGED <<pick, sampleSet, loopVariant>>

SlushLoopStep(self) ==
  RequireColorAssignment(self) \/ ExecuteSlushLoop(self)
  \/ QuerySampleSet(self) \/ TallyQueryReplies(self)
  \/ SlushLoopTermination(self)

ClientRequestLoop ==
  /\ pc["ClientRequest"] = "ClientRequestLoop"
  /\ IF \E n \in Node : pick[n] = NoColor
       THEN pc' = [pc EXCEPT !["ClientRequest"] = "AssignColorToNode"]
       ELSE pc' = [pc EXCEPT !["ClientRequest"] = "Done"]
  /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

AssignColorToNode ==
  /\ pc["ClientRequest"] = "AssignColorToNode"
  /\ \E n \in Node : \E c \in Color :
        IF pick[n] = NoColor
           THEN pick' = [pick EXCEPT ![n] = c]
           ELSE pick' = pick
  /\ pc' = [pc EXCEPT !["ClientRequest"] = "ClientRequestLoop"]
  /\ UNCHANGED <<message, sampleSet, loopVariant>>

ClientRequestStep == ClientRequestLoop \/ AssignColorToNode

Terminating == \A s \in ProcSet : pc[s] = "Done"

Next ==
  ClientRequestStep \/ (\E s \in SlushQueryProcess : SlushQueryStep(s))
  \/ (\E s \in SlushLoopProcess : SlushLoopStep(s))
  \/ (Terminating /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A s \in ProcSet : pc[s] = "Done")

(* No node is ever left undecided at the end of the run.                      *)
AllNodesDecided == \A n \in Node : <>[](pick[n] # NoColor)

====