---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
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
  CHOOSE n \in Node : \E mapping \in HostMapping :
    /\ n \in mapping /\ pid \in mapping

(* Global variables *)
VARIABLES pick, message, pc, sampleSet, loopVariant
vars == << pick, message, pc, sampleSet, loopVariant >>

TypeInvariant ==
  /\ pick \in [Node -> {"Red", "Blue", "NoColor"}]
  /\ message \subseteq
       { color \in {"Red", "Blue"} : [type |-> "QueryMessageType", src |-> SlushLoopProcess,
          dst |-> SlushQueryProcess, color |-> color]
       } \cup
       { color \in {"Red", "Blue"} : [type |-> "QueryReplyMessageType", src |-> SlushQueryProcess,
          dst |-> SlushLoopProcess, color |-> color]
       } \cup {[type |-> "TerminationMessageType", pid |-> SlushLoopProcess]}
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopVariant \in [SlushLoopProcess -> 0..SlushIterationCount]
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"ClientRequest"} ->
            {"QueryReplyLoop", "StartQueryLoop", "QueryReplyLoopWaiting", "RespondToQueryMessage",
             "RequireColorAssignment", "ExecuteSlushLoop", "QuerySampleSet", "TallyQueryReplies",
             "SlushLoopTermination", "ClientRequestLoop", "AssignColorToNode", "Done"}]

Init ==
  /\ pick = [node \in Node |-> "NoColor"]
  /\ message = {}
  /\ sampleSet = [self \in SlushLoopProcess |-> {}]
  /\ loopVariant = [self \in SlushLoopProcess |-> 0]
  /\ pc = [self \in SlushLoopProcess \cup SlushQueryProcess \cup {"ClientRequest"}|->
            CASE self \in SlushQueryProcess -> "QueryReplyLoop"
              [] self \in SlushLoopProcess -> "RequireColorAssignment"
              [] self = "ClientRequest" -> "ClientRequestLoop"]

Pick(pid) == pick[HostOf[pid]]

Pending(mtype, pid) == { m \in message : m.type = mtype /\ m.dst = pid }

Terminate == message = {[type |-> "TerminationMessageType", pid |-> SlushLoopProcess]}

QueryReplyLoop(self) ==
  /\ pc[self] = "QueryReplyLoop"
  /\ pc' = [pc EXCEPT ![self] = IF ~Terminate THEN "QueryReplyLoopWaiting" ELSE "Done"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

QueryReplyLoopWaiting(self) ==
  /\ pc[self] = "QueryReplyLoopWaiting"
  /\ Pending("QueryMessageType", self) # {} \/ Terminate
  /\ pc' = [pc EXCEPT ![self] = IF Terminate THEN "QueryReplyLoop" ELSE "RespondToQueryMessage"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

RespondToQueryMessage(self) ==
  /\ pc[self] = "RespondToQueryMessage"
  /\ \E msg \in Pending("QueryMessageType", self) :
       LET color == IF Pick(self) = "NoColor" THEN msg.color ELSE Pick(self) IN
         /\ pick' = [pick EXCEPT ![HostOf[self]] = color]
         /\ message' = (message \ {msg}) \cup
              {[type |-> "QueryReplyMessageType", src |-> self, dst |-> msg.src, color |-> color]}
  /\ pc' = [pc EXCEPT ![self] = "QueryReplyLoop"]
  /\ UNCHANGED << sampleSet, loopVariant >>

RequireColorAssignment(self) ==
  /\ pc[self] = "RequireColorAssignment"
  /\ Pick(self) # "NoColor"
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

ExecuteSlushLoop(self) ==
  /\ pc[self] = "ExecuteSlushLoop"
  /\ pc' = [pc EXCEPT ![self] = IF loopVariant[self] < SlushIterationCount
                                   THEN "QuerySampleSet"
                                   ELSE "SlushLoopTermination"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

QuerySampleSet(self) ==
  /\ pc[self] = "QuerySampleSet"
  /\ \E possible \in
        LET otherNodes == Node \ {HostOf[self]}
            otherQueries == {pid \in SlushQueryProcess : HostOf[pid] \in otherNodes}
        IN {p \in SUBSET otherQueries : Cardinality(p) = SampleSetSize} :
       /\ sampleSet' = [sampleSet EXCEPT ![self] = possible]
       /\ message' = message \cup
            {[type |-> "QueryMessageType", src |-> self, dst |-> pid, color |-> Pick(self)]
               : pid \in possible}
  /\ pc' = [pc EXCEPT ![self] = "TallyQueryReplies"]
  /\ UNCHANGED << pick, loopVariant >>

TallyQueryReplies(self) ==
  /\ pc[self] = "TallyQueryReplies"
  /\ \A pid \in sampleSet[self] : \E m \in Pending("QueryReplyMessageType", self) : m.src = pid
  /\ LET red == Cardinality(
            {m \in Pending("QueryReplyMessageType", self) :
               m.src \in sampleSet[self] /\ m.color = "Red"})
         blue == Cardinality(
            {m \in Pending("QueryReplyMessageType", self) :
               m.src \in sampleSet[self] /\ m.color = "Blue"}) IN
       pick' = IF red >= PickFlipThreshold
                 THEN [pick EXCEPT ![HostOf[self]] = "Red"]
                 ELSE IF blue >= PickFlipThreshold
                        THEN [pick EXCEPT ![HostOf[self]] = "Blue"]
                        ELSE pick
  /\ message' = message \ {m \in message :
                    m.type = "QueryReplyMessageType" /\ m.src \in sampleSet[self] /\ m.dst = self}
  /\ sampleSet' = [sampleSet EXCEPT ![self] = {}]
  /\ loopVariant' = [loopVariant EXCEPT ![self] = loopVariant[self] + 1]
  /\ pc' = [pc EXCEPT ![self] = "ExecuteSlushLoop"]

SlushLoopTermination(self) ==
  /\ pc[self] = "SlushLoopTermination"
  /\ message' = message \cup {[type |-> "TerminationMessageType", pid |-> self]}
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED << pick, sampleSet, loopVariant >>

ClientRequestLoop ==
  /\ pc["ClientRequest"] = "ClientRequestLoop"
  /\ pc' = [pc EXCEPT !["ClientRequest"] =
            IF \E n \in Node : pick[n] = "NoColor" THEN "AssignColorToNode" ELSE "Done"]
  /\ UNCHANGED << pick, message, sampleSet, loopVariant >>

AssignColorToNode ==
  /\ pc["ClientRequest"] = "AssignColorToNode"
  /\ \E node \in Node, color \in {"Red", "Blue"} :
       pick' = [pick EXCEPT ![node] = IF pick[node] = "NoColor" THEN color ELSE pick[node]]
  /\ pc' = [pc EXCEPT !["ClientRequest"] = "ClientRequestLoop"]
  /\ UNCHANGED << message, sampleSet, loopVariant >>

Done == \A self \in SlushLoopProcess \cup SlushQueryProcess \cup {"ClientRequest"} : pc[self] = "Done"
Terminating == Done /\ UNCHANGED vars

Next ==
  \/ \E self \in SlushQueryProcess : QueryReplyLoop(self) \/ QueryReplyLoopWaiting(self) \/ RespondToQueryMessage(self)
  \/ \E self \in SlushLoopProcess :
        RequireColorAssignment(self) \/ ExecuteSlushLoop(self) \/ QuerySampleSet(self)
          \/ TallyQueryReplies(self) \/ SlushLoopTermination(self)
  \/ ClientRequestLoop \/ AssignColorToNode \/ Terminating

Spec == Init /\ [][Next]_vars

TerminatingPath == <>(Done)

====