---- MODULE Slush ----
(* Slush: a very simple probabilistic consensus protocol in the Avalanche family.
   This is a TLA+ version of the original ANU model; it does not model the
   probabilistic aspect itself. *)
EXTENDS Naturals, FiniteSets, Sequences
CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold

ASSUME /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
       /\ Cardinality(Node) = Cardinality(SlushQueryProcess)
       /\ SlushIterationCount \in Nat /\ SampleSetSize \in Nat /\ PickFlipThreshold \in Nat

ASSUME HostMappingType ==
  /\ Cardinality(Node) = Cardinality(HostMapping)
  /\ \A m \in HostMapping : Cardinality(m) = 3 /\ \E e \in m : e \in Node /\ \E e \in m : e \in SlushLoopProcess /\ \E e \in m : e \in SlushQueryProcess

HostOf[pid \in SlushLoopProcess \cup SlushQueryProcess] ==
  CHOOSE n \in Node : \E m \in HostMapping : n \in m /\ pid \in m

Red == "Red" Blue == "Blue"
Color == {Red, Blue} NoColor == CHOOSE c : c \notin Color
QueryMessageType == "QueryMessageType" QueryReplyMessageType == "QueryReplyMessageType"
TerminationMessageType == "TerminationMessageType"
QueryMessage == [type : {QueryMessageType}, src : SlushLoopProcess, dst : SlushQueryProcess, color : Color]
QueryReplyMessage == [type : {QueryReplyMessageType}, src : SlushQueryProcess, dst : SlushLoopProcess, color : Color]
TerminationMessage == [type : {TerminationMessageType}, pid : SlushLoopProcess]
Message == QueryMessage \cup QueryReplyMessage \cup TerminationMessage

VARIABLES pick, message, pc, sampleSet, loopVariant
vars == <<pick, message, pc, sampleSet, loopVariant>>
ProcSet == SlushQueryProcess \cup SlushLoopProcess \cup {"ClientRequest"}

TypeInv == /\ pick \in [Node -> Color \cup {NoColor}]
           /\ message \subseteq Message /\ pc \in [ProcSet -> {"Done","QueryReplyLoop","WaitForQueryMessageOrTermination","RespondToQueryMessage","RequireColorAssignment","ExecuteSlushLoop","QuerySampleSet","TallyQueryReplies","SlushLoopTermination","ClientRequestLoop","AssignColorToNode"}]

Pick(pid) == pick[HostOf[pid]]
PendingQuery(pid) == {m \in message : m.type = QueryMessageType /\ m.dst = pid}
PendingReply(pid) == {m \in message : m.type = QueryReplyMessageType /\ m.dst = pid}
Terminate == message = TerminationMessage

Init == /\ pick = [n \in Node |-> NoColor] /\ message = {}
        /\ sampleSet = [s \in SlushLoopProcess |-> {}]
        /\ loopVariant = [s \in SlushLoopProcess |-> 0]
        /\ pc = [p \in ProcSet |-> CASE p \in SlushQueryProcess -> "QueryReplyLoop" [] p \in SlushLoopProcess -> "RequireColorAssignment" [] p = "ClientRequest" -> "ClientRequestLoop"]

QueryReplyLoop(s) == /\ pc[s] = "QueryReplyLoop" /\ pc' = [pc EXCEPT ![s] = IF ~Terminate THEN "WaitForQueryMessageOrTermination" ELSE "Done"]
                     /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

WaitForQuery(s) == /\ pc[s] = "WaitForQueryMessageOrTermination" /\ (PendingQuery(s) # {} \/ Terminate)
                    /\ pc' = [pc EXCEPT ![s] = IF Terminate THEN "QueryReplyLoop" ELSE "RespondToQueryMessage"]
                    /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

RespondToQuery(s) == /\ pc[s] = "RespondToQueryMessage" /\ \E m \in PendingQuery(s) :
                        /\ pick' = [pick EXCEPT ![HostOf[s]] = IF Pick(s) = NoColor THEN m.color ELSE Pick(s)]
                        /\ message' = message \ {m} \cup {[type |-> QueryReplyMessageType, src |-> s, dst |-> m.src, color |-> IF Pick(s) = NoColor THEN m.color ELSE Pick(s)]}
                     /\ pc' = [pc EXCEPT ![s] = "QueryReplyLoop"]
                     /\ UNCHANGED <<sampleSet, loopVariant>>

SlushQuery(s) == QueryReplyLoop(s) \/ WaitForQuery(s) \/ RespondToQuery(s)

RequireColor(s) == /\ pc[s] = "RequireColorAssignment" /\ Pick(s) # NoColor
                    /\ pc' = [pc EXCEPT ![s] = "ExecuteSlushLoop"]
                    /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

ExecuteLoop(s) == /\ pc[s] = "ExecuteSlushLoop"
                  /\ pc' = [pc EXCEPT ![s] = IF loopVariant[s] < SlushIterationCount THEN "QuerySampleSet" ELSE "SlushLoopTermination"]
                  /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

QuerySample(s) == /\ pc[s] = "QuerySampleSet"
                   /\ \E q \in SUBSET {p \in SlushQueryProcess : HostOf[p] # HostOf[s]} : Cardinality(q) = SampleSetSize
                       /\ sampleSet' = [sampleSet EXCEPT ![s] = q]
                       /\ message' = message \cup {[type |-> QueryMessageType, src |-> s, dst |-> p, color |-> Pick(s)] : p \in q}
                   /\ pc' = [pc EXCEPT ![s] = "TallyQueryReplies"]
                   /\ UNCHANGED <<pick, loopVariant>>

Tally(s) == /\ pc[s] = "TallyQueryReplies" /\ \A p \in sampleSet[s] : \E m \in PendingReply(s) : m.src = p
             /\ LET red == Cardinality({m \in PendingReply(s) : m.src \in sampleSet[s] /\ m.color = Red})
                    blue == Cardinality({m \in PendingReply(s) : m.src \in sampleSet[s] /\ m.color = Blue}) IN
                pick' = IF red >= PickFlipThreshold THEN [pick EXCEPT ![HostOf[s]] = Red]
                        ELSE IF blue >= PickFlipThreshold THEN [pick EXCEPT ![HostOf[s]] = Blue] ELSE pick
             /\ message' = message \ {m \in message : m.type = QueryReplyMessageType /\ m.src \in sampleSet[s] /\ m.dst = s}
             /\ sampleSet' = [sampleSet EXCEPT ![s] = {}]
             /\ loopVariant' = [loopVariant EXCEPT ![s] = loopVariant[s] + 1]
             /\ pc' = [pc EXCEPT ![s] = "ExecuteSlushLoop"]

SlushLoop(s) == RequireColor(s) \/ ExecuteLoop(s) \/ QuerySample(s) \/ Tally(s)

TerminateLoop(s) == /\ pc[s] = "SlushLoopTermination"
                    /\ message' = message \cup {[type |-> TerminationMessageType, pid |-> s]}
                    /\ pc' = [pc EXCEPT ![s] = "Done"]
                    /\ UNCHANGED <<pick, sampleSet, loopVariant>>

ClientLoop == /\ pc["ClientRequest"] = "ClientRequestLoop"
               /\ pc' = [pc EXCEPT !"ClientRequest" = IF \E n \in Node : pick[n] = NoColor THEN "AssignColorToNode" ELSE "Done"]
               /\ UNCHANGED <<pick, message, sampleSet, loopVariant>>

AssignColor == /\ pc["ClientRequest"] = "AssignColorToNode"
                /\ \E n \in Node, c \in Color : pick' = [pick EXCEPT ![n] = IF pick[n] = NoColor THEN c ELSE pick[n]]
                /\ pc' = [pc EXCEPT !"ClientRequest" = "ClientRequestLoop"]
                /\ UNCHANGED <<message, sampleSet, loopVariant>>

Stall == /\ \A p \in ProcSet : pc[p] = "Done" /\ UNCHANGED vars
Next == Stall \/ (\E s \in SlushQueryProcess : SlushQuery(s))
            \/ (\E s \in SlushLoopProcess : SlushLoop(s) \/ TerminateLoop(s))
            \/ ClientLoop \/ AssignColor
Spec == Init /\ [][Next]_vars

====