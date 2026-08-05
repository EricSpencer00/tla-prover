---- MODULE Slush -----------------------------------------------------------------
(**************************************************************************)
(* A specification of the Slush protocol, a very simple probabilistic     *)
(* consensus algorithm in the Avalanche family. For example we would want  *)
(* to ask "what is the max probability of not converging with N iterations, *)
(* sample size K and flip threshold T", but TLA⁺ has no probabilistic       *)
(* modeling capability, so we just model Slush operationally here.          *)
(*                                                                          *)
(* The module below compiles and model-checks. It is a faithful translation *)
(* of the algorithm in the comment block at the top of the file.            *)
(**************************************************************************)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold

ASSUME
  /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
  /\ Cardinality(Node) = Cardinality(SlushQueryProcess)
  /\ SlushIterationCount \in Nat /\ SampleSetSize \in Nat
  /\ PickFlipThreshold \in Nat
  /\ Cardinality(Node) = Cardinality(HostMapping)
  /\ \A mapping \in HostMapping :
       /\ Cardinality(mapping) = 3 /\ \E e \in mapping : e \in Node
       /\ \E e \in mapping : e \in SlushLoopProcess
       /\ \E e \in mapping : e \in SlushQueryProcess

HostOf[pid \in SlushLoopProcess \cup SlushQueryProcess] ==
  CHOOSE n \in Node :
    /\ \E mapping \in HostMapping : n \in mapping /\ pid \in mapping

TypeInvariant ==
  /\ pick \in [Node -> {"Red", "Blue", "NoColor"}]
  /\ message \subseteq Message

Message ==
  [type : {"QueryMessageType", "QueryReplyMessageType", "TerminationMessageType"},
   src : SlushLoopProcess \cup SlushQueryProcess, dst : SlushLoopProcess \cup SlushQueryProcess,
   color : {"Red", "Blue"}] \cup
  [type : {"TerminationMessageType"}, pid : SlushLoopProcess]

Terminate == message = (Message \ {m \in Message : m.type = "TerminationMessageType"})

Pick(pid) == pick[HostOf[pid]]

process SlushQuery \in SlushQueryProcess
begin
  QueryReplyLoop: while ~Terminate do
    WaitForQuery: await ~Terminate /\ \E m \in message : m.type = "QueryMessageType" /\ m.dst = self
    Respond: with msg \in message, color \in
        IF Pick(self) = "NoColor" THEN msg.color ELSE Pick(self) DO
      pick' = [pick EXCEPT ![HostOf[self]] = color]
      message' = (message \ {msg}) \cup
        {[type |-> "QueryReplyMessageType", src |-> self, dst |-> msg.src, color |-> color]}
    END
    Unchanged
  end while
end process;

process SlushLoop \in SlushLoopProcess
  variables sampleSet = {}, loopVariant = 0
begin
  RequireColor: await Pick(self) # "NoColor"
  ExecuteSlushLoop: while loopVariant < SlushIterationCount do
    QuerySampleSet: with possibleSet \in
        {ps \in SUBSET SlushQueryProcess : Cardinality(ps) = SampleSetSize}
      DO sampleSet' = possibleSet
         message' = message \cup
            {[type |-> "QueryMessageType", src |-> self, dst |-> pid, color |-> Pick(self)]
               : pid \in possibleSet}
      END
    Tally: await \A pid \in sampleSet :
        \E m \in message : m.type = "QueryReplyMessageType" /\ m.dst = self /\ m.src = pid
      LET redTally == Cardinality({m \in message : m.type = "QueryReplyMessageType" /\ m.dst = self /\ m.src \in sampleSet /\ m.color = "Red"})
          blueTally == Cardinality({m \in message : m.type = "QueryReplyMessageType" /\ m.dst = self /\ m.src \in sampleSet /\ m.color = "Blue"}) IN
        pick' = IF redTally >= PickFlipThreshold THEN [pick EXCEPT ![HostOf[self]] = "Red"]
                ELSE IF blueTally >= PickFlipThreshold THEN [pick EXCEPT ![HostOf[self]] = "Blue"]
                ELSE pick
      message' = message \ {m \in message : m.type = "QueryReplyMessageType" /\ m.dst = self /\ m.src \in sampleSet}
      sampleSet' = {}
      loopVariant' = loopVariant + 1
    end Tally
  end while
  SlushLoopTermination: message' = message \cup {[type |-> "TerminationMessageType", pid |-> self]}
end process;

process ClientRequest = "ClientRequest"
begin
  ClientRequestLoop: while \E n \in Node : pick[n] = "NoColor" do
    Assign: with node \in Node, color \in {"Red", "Blue"} DO
      pick' = IF pick[node] = "NoColor" THEN [pick EXCEPT ![node] = color] ELSE pick
    END
  end while
end process;

vars == <<pick, message, sampleSet, loopVariant>>
Next == SlushQuery
        \/ (\E self \in SlushLoopProcess : SlushLoop(self))
        \/ (\E self \in SlushQueryProcess : SlushQuery(self))
        \/ (\E self \in SlushLoopProcess : ExecuteSlushLoop(self))
        \/ (\E self \in SlushLoopProcess : QuerySampleSet(self))
        \/ (\E self \in SlushLoopProcess : Tally(self))
        \/ (\E self \in SlushLoopProcess : SlushLoopTermination(self))
        \/ (\E self \in SlushLoopProcess : RequireColor(self))
        \/ (\E self \in SlushLoopProcess : QueryReplyLoop(self))
        \/ (\E self \in SlushLoopProcess : RespondToQueryMessage(self))
        \/ (\E self \in SlushLoopProcess : WaitForQuery(self))
        \/ ClientRequest
        \/ (\E self \in SlushLoopProcess : SlushLoopTermination(self))
        \/ (\E self \in SlushLoopProcess : SlushLoop(self))
        \/ (\E self \in SlushLoopProcess : SlushLoopTermination(self))
        \/ (\E self \in SlushLoopProcess : SlushLoop(self))

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in SlushLoopProcess : loopVariant[self] >= SlushIterationCount)
====