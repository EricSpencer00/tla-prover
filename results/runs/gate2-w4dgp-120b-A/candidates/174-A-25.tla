---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Slush: the simplest metastable consensus protocol from the Avalanche family. *)
(* Each node runs a loop process that samples peers and adopts the majority   *)
(* color it observes; each node also runs a query process that answers      *)
(* sampled queries. A client process assigns initial colors to uncolored     *)
(* nodes. PlusCal translation; the model checks type safety and termination. *)

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping
          SlushIterationCount, SampleSetSize, PickFlipThreshold
          NoColor, NoMessage

VARIABLES color, messages, pc, sampleSet, iterationCount

vars == << color, messages, pc, sampleSet, iterationCount >>

\* A query message records the sender, the receiver query process, and the
\* sender's current color. A query reply swaps sender and receiver.
\* The termination message signals a finished loop process.
Message == [sender: SlushLoopProcess, receiver: SlushQueryProcess, color: {NoColor} \cup {1, 2}]
           \cup [sender: SlushQueryProcess, receiver: SlushLoopProcess, color: {NoColor} \cup {1, 2}]
           \cup [loopProcess: SlushLoopProcess]

TypeOK ==
  /\ color \in [Node -> {NoColor} \cup {1, 2}]
  /\ messages \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"ready", "working", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterationCount \in [SlushLoopProcess -> 0..SlushIterationCount]

RECURSIVE MaxIter(_)
MaxIter(n) == IF n = 0 THEN 0 ELSE IF iterationCount[n] > MaxIter(n-1) THEN iterationCount[n] ELSE MaxIter(n-1)

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [proc \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> "ready"]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ iterationCount = [lp \in SlushLoopProcess |-> 0]

\* The client assigns a random color to some uncolored node.
ClientAssignsColor ==
  /\ pc["client"] = "ready"
  /\ \E n \in Node :
       /\ color[n] = NoColor
       /\ \E k \in {1, 2} : color' = [color EXCEPT ![n] = k]
  /\ pc' = [pc EXCEPT !["client"] = "working"]
  /\ UNCHANGED << messages, sampleSet, iterationCount >>

ClientLoopExit ==
  /\ pc["client"] = "working"
  /\ \A n \in Node : color[n] # NoColor
  /\ pc' = [pc EXCEPT !["client"] = "done"]
  /\ UNCHANGED << color, messages, sampleSet, iterationCount >>

\* A loop process needs its host node to be colored before it can begin.
RequireColor ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "ready"
       /\ LET n == CHOOSE n \in Node : <<lp, n>> \in HostMapping
          IN color[n] # NoColor
       /\ pc' = [pc EXCEPT ![lp] = "working"]
  /\ UNCHANGED << color, messages, sampleSet, iterationCount >>

\* The loop process samples a random subset of peers and sends queries.
QuerySampleSet ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "working"
       /\ iterationCount[lp] < SlushIterationCount
       /\ LET n == CHOOSE n \in Node : <<lp, n>> \in HostMapping
              peers == { q \in SlushQueryProcess : q # CHOOSE q \in SlushQueryProcess : <<q, n>> \in HostMapping }
              sample == { q \in peers : Cardinality({x \in peers : x <= q}) <= SampleSetSize }
              inMessages == { [sender |-> lp, receiver |-> q, color |-> color[n]] : q \in sample }
          IN /\ messages' = messages \cup inMessages
             /\ sampleSet' = [sampleSet EXCEPT ![lp] = sample]
  /\ UNCHANGED << color, pc, iterationCount >>

\* A query process answers with its current color (adopting the query's color if uncolored).
RespondToQuery ==
  /\ \E m \in messages :
       /\ m \in [sender: SlushLoopProcess, receiver: SlushQueryProcess, color: {NoColor} \cup {1, 2}]
       /\ LET n == CHOOSE n \in Node : <<m.receiver, n>> \in HostMapping
              reply == [sender |-> m.receiver, receiver |-> m.sender, color |-> IF color[n] = NoColor THEN m.color ELSE color[n]]
          IN /\ messages' = (messages \ {m}) \cup {reply}
             /\ color' = IF color[n] = NoColor /\ m.color # NoColor THEN [color EXCEPT ![n] = m.color] ELSE color
  /\ UNCHANGED << pc, sampleSet, iterationCount >>

\* Replies are tallied; with enough consensus the node flips to the majority.
TallyReplies ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "working"
       /\ sampleSet[lp] # {}
       /\ \A q \in sampleSet[lp] : [sender |-> q, receiver |-> lp, color |-> NoColor] \in messages
       /\ LET n == CHOOSE n \in Node : <<lp, n>> \in HostMapping
              rmsgs == { m \in messages : m.receiver = lp } \ [sender |-> lp, receiver |-> n, color |-> NoColor]
              pcntc == { m \in rmsgs : m.color = 1 }
              cntc == Cardinality(pcntc)
              pntc == { m \in rmsgs : m.color = 2 }
              cntnc == Cardinality(pntc)
              newcolor == IF cntc >= PickFlipThreshold THEN 1
                          ELSE IF cntnc >= PickFlipThreshold THEN 2 ELSE color[n]
          IN /\ color' = [color EXCEPT ![n] = newcolor]
             /\ iterationCount' = [iterationCount EXCEPT ![lp] = iterationCount[lp] + 1]
             /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
  /\ UNCHANGED << messages, pc >>

LoopTermination ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "working"
       /\ iterationCount[lp] = SlushIterationCount
       /\ pc' = [pc EXCEPT ![lp] = "done"]
       /\ messages' = messages \cup {[loopProcess |-> lp]}
  /\ UNCHANGED << color, sampleSet, iterationCount >>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "ready"
       /\ \A lp \in SlushLoopProcess : [loopProcess |-> lp] \in messages
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED << color, messages, sampleSet, iterationCount >>

Next ==
  \/ ClientAssignsColor \/ ClientLoopExit \/ RequireColor
  \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ClientAssignsColor) /\ WF_vars(ClientLoopExit)
        /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
        /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)
        /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

AllProcessesTerminate == <>(\A proc \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : pc[proc] = "done")

====