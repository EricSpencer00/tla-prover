---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush: a metastable probabilistic-consensus protocol (Team Rocket, 2018)
\* From the spec's perspective this is purely a deterministic executable
\* model of the protocol's control flow; the random choices are modeled as
\* nondeterministic choice, and the flip-to-a-consensus phase is
\* deliberately omitted (it is the probabilistic part the model cannot
\* represent). The spec therefore checks only structural properties:
\* typing (colors, messages) and eventual termination of every process.

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold,
          NoColor, NoMessage

Processes == SlushLoopProcess \cup SlushQueryProcess \cup {"client"}

MessageType == {"query", "queryReply", "termination"}
Color == {"colorRed", "colorBlue"}
Query == [qtype: "query", pid: SlushLoopProcess, col: Color]
QueryReply == [qtype: "queryReply", pid: SlushLoopProcess, col: Color]
Termination == [qtype: "termination", pid: SlushLoopProcess]

VARIABLES nodeColor, inbox, pc, sampleSet, iterations
vars == <<nodeColor, inbox, pc, sampleSet, iterations>>

QueryPeers(p) == {q \in SlushQueryProcess : <<p, q>> \in HostMapping}

TypeOK ==
  /\ nodeColor \in [Node -> Color \cup {NoColor}]
  /\ inbox \subseteq (Query \cup QueryReply \cup Termination)
  /\ pc \in [Processes -> 0..4]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ inbox = {}
  /\ pc = [p \in Processes |-> IF p = "client" THEN 0 ELSE 1]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iterations = [p \in SlushLoopProcess |-> 0]

\* Client process: assigns an initial color to a still-uncolored node.
AssignColor(n, c) ==
  /\ pc["client"] = 0
  /\ nodeColor[n] = NoColor
  /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = 0]
  /\ UNCHANGED <<inbox, sampleSet, iterations>>

\* Each loop process waits for its host node to be colored before iterating.
RequireColor(p) ==
  /\ pc[p] = 1
  /\ nodeColor[CHOOSE n \in Node : <<p, n>> \in HostMapping] # NoColor
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<nodeColor, inbox, sampleSet, iterations>>

\* The loop process chooses a random sample of peers and queries them.
QuerySampleSet(p) ==
  /\ pc[p] = 2
  /\ sampleSet[p] = {}
  /\ \E peers \in SUBSET QueryPeers(p) :
       /\ Cardinality(peers) = SampleSetSize
       /\ sampleSet' = [sampleSet EXCEPT ![p] = peers]
  /\ inbox' = inbox \union { [qtype |-> "query", pid |-> p,
                    col |-> nodeColor[CHOOSE n \in Node : <<p, n>> \in HostMapping]]
                    : q \in sampleSet[p] }
  /\ pc' = [pc EXCEPT ![p] = 3]
  /\ UNCHANGED <<nodeColor, iterations>>

\* A query process adopts the querying color if it is uncolored, then replies.
RespondToQuery ==
  /\ pc["client"] = 0
  /\ \E q \in inbox :
       /\ q.qtype = "query"
       /\ nodeColor' = [nodeColor EXCEPT
             ![CHOOSE n \in Node : <<q.pid, n>> \in HostMapping] =
               IF nodeColor[CHOOSE n \in Node : <<q.pid, n>> \in HostMapping]
                 = NoColor THEN q.col ELSE nodeColor[CHOOSE n \in Node : <<q.pid, n>> \in HostMapping]]
       /\ inbox' = (inbox \ {q}) \union
             {[qtype |-> "queryReply", pid |-> q.pid,
                 col |-> nodeColor[CHOOSE n \in Node : <<q.pid, n>> \in HostMapping]]}
  /\ UNCHANGED <<pc, sampleSet, iterations>>

\* The loop process tallies replies; a strong majority flips the node's color.
TallyReplies ==
  /\ pc["client"] = 0
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 3
       /\ \A q \in sampleSet[p] : \E r \in inbox : r.qtype = "queryReply" /\ r.pid = p /\ r.col = nodeColor[CHOOSE n \in Node : <<p, n>> \in HostMapping]
       /\ LET c1 == Cardinality({q \in inbox : q.qtype = "queryReply" /\ q.pid = p /\ q.col = "colorRed"})
              c2 == Cardinality({q \in inbox : q.qtype = "queryReply" /\ q.pid = p /\ q.col = "colorBlue"})
          IN nodeColor' = [nodeColor EXCEPT ![CHOOSE n \in Node : <<p, n>> \in HostMapping] =
                IF c1 >= PickFlipThreshold THEN "colorRed" ELSE IF c2 >= PickFlipThreshold THEN "colorBlue" ELSE nodeColor[CHOOSE n \in Node : <<p, n>> \in HostMapping]]
       /\ inbox' = {r \in inbox : ~(r.qtype = "queryReply" /\ r.pid = p)}
       /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
       /\ iterations' = [iterations EXCEPT ![p] = @ + 1]
       /\ pc' = [pc EXCEPT ![p] = IF iterations[p] < SlushIterationCount THEN 2 ELSE 4]
  /\ UNCHANGED <<>>

\* Loop termination: each loop process broadcasts its termination message.
LoopTerminate ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 4
       /\ pc' = [pc EXCEPT ![p] = 5]
       /\ inbox' = inbox \union { [qtype |-> "termination", pid |-> p] }
  /\ UNCHANGED <<nodeColor, sampleSet, iterations>>

\* Query processes exit once every loop process has terminated.
QueryLoopExit ==
  /\ pc["client"] = 0
  /\ \A p \in SlushLoopProcess : pc[p] = 5
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = 1
       /\ pc' = [pc EXCEPT ![q] = 5]
  /\ UNCHANGED <<nodeColor, inbox, sampleSet, iterations>>

Next ==
  \/ \E n \in Node, c \in Color : AssignColor(n, c)
  \/ \E p \in SlushLoopProcess : RequireColor(p)
  \/ \E p \in SlushLoopProcess : QuerySampleSet(p)
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTerminate
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(LoopTerminate) /\ WF_vars(TallyReplies)
        /\ WF_vars(QueryLoopExit) /\ WF_vars(RespondToQuery)

AllDone == \A p \in Processes : pc[p] = 5

Termination == <>(AllDone)

====