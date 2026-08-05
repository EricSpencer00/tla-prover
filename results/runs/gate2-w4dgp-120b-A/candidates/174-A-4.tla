---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Slush: the simplest member of the Snow family of probabilistic consensus   *)
(* protocols (Avalanche, Team Rocket 2018).  Nodes repeatedly sample random   *)
(* peers and adopt a sufficiently popular opinion, leading the network to a   *)
(* single consensus color.  This PlusCal model provides executable pseudocode *)
(* for the protocol; the convergence guarantee itself is probabilistic and     *)
(* cannot be captured directly in TLA+.                                           *)

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Loop processes are the Slush drivers (one per node); query processes answer
\* each other's sampling queries.  HostMapping links every loop and query
\* process to its owning node, and enforces the 1:1:1 ratio between processes
\* and nodes expected by the protocol's design.

VARIABLES color, msg, pc, sampleSet, iterCount

vars == <<color, msg, pc, sampleSet, iterCount>>

\* A message is an element of exactly one of the three payload tables below:
\* pQuery (a loop process querying a peer's query process), pReply (a query
\* process answering a loop process), pDone (a loop process signaling that
\* it has finished all its iterations).  NoMessage is a distinguished value
\* outside the range of any real message, used to mark a process as idle.
Message == pQuery[SlushQueryProcess, SlushLoopProcess] \cup
           pReply[SlushLoopProcess, Color] \cup
           pDone[SlushLoopProcess]

\* A sample set is the subset of peers a loop process has queried this round.
\* The number of replies it must hear is exactly its sample set size (a fixed
\* parameter of the protocol's metastable voting rule).
SampleSpace == (SUBSET SlushQueryProcess) \ {{}}

TypeOK ==
  /\ color \in [Node -> Color \cup {NoColor}]
  /\ msg \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"Client"} -> 0..4]
  /\ sampleSet \in [SlushLoopProcess -> SampleSpace]
  /\ iterCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msg = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"Client"} |-> 0]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iterCount = [p \in SlushLoopProcess |-> 0]

\* The client process assigns the first color to an uncolored node.
AssignColor ==
  /\ pc["Client"] = 0
  /\ \E n \in Node :
       /\ color[n] = NoColor
       /\ \E c \in Color : color' = [color EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["Client"] = 1]
  /\ UNCHANGED <<msg, sampleSet, iterCount>>

\* A loop process only begins once its node has been assigned a color.
RequireColor ==
  /\ UNCHANGED <<color, msg, sampleSet, iterCount>>
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 0
       /\ \E n \in Node : <<p, n>> \in HostMapping /\ color[n] # NoColor
       /\ pc' = [pc EXCEPT ![p] = 1]

\* The core of Slush: a loop process samples a fixed-size subset of peers;
\* the peer set is a tuple (process, node) so that the sampling is over
\* processes, but the color lookup is on the owning node.
QuerySampleSet ==
  /\ UNCHANGED <<color, sampleSet, iterCount>>
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 1
       /\ iterCount[p] < SlushIterationCount
       /\ \E S \in SampleSpace :
            /\ Cardinality(S) = SampleSetSize
            /\ sampleSet' = [sampleSet EXCEPT ![p] = S]
            /\ msg' = msg \cup {[target |-> q, initiator |-> p, plabel |-> color[n]]
                                 : <<q, n>> \in {<<q, n>> : <<q, p>> \in S}
                                 /\ <<q, n>> \in HostMapping}
       /\ pc' = [pc EXCEPT ![p] = 2]

\* A query process either adopts the query's color (if its node is still
\* uncolored) or simply reflects its current color back to the loop.
RespondToQuery ==
  /\ UNCHANGED <<color, sampleSet, iterCount, pc>>
  /\ \E m \in msg :
       /\ m \in pQuery[SlushQueryProcess, SlushLoopProcess]
       /\ LET q == m.target
              n == CHOOSE x \in Node : <<q, x>> \in HostMapping
              pcurr == IF color[n] = NoColor THEN m.plabel ELSE color[n]
              reply == [dest |-> m.initiator, plabel |-> pcurr]
          IN /\ msg' = (msg \ {m}) \cup {reply}
       /\ UNCHANGED <<color, sampleSet, iterCount>>

\* The loop process tallies replies; a color reaching the flip threshold
\* (or exceeding it) wins the round.  Because each sampled peer replies
\* exactly once, every reply is counted precisely once in this round.
TallyReplies ==
  /\ UNCHANGED <<color, sampleSet, iterCount>>
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 2
       /\ Cardinality({m \in msg : m.destination = p}) = SampleSetSize
       /\ LET Tally == [c \in Color |-> Cardinality({m \in msg : m.dest = p /\ m.plabel = c})]
              ONWIN(r) == color' = [color EXCEPT ![CHOOSE n \in Node : <<p, n>> \in HostMapping] = r]
              ONWIN2 == color' = color
          IN \E r \in Color : Tally[r] >= PickFlipThreshold => ONWIN(r) /\ color' = [n \in Node |-> IF <<p, n>> \in HostMapping /\ color[n] = NoColor THEN r ELSE color[n]]
             \/ (\A r \in Color : Tally[r] < PickFlipThreshold) => ONWIN2
       /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
       /\ iterCount' = [iterCount EXCEPT ![p] = iterCount[p] + 1]
       /\ pc' = [pc EXCEPT ![p] = 3]

LoopTermination ==
  /\ UNCHANGED <<color, sampleSet, iterCount>>
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = 3
       /\ iterCount[p] >= SlushIterationCount
       /\ msg' = msg \cup [p |-> p]
       /\ pc' = [pc EXCEPT ![p] = 4]
  /\ UNCHANGED <<color, sampleSet, iterCount>>

QueryLoopExit ==
  /\ UNCHANGED <<color, sampleSet, iterCount>>
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = 1
       /\ \A p \in SlushLoopProcess : [p |-> p] \in msg
       /\ pc' = [pc EXCEPT ![q] = 4]
  /\ UNCHANGED <<color, sampleSet, iterCount>>

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
        \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(AssignColor) /\ WF_vars(RequireColor)
                 /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)
                 /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination)

\* The client always finishes (all nodes eventually colored), and every
\* process eventually reaches its terminal "done" state.
AllProcessesTerminate ==
  /\ <>(pc["Client"] = 1)
  /\ \A p \in SlushLoopProcess \cup SlushQueryProcess : <>(pc[p] = 4)

TypeInvariant == TypeOK
TerminationProperty == AllProcessesTerminate
====