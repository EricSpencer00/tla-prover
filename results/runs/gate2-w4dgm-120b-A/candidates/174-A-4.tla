---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* The Slush protocol is the simplest member of the Snow family of          *)
(* probabilistic consensus protocols.  Nodes run two interlocked processes:    *)
(* a loop process that repeatedly samples random peers and adopts a           *)
(* sufficiently popular opinion, and a query process that replies to          *)
(* queries (adopting the query's color if the node is still uncolored).       *)

CONSTANTS
  Node,               \* the set of nodes in the network
  SlushLoopProcess,   \* the set of loop processes (one per node)
  SlushQueryProcess,  \* the set of query processes (one per node)
  HostMapping,        \* a set of triples <<node, loopProc, queryProc>>
  SlushIterationCount,\* how many sample rounds a loop process takes
  SampleSetSize,      \* how many peers a loop process queries per round
  PickFlipThreshold,  \* votes needed to adopt a color
  NoColor,            \* a node that has not yet been colored
  NoMessage           \* a loop process that has no message in flight

VARIABLES
  color,        \* color[n] : node -> its current color or NoColor
  message,      \* in-flight messages (queries, replies, terminations)
  procPC,       \* program counter for each process (where it is)
  sampleSet,    \* sampleSet[lp] : peers queried by loop process lp this round
  lpIterations  \* lpIterations[lp] : rounds loop process lp has completed

vars == <<color, message, procPC, sampleSet, lpIterations>>

MessageDomain ==
  { <<"query", lp, qp, col>> : lp \in SlushLoopProcess, qp \in SlushQueryProcess,
                                col \in {0, 1}
  } \cup
  { <<"reply", lp, qp, col>> : lp \in SlushLoopProcess, qp \in SlushQueryProcess,
                                col \in {0, 1}
  } \cup
  { <<"done", lp>> : lp \in SlushLoopProcess }

LoopProc(n) == CHOOSE lp \in SlushLoopProcess : \E qp \in SlushQueryProcess : <<n, lp, qp>> \in HostMapping
QueryProc(n) == CHOOSE qp \in SlushQueryProcess : \E lp \in SlushLoopProcess : <<n, lp, qp>> \in HostMapping

TypeOK ==
  /\ color \in [Node -> {NoColor, 0, 1}]
  /\ message \subseteq MessageDomain
  /\ procPC \in [SlushLoopProcess \cup SlushQueryProcess -> {"idle", "waiting", "done", NoMessage}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ lpIterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ message = {}
  /\ procPC = [p \in SlushLoopProcess \cup SlushQueryProcess |-> "idle"]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ lpIterations = [lp \in SlushLoopProcess |-> 0]

\* Client request: assign an initial color to an uncolored node.
AssignColor ==
  \E n \in Node, col \in {0, 1} :
    /\ color[n] = NoColor
    /\ color' = [color EXCEPT ![n] = col]
    /\ UNCHANGED <<message, procPC, sampleSet, lpIterations>>

RequireColor ==
  \E lp \in SlushLoopProcess :
    /\ procPC[lp] = "idle"
    /\ color[LoopProc(lp)] # NoColor
    /\ procPC' = [procPC EXCEPT ![lp] = "waiting"]
    /\ UNCHANGED <<color, message, sampleSet, lpIterations>>

\* Loop process selects a random sample of peers (size fixed by constant).
QuerySampleSet ==
  \E lp \in SlushLoopProcess :
    /\ procPC[lp] = "waiting"
    /\ lpIterations[lp] < SlushIterationCount
    /\ Cardinality(sampleSet[lp]) < SampleSetSize
    /\ \E qp \in SlushQueryProcess \ sampleSet[lp] :
         /\ sampleSet' = [sampleSet EXCEPT ![lp] = @ \cup {qp}]
         /\ message' = message \cup {<<"query", lp, qp, color[LoopProc(lp)]>>}
    /\ UNCHANGED <<color, procPC, lpIterations>>

\* Query process replies, adopting the color if it is still uncolored.
RespondToQuery ==
  \E qp \in SlushQueryProcess :
    \E m \in message :
      /\ m[1] = "query" /\ m[3] = qp
      /\ LET lp == m[2] IN
           /\ color' = [color EXCEPT ![LoopProc(lp)] =
                            IF color[LoopProc(lp)] = NoColor THEN m[4] ELSE @]
           /\ message' = (message \ {m}) \cup {<<"reply", lp, qp, color[LoopProc(lp)]>>}
      /\ UNCHANGED <<procPC, sampleSet, lpIterations>>

TallyReplies ==
  \E lp \in SlushLoopProcess :
    /\ Cardinality(sampleSet[lp]) = SampleSetSize
    /\ \A qp \in sampleSet[lp] : <<"reply", lp, qp, color[LoopProc(lp)]>> \in message
    /\ LET count0 == Cardinality({qp \in sampleSet[lp] :
                                    <<"reply", lp, qp, 0>> \in message})
        count1 == Cardinality({qp \in sampleSet[lp] :
                                    <<"reply", lp, qp, 1>> \in message}) IN
         color' = [color EXCEPT ![LoopProc(lp)] =
                      IF count0 >= PickFlipThreshold THEN 0
                      ELSE IF count1 >= PickFlipThreshold THEN 1
                      ELSE color[LoopProc(lp)]]
    /\ message' = message \ {m \in message : m[1] = "reply" /\ m[2] = lp}
    /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
    /\ lpIterations' = [lpIterations EXCEPT ![lp] = @ + 1]
    /\ UNCHANGED procPC

LoopTermination ==
  \E lp \in SlushLoopProcess :
    /\ procPC[lp] = "waiting"
    /\ lpIterations[lp] = SlushIterationCount
    /\ message' = message \cup {<<"done", lp>>}
    /\ procPC' = [procPC EXCEPT ![lp] = "done"]
    /\ UNCHANGED <<color, sampleSet, lpIterations>>

QueryLoopExit ==
  \E qp \in SlushQueryProcess :
    /\ procPC[qp] = "idle"
    /\ \A lp \in SlushLoopProcess : <<"done", lp>> \in message
    /\ procPC' = [procPC EXCEPT ![qp] = "done"]
    /\ UNCHANGED <<color, message, sampleSet, lpIterations>>

Next ==
  \/ AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
  \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(AssignColor) /\ WF_vars(RequireColor) /\ WF_vars(QuerySampleSet)
  /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies)
  /\ WF_vars(LoopTermination) /\ WF_vars(QueryLoopExit)

\* The loop process waits for every reply before it may re-evaluate; this
\* per-round progress guarantee is what bounds the message count so that
\* weak fairness suffices for the rest of the actions.
ProtocolProgress == \A lp \in SlushLoopProcess : (procPC[lp] = "waiting") ~> (procPC[lp] = "done")

TypeInvariant == TypeOK
\* Liveness: every process eventually reaches its done state.  Convergence
\* to a single color is a probabilistic guarantee and is not expressible here.
ProtocolTermination == ProtocolProgress

====