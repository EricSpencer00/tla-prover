---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Slush is the simplest Snow-family protocol: loop processes query random peers *)
(* and adopt a popular color, converging to a single decision.  TLA+ has no     *)
(* probabilistic semantics, so this spec is executable pseudocode checking only  *)
(* type safety and termination of the protocol machinery.                     *)

CONSTANTS
  Node,                 \* the network nodes
  SlushLoopProcess,     \* the loop process driving each node's iteration
  SlushQueryProcess,    \* the query process answering peer queries
  HostMapping,          \* { <<p, n, q>> } links a loop and its query process to a node
  SlushIterationCount,  \* #iterations each loop process performs
  SampleSetSize,        \* number of peers sampled per query round
  PickFlipThreshold,    \* #matching replies needed to adopt a color
  NoColor,              \* the uncolored marker
  NoMessage             \* sentinel for "no message"

\* pc: Where each process is in its own protocol cycle
\* color: each node's current opinion; message: the in-flight network
\* sampleSet: which peers the current round queried; iteration: rounds done
VARIABLES color, message, pc, sampleSet, iteration

TypeOK ==
  /\ color \in [Node -> Node \cup {NoColor}]
  /\ message \subseteq (SlushLoopProcess \X SlushQueryProcess \X (Node \cup {NoMessage}))
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {NoColor} -> {"queryLoop", "waiting", "querying", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ message = {}
  /\ pc = [x \in (SlushLoopProcess \cup SlushQueryProcess \cup {NoColor}) |-> IF x \in SlushQueryProcess THEN "queryLoop" ELSE "waiting"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ iteration = [p \in SlushLoopProcess |-> 0]

\* External client assigns a random initial color to an uncolored node.
AssignColor ==
  /\ \E n \in Node, c \in Node :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<message, pc, sampleSet, iteration>>

RequireColor ==
  /\ \E p \in SlushLoopProcess, n \in Node, q \in SlushQueryProcess :
       /\ <<p, n, q>> \in HostMapping
       /\ pc[p] = "waiting"
       /\ color[n] # NoColor
       /\ pc' = [pc EXCEPT ![p] = "querying"]
  /\ UNCHANGED <<color, message, sampleSet, iteration>>

\* An iteration round: choose peers and send them a query message.
QuerySampleSet ==
  /\ \E p \in SlushLoopProcess, n \in Node, q \in SlushQueryProcess, peers \in SUBSET SlushQueryProcess :
       /\ <<p, n, q>> \in HostMapping
       /\ pc[p] = "querying"
       /\ iteration[p] < SlushIterationCount
       /\ Cardinality(peers) = SampleSetSize
       /\ sampleSet' = [sampleSet EXCEPT ![p] = peers]
       /\ message' = message \cup { <<p, r, color[n]>> : r \in peers }
  /\ UNCHANGED <<color, pc, iteration>>

\* A queried node adopts the query's color if needed, then replies.
RespondToQuery =
  /\ \E r \in SlushQueryProcess, p \in SlushLoopProcess, n \in Node, c \in Node \cup {NoMessage} :
       /\ <<p, n, r>> \in HostMapping
       /\ <<p, r, c>> \in message
       /\ color' = [color EXCEPT ![n] = IF color[n] = NoColor THEN c ELSE color[n]]
       /\ message' = (message \ {<<p, r, c>>}) \cup {<<p, r, color[n]>>}
  /\ UNCHANGED <<pc, sampleSet, iteration>>

\* Once every sampled peer has replied, adopt a popular color if it passes.
TallyReplies ==
  /\ \E p \in SlushLoopProcess, n \in Node, q \in SlushQueryProcess :
       /\ <<p, n, q>> \in HostMapping
       /\ pc[p] = "querying"
       /\ sampleSet[p] # {}
       /\ \A r \in sampleSet[p] : <<p, r, color[n]>> \in message
       /\ LET count(x) == Cardinality({r \in sampleSet[p] : <<p, r, x>> \in message})
          IN color' = [color EXCEPT ![n] = IF count(color[n]) >= PickFlipThreshold THEN color[n] ELSE IF \E x \in Node : count(x) >= PickFlipThreshold THEN x ELSE color[n]]
       /\ message' = {m \in message : m[1] # p}
       /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
       /\ iteration' = [iteration EXCEPT ![p] = iteration[p] + 1]
  /\ UNCHANGED pc

LoopTermination ==
  /\ \E p \in SlushLoopProcess, n \in Node, q \in SlushQueryProcess :
       /\ <<p, n, q>> \in HostMapping
       /\ pc[p] = "querying"
       /\ iteration[p] = SlushIterationCount
       /\ pc' = [pc EXCEPT ![p] = "done"]
       /\ message' = message \cup {<<p, s, NoMessage>> : s \in SlushQueryProcess}
  /\ UNCHANGED <<color, sampleSet, iteration>>

QueryLoopExit ==
  /\ \A r \in SlushQueryProcess : pc[r] = "queryLoop"
  /\ \E s \in SlushQueryProcess :
       /\ pc' = [pc EXCEPT ![s] = "done"]
  /\ UNCHANGED <<color, message, sampleSet, iteration>>

Next ==
  \/ AssignColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTermination
  \/ QueryLoopExit

Spec ==
  /\ Init
  /\ [][Next]_<<color, message, pc, sampleSet, iteration>>
  /\ WF_Vars(AssignColor)
  /\ WF_Vars(RequireColor)
  /\ WF_Vars(QuerySampleSet)
  /\ WF_Vars(RespondToQuery)
  /\ WF_Vars(TallyReplies)
  /\ WF_Vars(LoopTermination)
  /\ WF_Vars(QueryLoopExit)

\* Only structural discipline is checked: message shape, and every process      *)
\* eventually reaches its done state (termination of the protocol itself,   *)
\* not the stochastic convergence Slush aims for).                           *
TypeInvariant == TypeOK
ProtocolTerminates == \A x \in (SlushLoopProcess \cup SlushQueryProcess) : <>(pc[x] = "done")
====