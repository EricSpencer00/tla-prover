---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Slush is the simplest member of the Snow family of probabilistic *)
(* consensus protocols (the Avalanche whitepaper describes it).  Each  *)
(* node hosts a loop process that samples random peers until a color   *)
(* reaches the flip threshold, at which point it adopts that color and *)
(* metastably stabilizes.  PlusCal is used for the action syntax and    *)
(* the spec translates one-to-one to TLA+.                              *)

CONSTANTS
  Node,               \* the set of participating nodes
  SlushLoopProcess,   \* one loop process per node, driving Slush rounds
  SlushQueryProcess,  \* one query process per node, answering queries
  HostMapping,        \* {(loop, query, node)} linking processes to nodes
  SlushIterationCount, \* max iteration per loop process
  SampleSetSize,      \* size of each peer sample
  PickFlipThreshold,  \* replies of one color needed to flip
  NoColor,            \* sentinel meaning "uncolored"
  NoMessage           \* sentinel meaning "no in-flight message"

\* Messages are sent over an unordered set, modeling an asynchronous network
\* where replies can be reordered or delayed.
Message == [kind: {"query", "reply", "termination"}, to: SlushQueryProcess \cup SlushLoopProcess, from: SlushLoopProcess, payload: Node \cup NoColor]

VARIABLES
  nodeColor,      \* [Node -> {NoColor} \cup {"color1", "color2"}] current color per node
  messageSet,     \* set of in-flight Message instances
  pc,             \* [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"idle","active","done"}]
  sample,         \* [SlushLoopProcess -> SUBSET SlushQueryProcess] peers sampled this round
  iteration       \* [SlushLoopProcess -> 0..SlushIterationCount] rounds completed

vars == <<nodeColor, messageSet, pc, sample, iteration>>

TypeOK ==
  /\ nodeColor \in [Node -> {NoColor} \cup {"color1", "color2"}]
  /\ messageSet \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"idle", "active", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ messageSet = {}
  /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "idle"]
  /\ sample = [q \in SlushLoopProcess |-> {}]
  /\ iteration = [q \in SlushLoopProcess |-> 0]

\* Client assigns an initial color to an uncolored node (external request).
AssignColor ==
  /\ pc["client"] = "idle"
  /\ \E n \in Node, c \in {"color1", "color2"} :
       /\ nodeColor[n] = NoColor
       /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = "active"]
  /\ UNCHANGED <<messageSet, sample, iteration>>

BeginLoop ==
  \/ \E lp \in SlushLoopProcess, n \in Node :
       /\ pc[lp] = "idle"
       /\ \E a \in HostMapping : a[1] = lp /\ nodeColor[n] = a[3]
       /\ pc' = [pc EXCEPT ![lp] = "active"]
       /\ UNCHANGED <<nodeColor, messageSet, sample, iteration>>
  \/ UNCHANGED pc

\* A loop process queries a random sample of peers, sending its color to each.
QuerySample ==
  \E lp \in SlushLoopProcess :
    /\ pc[lp] = "active"
    /\ iteration[lp] < SlushIterationCount
    /\ sample[lp] = {}
    /\ nodeColor' = nodeColor
    /\ sample' = [sample EXCEPT ![lp] = CHOOSE qSet \in SUBSET SlushQueryProcess :
                                            Cardinality(qSet) = SampleSetSize]
    /\ messageSet' = messageSet \cup
         {[kind |-> "query", to |-> q, from |-> lp, payload |-> nodeColor[CHOOSE n \in Node : \E a \in HostMapping : a[1] = lp /\ a[3] = n]} : q \in sample[lp]}
    /\ UNCHANGED <<pc, iteration>>

\* A query process adopts the query's color if uncolored, then replies.
RespondQuery ==
  \E rq \in messageSet :
    /\ rq.kind = "query"
    /\ \E qp \in SlushQueryProcess :
         /\ rq.to = qp
         /\ nodeColor' = [nodeColor EXCEPT ![CHOOSE n \in Node : \E a \in HostMapping : a[2] = qp /\ a[3] = n] =
                           IF nodeColor[CHOOSE n \in Node : \E a \in HostMapping : a[2] = qp /\ a[3] = n] = NoColor
                           THEN rq.payload
                           ELSE nodeColor[CHOOSE n \in Node : \E a \in HostMapping : a[2] = qp /\ a[3] = n]]
         /\ messageSet' = (messageSet \ {rq}) \cup {[kind |-> "reply", to |-> rq.from, from |-> qp, payload |-> nodeColor[CHOOSE n \in Node : \E a \in HostMapping : a[2] = qp /\ a[3] = n]]}
    /\ UNCHANGED <<pc, sample, iteration>>

\* Once every sampled peer has replied, the loop process tallies and flips
\* if a color reaches the flip threshold.
TallyReplies ==
  \E lp \in SlushLoopProcess :
    /\ pc[lp] = "active"
    /\ sample[lp] # {}
    /\ \A q \in sample[lp] : [kind |-> "reply", to |-> lp, from |-> q, payload |-> NoMessage] \notin messageSet
    /\ LET tally == [c \in {"color1", "color2"} |-> Cardinality({q \in sample[lp] : [kind |-> "reply", to |-> lp, from |-> q, payload |-> c] \in messageSet})] IN
         nodeColor' = IF \E c \in {"color1", "color2"} : tally[c] >= PickFlipThreshold
                      THEN LET best == CHOOSE c \in {"color1", "color2"} : tally[c] >= PickFlipThreshold
                           IN [nodeColor EXCEPT ![CHOOSE n \in Node : \E a \in HostMapping : a[1] = lp /\ a[3] = n] = best]
                      ELSE nodeColor
    /\ sample' = [sample EXCEPT ![lp] = {}]
    /\ iteration' = [iteration EXCEPT ![lp] = iteration[lp] + 1]
    /\ UNCHANGED <<pc, messageSet>>

\* After completing its rounds the loop process broadcasts termination.
TerminateLoop ==
  \E lp \in SlushLoopProcess :
    /\ pc[lp] = "active"
    /\ iteration[lp] = SlushIterationCount
    /\ sample[lp] = {}
    /\ messageSet' = messageSet \cup {[kind |-> "termination", to |-> NoMessage, from |-> lp, payload |-> NoMessage]}
    /\ pc' = [pc EXCEPT ![lp] = "done"]
    /\ UNCHANGED <<nodeColor, sample, iteration>>

BroadcastTermination == TerminateLoop

\* Query processes stop once every loop process has terminated.
QueryLoopExit ==
  /\ \A lp \in SlushLoopProcess : pc[lp] = "done"
  /\ pc' = [q \in SlushQueryProcess |-> "done"]
  /\ UNCHANGED <<nodeColor, messageSet, sample, iteration>>

Next ==
  \/ AssignColor
  \/ BeginLoop
  \/ QuerySample
  \/ RespondQuery
  \/ TallyReplies
  \/ BroadcastTermination
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(BeginLoop) /\ WF_vars(QuerySample) /\ WF_vars(RespondQuery) /\ WF_vars(TallyReplies) /\ WF_vars(BroadcastTermination) /\ WF_vars(QueryLoopExit)

\* Safety: the node-color map and every in-flight message are well-typed.
TypeInvariant ==
  /\ TypeOK
  /\ \A m \in messageSet : m.kind \in {"query", "reply", "termination"}

\* Liveness: all processes eventually reach their done state.
Termination == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : pc[p] = "done")

====