---- MODULE Slush ----
EXTENDS Integers, FiniteSets

(* Slush is the simplest member of the Snow family of probabilistic consensus    *)
(* protocols (Team Rocket, 2018).  Nodes repeatedly sample random peers and      *)
(* adopt a sufficiently popular opinion, converging the network on one color.    *)
(* TLA+ has no probabilistic modeling, so this is an executable model of the     *)
(* protocol's control flow rather than a proof of convergence.                  *)

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Loop processes and query processes are paired with their host node through  *
(* HostMapping, a set of triples.  Uncolored is the sentinel for "no color".    *)

VARIABLES color, messages, pc, sample, iteration

vars == <<color, messages, pc, sample, iteration>>

TypeOK ==
  /\ color \in [Node -> {NoColor} \cup SlushQueryProcess]
  /\ messages \subseteq SlushMessage
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {NoMessage} -> {"idle", "sampling", "tallying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iteration \in [SlushLoopProcess -> 0..SlushIterationCount]

AllLoopProcesses == SlushLoopProcess
AllQueryProcesses == SlushQueryProcess

\* A loop process runs only once its host node has been assigned a color.
HostHasColor(lp) == \E n \in Node : <<lp, n, NoMessage>> \in HostMapping /\ color[n] # NoColor

QueryFor(lp) == {msg \in messages : msg.kind = "query" /\ msg.src = lp}
ReplyFor(lp) == {msg \in messages : msg.kind = "reply" /\ msg.dst = lp}

ReplyCounts(lp) ==
  [c \in SlushQueryProcess |-> Cardinality({msg \in ReplyFor(lp) : msg.arg = c})]

AllLoopDone == \A lp \in SlushLoopProcess : pc[lp] = "done"
AllQueryDone == \A qp \in SlushQueryProcess : pc[qp] = "done"

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {NoMessage}) |-> "idle"]
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ iteration = [lp \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node (an external request).
ClientAssignsColor ==
  /\ \E n \in Node, c \in SlushQueryProcess :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<messages, pc, sample, iteration>>

RequireColor(lp) ==
  /\ pc[lp] = "idle"
  /\ HostHasColor(lp)
  /\ pc' = [pc EXCEPT ![lp] = "ready"]
  /\ UNCHANGED <<color, messages, sample, iteration>>

\* A loop process samples a random set of peers and sends them a query.
QuerySampleSet(lp) ==
  /\ pc[lp] = "ready"
  /\ iteration[lp] < SlushIterationCount
  /\ \E S \in SUBSET AllQueryProcesses :
       /\ Cardinality(S) = SampleSetSize
       /\ sample' = [sample EXCEPT ![lp] = S]
  /\ messages' = messages \cup { [kind |-> "query", src |-> lp, dst |-> qp, arg |-> color[CHOOSE n \in Node : <<lp, n, NoMessage>> \in HostMapping] ] : qp \in sample[lp] }
  /\ pc' = [pc EXCEPT ![lp] = "sampling"]
  /\ UNCHANGED <<color, iteration>>

\* A query process adopts the queryer's color if uncolored, then replies.
RespondToQuery(qp) ==
  /\ pc[qp] = "idle"
  /\ \E msg \in messages :
       /\ msg.kind = "query" /\ msg.dst = qp
       /\ LET n == CHOOSE n \in Node : <<msg.src, n, NoMessage>> \in HostMapping
          IN color' = [color EXCEPT ![n] = IF color[n] = NoColor THEN msg.arg ELSE color[n]]
       /\ messages' = (messages \ {msg}) \cup { [kind |-> "reply", src |-> qp, dst |-> msg.src, arg |-> color[n] ] }
  /\ pc' = [pc EXCEPT ![qp] = "ready"]
  /\ UNCHANGED <<sample, iteration>>

\* The loop process counts replies; if one color is popular enough it flips.
TallyReplies(lp) ==
  /\ pc[lp] = "sampling"
  /\ \A qp \in sample[lp] : [kind |-> "reply", src |-> qp, dst |-> lp, arg |-> NoMessage] \in messages
  /\ \E c \in SlushQueryProcess :
       /\ ReplyCounts(lp)[c] >= PickFlipThreshold
       /\ color' = [color EXCEPT ![CHOOSE n \in Node : <<lp, n, NoMessage>> \in HostMapping] = c]
  /\ messages' = { msg \in messages : msg.dst # lp }
  /\ pc' = [pc EXCEPT ![lp] = "tallying"]
  /\ UNCHANGED <<sample, iteration>>

LoopTermination(lp) ==
  /\ pc[lp] = "tallying"
  /\ iteration[lp] + 1 = SlushIterationCount
  /\ messages' = messages \cup { [kind |-> "done", src |-> lp, dst |-> NoMessage, arg |-> NoMessage] }
  /\ pc' = [pc EXCEPT ![lp] = "done"]
  /\ iteration' = [iteration EXCEPT ![lp] = iteration[lp] + 1]
  /\ UNCHANGED <<color, sample>>

QueryLoopExit(qp) ==
  /\ pc[qp] = "ready"
  /\ AllLoopDone
  /\ pc' = [pc EXCEPT ![qp] = "done"]
  /\ UNCHANGED <<color, messages, sample, iteration>>

Next ==
  \/ ClientAssignsColor
  \/ \E lp \in AllLoopProcesses : RequireColor(lp)
  \/ \E lp \in AllLoopProcesses : QuerySampleSet(lp)
  \/ \E qp \in AllQueryProcesses : RespondToQuery(qp)
  \/ \E lp \in AllLoopProcesses : TallyReplies(lp)
  \/ \E lp \in AllLoopProcesses : LoopTermination(lp)
  \/ \E qp \in AllQueryProcesses : QueryLoopExit(qp)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E qp \in AllQueryProcesses : RespondToQuery(qp))
          /\ WF_vars(\E lp \in AllLoopProcesses : LoopTermination(lp))

\* The invariant checks purely syntactic/structural properties: every node has a
\* color or NoColor, and every in-flight message conforms to the protocol grammar.
TypeInvariant == TypeOK

Termination == AllLoopDone /\ AllQueryDone

====