---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Slush is the simplest member of the Snow family of probabilistic consensus   *)
(* protocols (Team Rocket, 2018).  Each node runs two processes: a loop process  *)
(* that drives the metastable iteration, and a query process that answers       *)
(* queries from peers.  There is also a client request process that assigns the  *)
(* initial colors to uncolored nodes.  The loop process repeatedly samples a     *)
(* random subset of peers and adopts a color that reaches the flip threshold.    *)
(* Since TLA+ has no probabilistic reasoning, the "convergence to one color"    *)
(* guarantee is out of scope here; the model only checks type-correctness and    *)
(* that every process eventually reaches a done state.                          *)

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

VARIABLES colorOf, msgs, pc, sample, completedCount

vars == <<colorOf, msgs, pc, sample, completedCount>>

Query(r, n) == [type |-> "slushQuery", fromLoop |-> r, toQuery |-> n]
QueryReply(r, q, c) == [type |-> "slushQueryReply", fromQuery |-> q, toLoop |-> r, color |-> c]
TermMessage(r) == [type |-> "slushTerm", fromLoop |-> r]

TypeOK ==
  /\ colorOf \in [Node -> {NoColor} \cup (Node \ {NoColor})]
  /\ msgs \subseteq NoMessage \cup
       (UNION {[type |-> "slushQuery", fromLoop |-> r, toQuery |-> n] : r \in SlushLoopProcess, n \in Node} \cup
              {[type |-> "slushQueryReply", fromQuery |-> q, toLoop |-> r, color |-> c] : q \in SlushQueryProcess, r \in SlushLoopProcess, c \in {NoColor} \cup (Node \ {NoColor})} \cup
              {[type |-> "slushTerm", fromLoop |-> r] : r \in SlushLoopProcess})
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"slushClient"} -> {"init", "wait", "sampling", "tallying", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ completedCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ colorOf = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [r \in SlushLoopProcess |-> "wait"] @@ [q \in SlushQueryProcess |-> "replying"] @@ [r \in {"slushClient"} |-> "init"]
  /\ sample = [r \in SlushLoopProcess |-> {}]
  /\ completedCount = [r \in SlushLoopProcess |-> 0]

QueryLoop(n) == CHOOSE r \in SlushLoopProcess : <<r, n>> \in HostMapping
ReplyLoop(q) == CHOOSE n \in Node : <<q, n>> \in HostMapping

* Client assigns an initial color to an uncolored node.
AssignColor ==
  /\ pc["slushClient"] = "init"
  /\ \E n \in Node :
       /\ colorOf[n] = NoColor
       /\ \E c \in Node \ {NoColor} : colorOf' = [colorOf EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["slushClient"] = "init"]
  /\ UNCHANGED <<msgs, sample, completedCount>>

* A loop process waits until its host node has been assigned a color.
RequireColor ==
  /\ \E r \in SlushLoopProcess :
       /\ pc[r] = "wait"
       /\ colorOf[QueryLoop(r)] # NoColor
       /\ pc' = [pc EXCEPT ![r] = "sampling"]
  /\ UNCHANGED <<colorOf, msgs, sample, completedCount>>

* The loop process selects a random subset of peers and queries them.
QuerySampleSet ==
  /\ \E r \in SlushLoopProcess :
       /\ pc[r] = "sampling"
       /\ \E q \in Subsets(Node) :
            /\ Cardinality(q) = SampleSetSize
            /\ q # {}
            /\ sample' = [sample EXCEPT ![r] = q]
            /\ msgs' = msgs \cup {Query(r, n) : n \in q}
  /\ UNCHANGED <<colorOf, pc, completedCount>>

* A query process replies with its current color; if still uncolored it adopts
* the incoming query's color.
RespondToQuery ==
  /\ \E m \in msgs :
       /\ m.type = "slushQuery"
       /\ LET q == ReplyLoop(m.toQuery) IN
            /\ pc[q] = "replying"
            /\ colorOf' = IF colorOf[m.toQuery] = NoColor THEN ([colorOf EXCEPT ![m.toQuery] = m.fromLoop]) ELSE colorOf
            /\ msgs' = (msgs \ {m}) \cup {QueryReply(r, q, IF colorOf[m.toQuery] = NoColor THEN m.fromLoop ELSE colorOf[m.toQuery])}
  /\ UNCHANGED <<pc, sample, completedCount>>

* The loop process tallies the replies.  If one color reaches the flip
* threshold the node adopts it, otherwise it keeps its current color.
TallyReplies ==
  /\ \E r \in SlushLoopProcess :
       /\ pc[r] = "sampling"
       /\ \A n \in sample[r] : \E m \in msgs : m.type = "slushQueryReply" /\ m.toLoop = r /\ m.fromQuery = ReplyLoop(n)
       /\ LET colorCount(c) == Cardinality({n \in sample[r] : \E m \in msgs : m.type = "slushQueryReply" /\ m.toLoop = r /\ m.fromQuery = ReplyLoop(n) /\ m.color = c}) IN
            LET winner == IF \E c \in {NoColor} \cup (Node \ {NoColor}) : colorCount(c) >= PickFlipThreshold
                         THEN (CHOOSE c \in {NoColor} \cup (Node \ {NoColor}) : colorCount(c) >= PickFlipThreshold)
                         ELSE colorOf[QueryLoop(r)] IN
                colorOf' = [colorOf EXCEPT ![QueryLoop(r)] = winner]
       /\ msgs' = {m \in msgs : ~(m.type = "slushQueryReply" /\ m.toLoop = r)}
       /\ sample' = [sample EXCEPT ![r] = {}]
       /\ completedCount' = [completedCount EXCEPT ![r] = IF completedCount[r] < SlushIterationCount THEN completedCount[r] + 1 ELSE SlushIterationCount]
       /\ pc' = [pc EXCEPT ![r] = IF completedCount[r] < SlushIterationCount THEN "sampling" ELSE "done"]
  /\ UNCHANGED <<pc>>

* The loop process broadcasts a termination message once it has completed all
* iterations.
LoopTerminate ==
  /\ \E r \in SlushLoopProcess :
       /\ pc[r] = "done"
       /\ TermMessage(r) \notin msgs
       /\ msgs' = msgs \cup {TermMessage(r)}
  /\ UNCHANGED <<colorOf, pc, sample, completedCount>>

* The query process exits when all loop processes have terminated.
QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "replying"
       /\ \A r \in SlushLoopProcess : TermMessage(r) \in msgs
       /\ pc' = [pc EXCEPT ![q] = "done"]
  /\ UNCHANGED <<colorOf, msgs, sample, completedCount>>

Next ==
  \/ AssignColor
  \/ RequireColor
  \/ QuerySampleSet
  \/ RespondToQuery
  \/ TallyReplies
  \/ LoopTerminate
  \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(AssignColor) /\ WF_vars(RequireColor) /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTerminate) /\ WF_vars(QueryLoopExit)

* Every process eventually reaches its done state.
AllProcessesTerminate == <>(\A r \in SlushLoopProcess \cup SlushQueryProcess \cup {"slushClient"} : pc[r] = "done")

====