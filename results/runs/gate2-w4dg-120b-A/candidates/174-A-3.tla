---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush (the simplest Snow family protocol) modeled in PlusCal. The spec
\* does not capture the probabilistic convergence guarantees -- only the
\* structural choreography: nodes get colors, loop processes sample peers,
\* query processes reply (adopting the query color if they were uncolored),
\* and loop processes flip their own color when a sampled majority is found.
CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

VARIABLES
  \* color: each node's current color (or NoColor if uncolored).
  \* msgs: in-flight protocol messages; pc: each process' program counter;
  \* sample: the peer set each loop process is currently polling;
  \* iters: how many sampling rounds each loop process has completed.
  color, msgs, pc, sample, iters

vars == <<color, msgs, pc, sample, iters>>

Range(f) == { f[x] : x \in DOMAIN f }

Message == [kind: {"query", "reply", "terminate"},
            from: SlushLoopProcess, to: SlushQueryProcess, c: {NoColor} \cup {0, 1}]
LoopReady == { p \in SlushLoopProcess : pc[p] = "waitColor" }

TypeOK ==
  /\ color \in [Node -> {NoColor, 0, 1}]
  /\ msgs \subseteq Message
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"slushClient"} -> {"init", "waitColor", "querying", "tallying", "done", "replying", "queryDone"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [x \in SlushLoopProcess \cup SlushQueryProcess \cup {"slushClient"} |-> "init"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iters = [p \in SlushLoopProcess |-> 0]

\* The client process assigns an initial color to an uncolored node.
AssignColor ==
  /\ pc["slushClient"] = "init"
  /\ \E n \in Node, c \in {0, 1} :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["slushClient"] = IF \E n \in Node : color[n] = NoColor
                                    THEN "init" ELSE "waitColor"]
  /\ UNCHANGED <<msgs, sample, iters>>

\* A loop process is allowed to start iteration only once its host node is colored.
RequireColor(p) ==
  /\ pc[p] = "init"
  /\ \E n \in Node : <<p, n>> \in HostMapping /\ color[n] # NoColor
  /\ pc' = [pc EXCEPT ![p] = "waitColor"]
  /\ UNCHANGED <<color, msgs, sample, iters>>

\* A loop process selects a random sample of peers and sends query messages.
QueryPeers(p) ==
  /\ pc[p] = "waitColor"
  /\ iters[p] < SlushIterationCount
  /\ sample' = [sample EXCEPT ![p] = CHOOSE s \in SUBSET SlushQueryProcess :
                      Cardinality(s) = SampleSetSize
                      /\ \A q \in s : \A q2 \in s : q2 # q => q2 # q]
                     /\
                     \A p2 \in SlushLoopProcess : IF p2 = p THEN s ELSE sample[p2]]
  /\ msgs' = msgs \cup { [kind |-> "query", from |-> p, to |-> q,
                           c |-> color[RANGE HostMapping][p]]
                         : q \in sample[p] }
  /\ pc' = [pc EXCEPT ![p] = "querying"]
  /\ UNCHANGED <<color, iters>>

\* A query process adopts the query's color when uncolored, then replies.
ReplyToQuery(q) ==
  /\ \E m \in msgs :
       /\ m.to = q
       /\ msgs' = (msgs \ {m}) \cup
                {[kind |-> "reply", from |-> m.from, to |-> q, c |-
                  IF color[RANGE HostMapping][q] = NoColor THEN m.c ELSE color[RANGE HostMapping][q]]}
  /\ pc' = [pc EXCEPT ![q] = "replying"]
  /\ UNCHANGED <<color, sample, iters>>

\* The loop process tallies replies and flips its node's color if the flip
\* threshold is reached. It advances its iteration counter.
TallyAndFlip(p) ==
  /\ pc[p] = "querying"
  /\ \A q \in sample[p] : \E m \in msgs : m.kind = "reply" /\ m.to = q /\ m.from = p
  /\ LET colors == [k \in {0, 1} |->
                      Cardinality({ m \in msgs : m.kind = "reply" /\ m.from = p /\ m.c = k })]
     IN
       /\ \E c \in {0, 1} : colors[c] >= PickFlipThreshold /\ color' = [color EXCEPT ![RANGE HostMapping][p] = c]
       /\ msgs' = msgs \ { m \in msgs : m.kind = "reply" /\ m.from = p }
       /\ pc' = [pc EXCEPT ![p] = "tallying"]
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ iters' = [iters EXCEPT ![p] = iters[p] + 1]

\* Having tallied, the loop process returns to the waiting state.
LoopRepeat(p) ==
  /\ pc[p] = "tallying"
  /\ pc' = [pc EXCEPT ![p] = "waitColor"]
  /\ UNCHANGED <<color, msgs, sample, iters>>

\* A loop process that has exhausted its iteration budget sends a termination message.
TerminateLoop(p) ==
  /\ pc[p] \in {"waitColor", "done"}
  /\ iters[p] = SlushIterationCount
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ msgs' = msgs \cup { [kind |-> "terminate", from |-> p, to |-> q, c |-> NoColor]
                         : q \in SlushQueryProcess }
  /\ UNCHANGED <<color, sample, iters>>

\* A query process closes its reply loop when every loop process has terminated.
QueryLoopExit(q) ==
  /\ pc[q] \in {"replying", "queryDone"}
  /\ LoopReady = SlushLoopProcess
  /\ pc' = [pc EXCEPT ![q] = "queryDone"]
  /\ UNCHANGED <<color, msgs, sample, iters>>

Next ==
  \/ AssignColor
  \/ \E p \in SlushLoopProcess : RequireColor(p) \/ QueryPeers(p) \/ TallyAndFlip(p) \/ LoopRepeat(p) \/ TerminateLoop(p)
  \/ \E q \in SlushQueryProcess : ReplyToQuery(q) \/ QueryLoopExit(q)

Spec == Init /\ [][Next]_vars

\* The spec must be both type-safe and terminating (no process stuck).
TypeInvariant == TypeOK
AllProcessesTerminate ==
  /\ LoopReady = SlushLoopProcess
  /\ \A q \in SlushQueryProcess : pc[q] = "queryDone"
  /\ \A p \in SlushLoopProcess : pc[p] = "done"

====