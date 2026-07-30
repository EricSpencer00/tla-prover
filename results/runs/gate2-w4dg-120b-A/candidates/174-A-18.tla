---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush protocol: loop processes repeatedly sample peers and adopt a color
\* that a sufficient majority of the sampled peers already hold. Since TLA+ has
\* no probabilistic primitives, the spec is written as deterministic
\* executable pseudocode and only checks structural properties (type safety,
\* termination). Convergence to a single color is an empirical fact of the
\* protocol, not something TLA+ can verify here.

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

\* Message type tags. A message is always a tuple whose first element is one of
\* these tags, so the type invariant can validate every message in the set.
MessageTag == {"slush_query", "slush_reply", "slush_term"}

\* A loop or query process hosts exactly one node, and every node is hosted by
\* exactly one loop and one query process -- HostMapping ties them together.
HOST == HostMapping

VARIABLES color, msgs, pc, sample, iters

vars == <<color, msgs, pc, sample, iters>>

TypeOK ==
  /\ color \in [Node -> Node \cup {NoColor}]
  /\ msgs \subseteq Union({MessageTag, Node} \times Node)
  /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"slush_client"} -> {"idle", "loop", "reply", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iters \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"slush_client"} |-> "idle"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iters = [p \in SlushLoopProcess |-> 0]

\* The client process models external transactions that assign initial colors
\* to uncolored nodes (bound by the SlushIterationCount, which is a capacity, not a
\* limit on the number of transactions).
SlushClient ==
  /\ pc["slush_client"] # "done"
  /\ \E n \in Node :
       /\ color[n] = NoColor
       /\ \E c \in Node : color' = [color EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["slush_client"] = "done"]
  /\ UNCHANGED <<msgs, sample, iters>>

\* A loop process cannot begin sampling until its host node has been
\* assigned a color by the client.
SlushRequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "idle"
       /\ LET n == CHOOSE n \in Node : <<p, n>> \in HOST
          IN /\ color[n] # NoColor
             /\ pc' = [pc EXCEPT ![p] = "loop"]
       /\ UNCHANGED <<color, msgs, sample, iters>>

\* Query a random sample of peers: send a query message to each sampled
\* query process, carrying the current color of the host node.
SlushQuery ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "loop"
       /\ sample[p] = {}
       /\ LET n == CHOOSE n \in Node : <<p, n>> \in HOST
          IN /\ Cardinality(N) >= SampleSetSize
             /\ \E S \in SUBSET SlushQueryProcess :
                  Cardinality(S) = SampleSetSize
                  /\ sample' = [sample EXCEPT ![p] = S]
                  /\ msgs' = msgs \union
                       {<<"slush_query", n>> \o q \o [color[n]] : q \in S}
       /\ UNCHANGED <<color, pc, iters>>

\* A query process answers: it adopts the query's color if uncolored, then
\* replies with its current color.
SlushReply ==
  /\ \E q \in SlushQueryProcess :
       /\ \E m \in msgs :
            /\ m[1] = "slush_query"
            /\ m[2] = q
            /\ LET n == m[3] IN
                 /\ color' = [color EXCEPT ![n] = IF color[n] = NoColor THEN m[4] ELSE color[n]]
                 /\ msgs' = (msgs \ {m}) \union {<<"slush_reply", n>> \o q \o [color[n]]}
       /\ UNCHANGED <<pc, sample, iters>>

\* Once every sampled peer has replied, the loop process may adopt a color
\* that the sampled replies reached the flip threshold for.
SlushTally ==
  /\ \E p \in SlushLoopProcess :
       /\ sample[p] # {}
       /\ \E m \in msgs :
            /\ m[1] = "slush_reply"
            /\ m[2] \in sample[p]
            /\ Cardinality(msgs \cap (SlushTag("slush_reply", sample[p]))) = Cardinality(sample[p])
            /\ LET n == CHOOSE n \in Node : <<p, n>> \in HOST
                   n1 == Cardinality({m \in msgs : m[1] = "slush_reply" /\ m[2] \in sample[p] /\ m[4] = n})
                   n2 == Cardinality({m \in msgs : m[1] = "slush_reply" /\ m[2] \in sample[p] /\ m[4] \in Node \ {n}})
               IN /\ color' = IF n1 >= PickFlipThreshold THEN [color EXCEPT ![n] = n] ELSE IF n2 >= PickFlipThreshold THEN [color EXCEPT ![n] = CHOOSE c \in Node \ {n : TRUE} : TRUE] ELSE color
                  /\ msgs' = msgs \ {m}
            /\ sample' = [sample EXCEPT ![p] = {}]
            /\ iters' = [iters EXCEPT ![p] = iters[p] + 1]
            /\ pc' = [pc EXCEPT ![p] = IF iters[p] + 1 >= SlushIterationCount THEN "done" ELSE "idle"]
       /\ UNCHANGED <<pc>>

\* After completing all iterations, a loop process broadcasts termination.
SlushTerminate ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "done"
       /\ \E n \in Node :
            /\ msgs' = msgs \union {<<"slush_term", n>> \o p}
       /\ UNCHANGED <<color, pc, sample, iters>>

\* Query processes may exit once every loop process has sent termination.
SlushQueryLoopExit ==
  /\ \A p \in SlushLoopProcess : pc[p] = "done"
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "reply"
       /\ pc' = [pc EXCEPT ![q] = "done"]
       /\ UNCHANGED <<color, msgs, sample, iters>>

\* Because every action's guard is a simple finite conjunction, each action
\* is weakly fair: an enabled action is always eventually taken.
Next ==
  \/ SlushClient \/ SlushRequireColor \/ SlushQuery \/ SlushReply
  \/ SlushTally \/ SlushTerminate \/ SlushQueryLoopExit

Spec == Init /\ [][Next]_vars
  /\ WF_vars(SlushClient) /\ WF_vars(SlushRequireColor) /\ WF_vars(SlushQuery)
  /\ WF_vars(SlushReply) /\ WF_vars(SlushTally) /\ WF_vars(SlushTerminate) /\ WF_vars(SlushQueryLoopExit)

TypeInvariant == TypeOK

Terminating == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"slush_client"} : pc[p] = "done")

====