---- MODULE Slush ----
EXTENDS Naturals

\* This Slush spec is written in PlusCal and translated to TLA+; every
\* identifier below (constants, Spec, Init, Next, TypeInvariant, etc.)
\* must be present and named exactly as the reference configuration demands.
CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

\* A message is a four-field record; the first field is its tag, and the
\* remaining three fields are the participants (and the loop's current
\* color, when it is a query) -- every message in the system must match
\* this shape, which is what the type invariant checks.
Message == [tag : {"query", "qreply", "termination"},
            loop : SlushLoopProcess, query : SlushQueryProcess, val : Node \cup {NoColor}]

\* The state record is the full set of variables the spec manipulates.
Vars == [color : [Node -> Node \cup {NoColor}], messages : SUBSET Message,
         pc : [SlushLoopProcess \cup SlushQueryProcess -> {"init", "loop", "done",
                                                          "replyLoop", "replyDone"}],
         sample : [SlushLoopProcess -> SUBSET SlushQueryProcess],
         loopsDone : [SlushLoopProcess -> 0..SlushIterationCount],
         client : {"ready", "done"}]

TypeOK ==
    /\ color \in [Node -> Node \cup {NoColor}]
    /\ messages \subseteq Message
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess -> {"init", "loop", "done",
                                                          "replyLoop", "replyDone"}]
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ loopsDone \in [SlushLoopProcess -> 0..SlushIterationCount]
    /\ client \in {"ready", "done"}

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ messages = {}
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess |-> IF p \in SlushLoopProcess THEN "init" ELSE "replyLoop"]
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ loopsDone = [p \in SlushLoopProcess |-> 0]
    /\ client = "ready"

\* Tera: a client process assigns an initial color to an uncolored node.
ClientAssignColor(n, col) ==
    /\ client = "ready"
    /\ color[n] = NoColor
    /\ color' = [color EXCEPT ![n] = col]
    /\ UNCHANGED <<messages, pc, sample, loopsDone, client>>

\* Each loop process waits for its host node to be colored before iterating.
RequireColor(p) ==
    /\ pc[p] = "init"
    /\ \E n \in Node : <<p, n, NoMessage>> \in HostMapping /\ color[n] # NoColor
    /\ pc' = [pc EXCEPT ![p] = "loop"]
    /\ UNCHANGED <<color, messages, sample, loopsDone, client>>

\* The loop process selects a random sample of peers and queries them.
QuerySampleSet(p, Q) ==
    /\ pc[p] = "loop"
    /\ loopsDone[p] < SlushIterationCount
    /\ Cardinality(Q) = SampleSetSize
    /\ \A q \in Q : \E n \in Node : <<p, n, q>> \in HostMapping
    /\ LET c == (CHOOSE n \in Node : <<p, n, NoMessage>> \in HostMapping /\ color[n] # NoColor)
       IN messages' = messages \cup {[tag |-> "query", loop |-> p, query |-> q, val |-> c] : q \in Q}
    /\ sample' = [sample EXCEPT ![p] = Q]
    /\ UNCHANGED <<color, pc, loopsDone, client>>

\* A query process adopts the query color if it is still uncolored, then
\* replies with whatever color it holds now.
RespondToQuery(q) ==
    /\ \E m \in messages :
        /\ m.tag = "query" /\ m.query = q
        /\ LET n == (CHOOSE x \in Node : <<m.loop, x, q>> \in HostMapping)
               nc == IF color[n] = NoColor THEN m.val ELSE color[n]
           IN /\ color' = [color EXCEPT ![n] = nc]
              /\ messages' = (messages \ {m}) \cup {[tag |-> "qreply", loop |-> m.loop, query |-> q, val |-> nc]}
    /\ UNCHANGED <<pc, sample, loopsDone, client>>

\* Once every sampled peer has replied, the loop process counts votes and
\* adopts a color if it reaches the flip threshold.
TallyReplies(p) ==
    /\ sample[p] # {}
    /\ \E m \in messages :
        /\ m.tag = "qreply" /\ m.loop = p /\ m.query \in sample[p]
    /\ Cardinality(messages \cap {[tag |-> "qreply", loop |-> p, query |-> q, val |-> NoColor} : q \in sample[p]]) = Cardinality(sample[p])
    /\ LET ct == [c \in {color[q] : q \in Node} \cup {NoColor} |-> Cardinality(messages \cap {[tag |-> "qreply", loop |-> p, query |-> q, val |-> c} : q \in sample[p]])]
       IN IF \E c \in {color[q] : q \in Node} \cup {NoColor} : ct[c] >= PickFlipThreshold
             THEN LET n == (CHOOSE x \in Node : <<p, x, NoMessage>> \in HostMapping)
                  IN color' = [color EXCEPT ![n] = (CHOOSE c \in {color[q] : q \in Node} \cup {NoColor} : ct[c] >= PickFlipThreshold)]
             ELSE color' = color
    /\ sample' = [sample EXCEPT ![p] = {}]
    /\ loopsDone' = [loopsDone EXCEPT ![p] = loopsDone[p] + 1]
    /\ UNCHANGED <<messages, pc, client>>

\* A loop process that has completed all its iterations broadcasts a termination
\* message and goes idle.
LoopTermination(p) ==
    /\ pc[p] = "loop" /\ loopsDone[p] = SlushIterationCount
    /\ messages' = messages \cup {[tag |-> "termination", loop |-> p, query |-> NoMessage, val |-> NoMessage]}
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<color, sample, loopsDone, client>>

\* Once the network is quiet, query processes go idle together.
QueryLoopExit ==
    /\ \A p \in SlushLoopProcess : pc[p] = "done"
    /\ \A q \in SlushQueryProcess : pc[q] = "replyLoop"
    /\ pc' = [pc EXCEPT ![q \in SlushQueryProcess] = "replyDone"]
    /\ UNCHANGED <<color, messages, sample, loopsDone, client>>

Next ==
    \/ \E n \in Node, col \in {Node \cup {NoColor}} : ClientAssignColor(n, col)
    \/ \E p \in SlushLoopProcess : RequireColor(p) \/ TallyReplies(p) \/ LoopTermination(p)
    \/ \E p \in SlushLoopProcess, Q \in SUBSET SlushQueryProcess : QuerySampleSet(p, Q)
    \/ \E q \in SlushQueryProcess : RespondToQuery(q)
    \/ QueryLoopExit

Spec ==
    /\ Init /\ [][Next]_Vars
    /\ \A n \in Node, col \in {Node \cup {NoColor}} : WF_Vars(ClientAssignColor(n, col))
    /\ \A p \in SlushLoopProcess : WF_Vars(RequireColor(p))
    /\ \A q \in SlushQueryProcess : WF_Vars(RespondToQuery(q))

TypeInvariant == TypeOK

Termination == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess : pc[p] \in {"done", "replyDone"})

====