---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node,
  SlushLoopProcess,
  SlushQueryProcess,
  HostMapping,
  SlushIterationCount,
  SampleSetSize,
  PickFlipThreshold,
  NoColor,
  NoMessage

Process == SlushLoopProcess \cup SlushQueryProcess

Message == [kind : {"query", "reply", "term"}, tgt : Process, src : SlushLoopProcess \cup {NoMessage}, pl : Node \cup {NoMessage}]

Colour == {NoColor, "A", "B"}
Step == {"loopInit", "loopSample", "loopReply", "loopDone", "queryReply", "queryExit"}

VARIABLES nodeColour, msgs, pc, sample, iterations

vars == << nodeColour, msgs, pc, sample, iterations >>

Init == /\ nodeColour = [n \in Node |-> NoColor]
        /\ msgs = {}
        /\ pc = [p \in Process |-> IF p \in SlushLoopProcess THEN "loopInit" ELSE "queryReply"]
        /\ sample = [l \in SlushLoopProcess |-> {}]
        /\ iterations = [l \in SlushLoopProcess |-> 0]

\* Client process: assign a random colour to an uncoloured node.
ClientAssignColour == \E n \in Node, c \in {"A", "B"} :
                        /\ nodeColour[n] = NoColor
                        /\ nodeColour' = [nodeColour EXCEPT ![n] = c]
                        /\ UNCHANGED << msgs, pc, sample, iterations >>

RequireColour == \E l \in SlushLoopProcess :
                    /\ pc[l] = "loopInit"
                    /\ \E n \in Node :
                        /\ n = CHOOSE m \in Node : \A k \in HostMapping : k[1] = m => k[2] = l
                        /\ nodeColour[n] # NoColor
                    /\ pc' = [pc EXCEPT ![l] = "loopSample"]
                    /\ UNCHANGED << nodeColour, msgs, sample, iterations >>

\* Loop process: pick a random sample set of peers to query.
QuerySampleSet == \E l \in SlushLoopProcess :
                    /\ pc[l] = "loopSample"
                    /\ \E subset \in SUBSET SlushQueryProcess :
                        /\ Cardinality(subset) = SampleSetSize
                        /\ msgs' = msgs \cup { [kind |-> "query", tgt |-> q, src |-> l, pl |-> CHOOSE n \in Node : \A k \in HostMapping : k[2] = l => k[1] = n] : q \in subset }
                        /\ sample' = [sample EXCEPT ![l] = subset]
                    /\ pc' = [pc EXCEPT ![l] = "loopReply"]
                    /\ UNCHANGED << nodeColour, iterations >>

\* Query process: reply to a query, adopting the query colour if uncoloured.
RespondToQuery == \E m \in msgs :
                    /\ m.kind = "query"
                    /\ pc[m.tgt] = "queryReply"
                    /\ LET n == CHOOSE k \in HostMapping : k[2] = m.tgt => k[1] IN
                        /\ nodeColour' = [nodeColour EXCEPT ![n] = IF nodeColour[n] = NoColor THEN m.pl ELSE nodeColour[n]]
                        /\ msgs' = (msgs \ {m}) \cup {[kind |-> "reply", tgt |-> m.src, src |-> NoMessage, pl |-> nodeColour[n]]}
                    /\ UNCHANGED << pc, sample, iterations >>

\* Loop process: once all sampled replies are in, tally and possibly flip colour.
TallyReplies == \E l \in SlushLoopProcess :
                  /\ pc[l] = "loopReply"
                  /\ \A q \in sample[l] : \E m \in msgs : m.kind = "reply" /\ m.tgt = l /\ m.src = q
                  /\ LET replies == [m \in msgs : m.kind = "reply" /\ m.tgt = l] IN
                        /\ nodeColour' = [n \in Node |->
                                            IF Cardinality({m \in replies : m.pl = "A"}) >= PickFlipThreshold THEN "A"
                                            ELSE IF Cardinality({m \in replies : m.pl = "B"}) >= PickFlipThreshold THEN "B"
                                            ELSE nodeColour[n]]
                        /\ msgs' = msgs \ {m \in msgs : m.kind = "reply" /\ m.tgt = l}
                  /\ sample' = [sample EXCEPT ![l] = {}]
                  /\ iterations' = [iterations EXCEPT ![l] = iterations[l] + 1]
                  /\ pc' = IF iterations[l] + 1 >= SlushIterationCount THEN "loopDone" ELSE "loopSample"

LoopTermination == \E l \in SlushLoopProcess :
                     /\ pc[l] = "loopDone"
                     /\ pc' = [pc EXCEPT ![l] = "loopExit"]
                     /\ UNCHANGED << nodeColour, msgs, sample, iterations >>

QueryLoopExit == /\ \A p \in SlushQueryProcess : pc[p] = "queryReply"
                 /\ \A l \in SlushLoopProcess : pc[l] \in {"loopDone", "loopExit"}
                 /\ \E p \in SlushQueryProcess : pc' = [pc EXCEPT ![p] = "queryExit"]
                 /\ UNCHANGED << nodeColour, msgs, sample, iterations >>

Next == \/ ClientAssignColour
        \/ RequireColour
        \/ QuerySampleSet
        \/ RespondToQuery
        \/ TallyReplies
        \/ LoopTermination
        \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ SF_vars(RespondToQuery)
        /\ SF_vars(TallyReplies)
        /\ WF_vars(QueryLoopExit)

TypeInvariant == /\ nodeColour \in [Node -> Colour]
                 /\ msgs \subseteq Message
                 /\ pc \in [Process -> Step]
                 /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
                 /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

\* Completion: every loop and query process has exited its active phase.
AllExited == <>(\A p \in Process : pc[p] \in {"loopExit", "queryExit"})

====