---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* Slush is the simplest member of the Snow consensus family: a set of nodes *)
(* repeatedly queries random peers and adopts a sufficiently popular opinion *)
(* (color) until the network converges. TLA+ provides no probabilistic        *)
(* primitives, so this is an executable sketch of the protocol. One loop      *)
(* process per node drives query/reply iterations; a separate query process per *)
(* node responds. Convergence (eventual unanimity) is a probabilistic safety  *)
(* property of Slush that TLA+ cannot express, so the spec only checks the     *)
(* structural properties stated below.                                          *)

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping
          SlushIterationCount, SampleSetSize, PickFlipThreshold
          NoColor, NoMessage

\* SlushLoopProcess and SlushQueryProcess are two views of the same node set.
\* Each loop process queries its peer nodes' query processes and counts their
\* replies. The three message types are: a query, a query reply, and a
\* termination notice from a loop process that has finished its iterations.

Message == [dest: SlushQueryProcess, src: SlushLoopProcess, payload: 0..1]
           \/ [dest: SlushLoopProcess, src: SlushQueryProcess, payload: 0..1]
           \/ [dest: SlushLoopProcess, src: "loop", payload: NoMessage]

VARIABLES color, messages, loopPc, queryPc, sample, loopIter

TypeInvariant ==
    /\ color \in [Node -> (0..1) \cup {NoColor}]
    /\ \A m \in messages : m \in Message
    /\ loopPc \in [SlushLoopProcess -> {"waitColor", "querying", "tallying", "done"}]
    /\ queryPc \in [SlushQueryProcess -> {"replying", "done"}]
    /\ \A q \in SlushLoopProcess : sample[q] \subseteq SlushQueryProcess
    /\ \A q \in SlushLoopProcess : loopIter[q] \in 0..SlushIterationCount

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ messages = {}
    /\ loopPc = [q \in SlushLoopProcess |-> "waitColor"]
    /\ queryPc = [p \in SlushQueryProcess |-> "replying"]
    /\ sample = [q \in SlushLoopProcess |-> {}]
    /\ loopIter = [q \in SlushLoopProcess |-> 0]

\* A client request assigns an initial color to some uncolored node.
ClientAssign ==
    /\ \E n \in Node :
         /\ color[n] = NoColor
         /\ color' = [color EXCEPT ![n] = IF Cardinality({x \in Node : x = n}) = 0 THEN 0 ELSE 1]
    /\ UNCHANGED <<messages, loopPc, queryPc, sample, loopIter>>

\* Each loop process waits for its host node to have a color.
RequireColor ==
    /\ \E q \in SlushLoopProcess :
         /\ loopPc[q] = "waitColor"
         /\ (\E n \in Node : [q, n] \in HostMapping /\ color[n] # NoColor)
         /\ loopPc' = [loopPc EXCEPT ![q] = "querying"]
    /\ UNCHANGED <<color, messages, queryPc, sample, loopIter>>

\* The loop process selects a random sample of peers to query (up to SampleSetSize).
QuerySample ==
    /\ \E q \in SlushLoopProcess :
         /\ loopPc[q] = "querying"
         /\ Cardinality(sample[q]) = 0
         /\ \E s \in SUBSET SlushQueryProcess :
              /\ Cardinality(s) = SampleSetSize
              /\ sample' = [sample EXCEPT ![q] = s]
              /\ messages' = messages \cup { [dest |-> p, src |-> q,
                                             payload |-> color[CHOOSE n \in Node :
                                                                   [q, n] \in HostMapping])] : p \in s }
    /\ UNCHANGED <<color, loopPc, queryPc, loopIter>>

\* A query process adopts the query's color if uncolored, then replies.
RespondQuery ==
    /\ \E m \in messages :
         /\ m \in [dest: SlushQueryProcess, src: SlushLoopProcess, payload: 0..1]
         /\ queryPc[m.dest] = "replying"
         /\ (\E n \in Node : [m.dest, n] \in HostMapping)
         /\ color' = [color EXCEPT ![CHOOSE n \in Node : [m.dest, n] \in HostMapping] =
                       IF color[CHOOSE n \in Node : [m.dest, n] \in HostMapping] = NoColor
                       THEN m.payload ELSE color[CHOOSE n \in Node : [m.dest, n] \in HostMapping]]]
         /\ messages' = (messages \ {m}) \cup {[dest |-> m.src, src |-> m.dest, payload |-> color[CHOOSE n \in Node : [m.dest, n] \in HostMapping]]}
    /\ UNCHANGED <<loopPc, queryPc, sample, loopIter>>

\* The loop process counts replies; if one color dominates the sample, it flips.
TallyReplies ==
    /\ \E q \in SlushLoopProcess :
         /\ loopPc[q] = "querying"
         /\ \E replies \in SUBSET {m \in messages : m.dest = q /\ m.src \in sample[q]} :
              /\ Cardinality(replies) = SampleSetSize
              /\ Cardinality({m \in replies : m.payload = 0}) >= PickFlipThreshold
                    \/ Cardinality({m \in replies : m.payload = 1}) >= PickFlipThreshold
              /\ color' = [color EXCEPT ![CHOOSE n \in Node : [q, n] \in HostMapping] =
                             IF Cardinality({m \in replies : m.payload = 0}) >= PickFlipThreshold
                             THEN 0 ELSE 1]
              /\ messages' = (messages \ replies) \cup { [dest |-> q, src |-> "loop", payload |-> NoMessage] }
              /\ loopPc' = [loopPc EXCEPT ![q] = "tallying"]
              /\ sample' = [sample EXCEPT ![q] = {}]
              /\ loopIter' = [loopIter EXCEPT ![q] = IF @ < SlushIterationCount THEN @ + 1 ELSE @]
    /\ UNCHANGED queryPc

LoopTermination ==
    /\ \E q \in SlushLoopProcess :
         /\ loopPc[q] = "tallying"
         /\ loopIter[q] = SlushIterationCount
         /\ loopPc' = [loopPc EXCEPT ![q] = "done"]
         /\ messages' = messages \cup {[dest |-> q, src |-> "loop", payload |-> NoMessage]}
    /\ UNCHANGED <<color, queryPc, sample, loopIter>>

QueryLoopExit ==
    /\ \E p \in SlushQueryProcess :
         /\ queryPc[p] = "replying"
         /\ \A q \in SlushLoopProcess : [q, p] \notin HostMapping \/ [q, p] \in HostMapping
         /\ Cardinality({m \in messages : m.src = "loop"}) = Cardinality(SlushLoopProcess)
         /\ queryPc' = [queryPc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<color, messages, loopPc, sample, loopIter>>

Next == ClientAssign \/ RequireColor \/ QuerySample \/ RespondQuery
        \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_<<color, messages, loopPc, queryPc, sample, loopIter>>

AllProcessesDone == <>(\A q \in SlushLoopProcess : loopPc[q] = "done")

====