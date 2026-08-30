---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

(* The Slush protocol is a metastable consensus mechanism in which     *)
(* loop processes sample peers and adopt a popular color, driving      *)
(* the network toward a single converged opinion.  This is a PlusCal  *)
(* specification (translated to TLA+ below) modeling that process;     *)
(* because TLA+ has no probabilistic semantics, convergence itself     *)
(* cannot be verified -- only structural safety and termination are.   *)

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold,
          NoColor, NoMessage

(* Two possible colors (plus a distinguished uncolored value); each   *)
(* node has exactly one host loop process and one host query process.  *)
Colors == {1, 2} \cup {NoColor}

VARIABLES color, messages, pc, sampleSet, loopIteration

vars == <<color, messages, pc, sampleSet, loopIteration>>

Typ == [kind: {"query", "reply", "term"}, src: SlushLoopProcess,
        dst: SlushQueryProcess, body: Colors]

TypeOK ==
    /\ color \in [Node -> Colors]
    /\ messages \subseteq Typ
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> Nat]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ loopIteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ messages = {}
    /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> 0]
    /\ sampleSet = [p \in SlushLoopProcess |-> {}]
    /\ loopIteration = [p \in SlushLoopProcess |-> 0]

HostOfLoop(p) == CHOOSE h \in HostMapping : h[1] = p
HostOfQuery(q) == CHOOSE h \in HostMapping : h[2] = q

\* Client assigns an initial color to an uncolored node (a transaction).
ClientAssignColor(n) ==
    /\ pc["client"] = 0
    /\ color[n] = NoColor
    /\ \E c \in {1, 2} : color' = [color EXCEPT ![n] = c]
    /\ pc' = [pc EXCEPT !["client"] = 1]
    /\ UNCHANGED <<messages, sampleSet, loopIteration>>

RequireColor(p) ==
    /\ pc[p] = 0
    /\ color[HostOfLoop(p)[1]] # NoColor
    /\ pc' = [pc EXCEPT ![p] = 1]
    /\ UNCHANGED <<color, messages, sampleSet, loopIteration>>

\* Loop process samples a fixed-size set of distinct peers to poll.
QuerySampleSet(p) ==
    /\ pc[p] = 1
    /\ sampleSet' = [sampleSet EXCEPT ![p] =
                        CHOOSE s \in (SUBSET SlushQueryProcess) :
                            Cardinality(s) = SampleSetSize]
    /\ messages' = messages \cup
        { [kind |-> "query", src |-> p, dst |-> q,
           body |-> color[HostOfLoop(p)[1]]] : q \in sampleSet[p] }
    /\ pc' = [pc EXCEPT ![p] = 2]
    /\ UNCHANGED <<color, loopIteration>>

\* Query process adopts the query's color if it is uncolored, then replies.
RespondToQuery(q) ==
    /\ pc[q] = 0
    /\ \E m \in messages :
         /\ m.dst = q
         /\ m.kind = "query"
         /\ LET n == HostOfQuery(q)[1] IN
              color' = [color EXCEPT ![n] = IF color[n] = NoColor
                                                  THEN m.body ELSE color[n]]
         /\ messages' = (messages \ {m}) \cup
              { [kind |-> "reply", src |-> m.src, dst |-> q, body |-> color[n]] }
    /\ UNCHANGED <<pc, sampleSet, loopIteration>>

\* Loop process waits for a full set of replies, then adopts a supermajority.
TallyReplies(p) ==
    /\ pc[p] = 2
    /\ \A q \in sampleSet[p] : \E m \in messages : m.dst = q /\ m.kind = "reply"
    /\ LET tallies == [c \in {1, 2} |-> Cardinality({q \in sampleSet[p] :
                    \E m \in messages : m.dst = q /\ m.kind = "reply" /\ m.body = c})]
       IN color' = [color EXCEPT ![HostOfLoop(p)[1]] =
                        IF tallies[1] >= PickFlipThreshold THEN 1
                        ELSE IF tallies[2] >= PickFlipThreshold THEN 2
                        ELSE color[HostOfLoop(p)[1]]]
    /\ messages' = { m \in messages :
                        ~(m.dst \in sampleSet[p] /\ m.kind = "reply") }
    /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
    /\ loopIteration' = [loopIteration EXCEPT ![p] =
                             IF loopIteration[p] < SlushIterationCount
                             THEN loopIteration[p] + 1 ELSE loopIteration[p]]
    /\ pc' = [pc EXCEPT ![p] = IF loopIteration[p] = SlushIterationCount
                                  THEN 4 ELSE 1]

\* Once a loop process has exhausted its iterations it broadcasts termination.
LoopTermination(p) ==
    /\ pc[p] = 4
    /\ pc' = [pc EXCEPT ![p] = 5]
    /\ messages' = messages \cup
        { [kind |-> "term", src |-> p, dst |-> q, body |-> NoColor]
            : q \in SlushQueryProcess }
    /\ UNCHANGED <<color, sampleSet, loopIteration>>

\* Query processes exit once every loop process has terminated.
QueryLoopExit(q) ==
    /\ pc[q] = 0
    /\ \A p \in SlushLoopProcess : \E m \in messages : m.dst = q /\ m.kind = "term"
    /\ pc' = [pc EXCEPT ![q] = 1]
    /\ UNCHANGED <<color, messages, sampleSet, loopIteration>>

Next ==
    \/ \E n \in Node : ClientAssignColor(n)
    \/ \E p \in SlushLoopProcess : RequireColor(p) \/ QuerySampleSet(p)
                                  \/ TallyReplies(p) \/ LoopTermination(p)
    \/ \E q \in SlushQueryProcess : RespondToQuery(q) \/ QueryLoopExit(q)

Spec == Init /\ [][Next]_vars /\ WF_vars(TallyReplies("lp1")) /\ WF_vars(TallyReplies("lp2"))

(* Every color is a valid color or uncolored; every in-flight message   *)
(* conforms to one of the three message shapes this protocol uses.      *)
TypeInvariant ==
    /\ \A n \in Node : color[n] \in Colors
    /\ \A m \in messages : \E c \in Colors :
           /\ m.kind \in {"query", "reply", "term"}
           /\ m.body \in (IF m.kind = "query" THEN {1, 2} ELSE {NoColor})

(* Every process (loops, queries, and the client) eventually reaches its *)
(* terminal state; this does not imply convergence to a single color.   *)
Termination ==
    \A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) :
        <>(pc[p] = (IF p \in SlushLoopProcess THEN 5
                    ELSE IF p \in SlushQueryProcess THEN 1 ELSE 2))

====