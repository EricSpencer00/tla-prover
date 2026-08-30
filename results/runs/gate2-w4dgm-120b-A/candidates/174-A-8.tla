---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* A message on the network; the "kind" field distinguishes queries from
\* query replies from the termination broadcast.
Message == [kind : {"query", "reply", "term"}, proc : SlushLoopProcess \cup SlushQueryProcess, body : 0..2]

VARIABLES color, messages, pc, sample, iterations

vars == <<color, messages, pc, sample, iterations>>

Hosts == {n \in Node : <<n, SlushLoopProcess, SlushQueryProcess>> \in HostMapping}
LoopProcs == {p \in SlushLoopProcess : \E n \in Node : <<n, p, SlushQueryProcess>> \in HostMapping}
QueryProcs == {q \in SlushQueryProcess : \E n \in Node : <<n, SlushLoopProcess, q>> \in HostMapping}
HostOfLoop(p) == CHOOSE n \in Node : <<n, p, SlushQueryProcess>> \in HostMapping
HostOfQuery(q) == CHOOSE n \in Node : <<n, SlushLoopProcess, q>> \in HostMapping
OtherQueryProcs(p) == QueryProcs \ { <<HostOfLoop(p), SlushQueryProcess>> }

TypeOK ==
    /\ color \in [Node -> {1, 2, NoColor}]
    /\ messages \subseteq Message
    /\ pc \in [SlushLoopProcess -> {"waiting", "sampling", "counting", "done"}]
    /\ iterations \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ messages = {}
    /\ pc = [p \in SlushLoopProcess |-> "waiting"]
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iterations = [p \in SlushLoopProcess |-> 0]

\* The client assigns an initial color to an uncolored node (a fresh txn).
AssignColor(n) ==
    /\ color[n] = NoColor
    /\ \E c \in {1, 2} : color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<messages, pc, sample, iterations>>

RequireColor(p) ==
    /\ pc[p] = "waiting"
    /\ color[HostOfLoop(p)] # NoColor
    /\ pc' = [pc EXCEPT ![p] = "sampling"]
    /\ UNCHANGED <<color, messages, sample, iterations>>

\* Loop process: sample a peer set and emit a query message to each member.
QuerySampleSet(p) ==
    /\ pc[p] = "sampling"
    /\ iterations[p] < SlushIterationCount
    /\ Cardinality(sample[p]) < SampleSetSize
    /\ iterations[p] = 0 \/ \A q \in sample[p] : <<HostOfQuery(q), SlushQueryProcess>> \in HostMapping
    /\ \E q \in OtherQueryProcs(p) \ sample[p] :
        /\ sample' = [sample EXCEPT ![p] = @ \cup {q}]
        /\ messages' = messages \cup {[kind |-> "query", proc |-> q, body |-> color[HostOfLoop(p)]]}
    /\ UNCHANGED <<color, pc, iterations>>

\* Query process: adopt the query's color if uncolored, then reply.
RespondToQuery(q) ==
    /\ [kind |-> "query", proc |-> q, body |-> NoMessage] \in messages
    /\ color' = [color EXCEPT ![HostOfQuery(q)] =
                    IF color[HostOfQuery(q)] = NoColor THEN @ ELSE @]
    /\ messages' = (messages \ {[kind |-> "query", proc |-> q, body |-> NoMessage]})
                    \cup {[kind |-> "reply", proc |-> q, body |-> color[HostOfQuery(q)]]}
    /\ UNCHANGED <<pc, sample, iterations>>

\* Loop process: tally replies and flip to the dominant opinion if it clears
\* the threshold.
TallyReplies(p) ==
    /\ pc[p] = "sampling"
    /\ \A q \in sample[p] : [kind |-> "reply", proc |-> q, body |-> NoMessage] \in messages
    /\ \E c \in {1, 2} :
        /\ Cardinality({q \in sample[p] : [kind |-> "reply", proc |-> q, body |-> c] \in messages}) >= PickFlipThreshold
        /\ color' = [color EXCEPT ![HostOfLoop(p)] = c]
    /\ messages' = messages \cup {[kind |-> "term", proc |-> p, body |-> NoMessage]}
    /\ sample' = [sample EXCEPT ![p] = {}]
    /\ iterations' = [iterations EXCEPT ![p] = @ + 1]
    /\ pc' = IF iterations[p] + 1 < SlushIterationCount THEN "sampling" ELSE "done"

LoopTerminate(p) ==
    /\ pc[p] = "sampling"
    /\ iterations[p] = SlushIterationCount
    /\ messages' = messages \cup {[kind |-> "term", proc |-> p, body |-> NoMessage]}
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<color, sample, iterations>>

\* Query processes wait for every loop process to be done.
QueryLoopExit ==
    /\ \A q \in QueryProcs : [kind |-> "reply", proc |-> q, body |-> NoMessage] \notin messages
    /\ \A p \in LoopProcs : [kind |-> "term", proc |-> p, body |-> NoMessage] \in messages
    /\ \A q \in QueryProcs : [kind |-> "term", proc |-> q, body |-> NoMessage] \notin messages
    /\ \A q \in QueryProcs : [kind |-> "term", proc |-> q, body |-> NoMessage] \in messages
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Node : AssignColor(n)
    \/ \E p \in LoopProcs : RequireColor(p)
    \/ \E p \in LoopProcs : QuerySampleSet(p)
    \/ \E q \in QueryProcs : RespondToQuery(q)
    \/ \E p \in LoopProcs : TallyReplies(p)
    \/ \E p \in LoopProcs : LoopTerminate(p)
    \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == \A p \in LoopProcs \cup QueryProcs : <>(pc[p] = "done")

====