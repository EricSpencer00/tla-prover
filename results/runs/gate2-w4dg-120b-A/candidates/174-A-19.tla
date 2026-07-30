---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
    SlushIterationCount, SampleSetSize, PickFlipThreshold,
    NoColor, NoMessage

\* Each loop and query process is hosted by exactly one node, and the three sets
\* of actors all have the same size.
\* NoMessage is the value of MessageType for termination messages that carry no color.

MessageType == [src : SlushLoopProcess, dst : SlushQueryProcess,
                kind : {"query", "reply", "final"}, col : {NoColor, "c1", "c2"}]

VARIABLES assign, msgs, pc, sample, rounds

vars == <<assign, msgs, pc, sample, rounds>>

TypeInvariant ==
    /\ assign \in [Node -> {"c1", "c2", NoColor}]
    /\ msgs \subseteq MessageType
    /\ pc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> {"idle", "querying", "tallying", "done"}]
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ rounds \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
    /\ assign = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} |-> "idle"]
    /\ sample = [l \in SlushLoopProcess |-> {}]
    /\ rounds = [l \in SlushLoopProcess |-> 0]

AssignColor(n) ==
    /\ assign[n] = NoColor
    /\ \E c \in {"c1", "c2"} : assign' = [assign EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, pc, sample, rounds>>

RequireColor(l) ==
    /\ pc[l] = "idle"
    /\ \E n \in Node : <<n, l, "loop">> \in HostMapping /\ assign[n] # NoColor
    /\ pc' = [pc EXCEPT ![l] = "querying"]
    /\ UNCHANGED <<assign, msgs, sample, rounds>>

QuerySample(l) ==
    /\ pc[l] = "querying"
    /\ rounds[l] < SlushIterationCount
    /\ \E Q \in SUBSET SlushQueryProcess : Cardinality(Q) = SampleSetSize
        /\ \A q \in Q : ~\E m \in msgs : m.src = l /\ m.dst = q
        /\ msgs' = msgs \cup {[src |-> l, dst |-> q, kind |-> "query", col |-> assign[CHOOSE n \in Node : <<n, l, "loop">> \in HostMapping]] : q \in Q}
        /\ sample' = [sample EXCEPT ![l] = Q]
    /\ pc' = [pc EXCEPT ![l] = "tallying"]
    /\ UNCHANGED <<assign, rounds>>

RespondQuery(q) ==
    /\ pc[q] # "done"
    /\ \E m \in msgs : m.dst = q /\ m.kind = "query"
        /\ LET sender == m.src
               col == m.col
           IN /\ \E n \in Node : <<n, q, "query">> \in HostMapping /\ assign' = [assign EXCEPT ![n] = IF assign[n] = NoColor THEN col ELSE assign[n]]
              /\ msgs' = (msgs \ {m}) \cup {[src |-> q, dst |-> sender, kind |-> "reply", col |-> assign[CHOOSE n \in Node : <<n, q, "query">> \in HostMapping]]}
    /\ UNCHANGED <<pc, sample, rounds>>

TallyReplies(l) ==
    /\ pc[l] = "tallying"
    /\ \A q \in sample[l] : \E m \in msgs : m.kind = "reply" /\ m.src = q /\ m.dst = l
    /\ LET tally(c) == Cardinality({q \in sample[l] : (\E m \in msgs : m.kind = "reply" /\ m.src = q /\ m.dst = l /\ m.col = c)}) IN
        /\ assign' = [n \in Node |-> IF \E c \in {"c1", "c2"} : tally(c) >= PickFlipThreshold THEN CHOOSE c \in {"c1", "c2"} : tally(c) >= PickFlipThreshold
                      ELSE assign[CHOOSE m \in msgs : m.kind = "reply" /\ m.dst = l /\ m.src = CHOOSE q \in sample[l] : TRUE]]
    /\ msgs' = {m \in msgs : ~(m.kind = "reply" /\ m.dst = l)}
    /\ rounds' = [rounds EXCEPT ![l] = rounds[l] + 1]
    /\ pc' = [pc EXCEPT ![l] = "idle"]
    /\ UNCHANGED sample

TerminateLoop(l) ==
    /\ pc[l] = "idle"
    /\ rounds[l] = SlushIterationCount
    /\ \A q \in SlushQueryProcess : ~\E m \in msgs : m.kind = "final" /\ m.src = l /\ m.dst = q
    /\ \E q \in SlushQueryProcess : msgs' = msgs \cup {[src |-> l, dst |-> q, kind |-> "final", col |-> NoColor]}
    /\ pc' = [pc EXCEPT ![l] = "done"]
    /\ UNCHANGED <<assign, sample, rounds>>

QueryLoopExit ==
    /\ \A q \in SlushQueryProcess : pc[q] = "idle"
    /\ \A m \in msgs : m.kind # "final"
    /\ pc' = [pc EXCEPT ![q] = "done" : q \in SlushQueryProcess]
    /\ UNCHANGED <<assign, msgs, sample, rounds>>

Next ==
    \/ \E n \in Node : AssignColor(n)
    \/ \E l \in SlushLoopProcess : RequireColor(l)
    \/ \E l \in SlushLoopProcess : QuerySample(l)
    \/ \E q \in SlushQueryProcess : RespondQuery(q)
    \/ \E l \in SlushLoopProcess : TallyReplies(l)
    \/ \E l \in SlushLoopProcess : TerminateLoop(l)
    \/ QueryLoopExit

\* Every actor eventually idles, which together with the bounded iteration count
\* means the whole system eventually idles.
Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E n \in Node : AssignColor(n))
        /\ WF_vars(\E l \in SlushLoopProcess : RequireColor(l))
        /\ WF_vars(\E l \in SlushLoopProcess : QuerySample(l))
        /\ WF_vars(\E q \in SlushQueryProcess : RespondQuery(q))
        /\ WF_vars(\E l \in SlushLoopProcess : TallyReplies(l))
        /\ WF_vars(\E l \in SlushLoopProcess : TerminateLoop(l))
        /\ WF_vars(QueryLoopExit)

Termination == <>(\A p \in SlushLoopProcess \cup SlushQueryProcess \cup {"client"} : pc[p] = "done")

====