---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

\* Each node has a loop process (which queries peers and decides) and a query
\* process (which answers queries). HostMapping links process ids to the node
\* they belong to: <<proc, node>> pairs for loop and query processes.

Hosts == Node
LoopProcs == { p \in SlushLoopProcess : \E n \in Hosts : <<p, n>> \in HostMapping }
QueryProcs == { q \in SlushQueryProcess : \E n \in Hosts : <<q, n>> \in HostMapping }
LoopHost(p) == CHOOSE n \in Hosts : <<p, n>> \in HostMapping
QueryHost(q) == CHOOSE n \in Hosts : <<q, n>> \in HostMapping

Message == [kind: {"query", "reply", "term"}, src: Hosts, dst: Hosts, col: {"a", "b"}]

VARIABLES color, inbox, pc, sample, iterCount

vars == <<color, inbox, pc, sample, iterCount>>

TypeOK ==
    /\ color \in [Node -> {"a", "b", NoColor}]
    /\ inbox \subseteq Message
    /\ pc \in [LoopProcs \cup QueryProcs -> {"idle", "looping", "done"}]
    /\ sample \in [LoopProcs -> SUBSET Node]
    /\ iterCount \in [LoopProcs -> 0..SlushIterationCount]

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ inbox = {}
    /\ pc = [p \in LoopProcs \cup QueryProcs |-> "idle"]
    /\ sample = [p \in LoopProcs |-> {}]
    /\ iterCount = [p \in LoopProcs |-> 0]

ClientAssignColor ==
    /\ \E n \in Node, k \in {"a", "b"} : (color[n] = NoColor /\ color' = [color EXCEPT ![n] = k])
    /\ UNCHANGED <<inbox, pc, sample, iterCount>>

RequireColor ==
    /\ \E p \in LoopProcs :
         /\ pc[p] = "idle"
         /\ color[LoopHost(p)] # NoColor
         /\ pc' = [pc EXCEPT ![p] = "looping"]
    /\ UNCHANGED <<color, inbox, sample, iterCount>>

QuerySampleSet ==
    /\ \E p \in LoopProcs :
         /\ pc[p] = "looping"
         /\ iterCount[p] < SlushIterationCount
         /\ sample[p] = {}
         /\ \E S \in SUBSET (Hosts \ {LoopHost(p)}) :
              /\ Cardinality(S) = SampleSetSize
              /\ sample' = [sample EXCEPT ![p] = S]
              /\ inbox' = inbox \cup { [kind |-> "query", src |-> LoopHost(p), dst |-> n, col |-> color[LoopHost(p)]] : n \in S }
    /\ UNCHANGED <<color, pc, iterCount>>

RespondToQuery ==
    /\ \E m \in inbox :
         /\ m.kind = "query"
         /\ color' = [color EXCEPT ![m.dst] = IF color[m.dst] = NoColor THEN m.col ELSE color[m.dst]]
         /\ inbox' = (inbox \ {m}) \cup {[kind |-> "reply", src |-> m.dst, dst |-> m.src, col |-> IF color[m.dst] = NoColor THEN m.col ELSE color[m.dst]]}
    /\ UNCHANGED <<pc, sample, iterCount>>

TallyReplies ==
    /\ \E p \in LoopProcs :
         /\ sample[p] # {}
         /\ \A n \in sample[p] : [kind |-> "reply", src |-> n, dst |-> LoopHost(p), col |-> color[n]] \in inbox
         /\ LET count(k) == Cardinality({ n \in sample[p] : color[n] = k })
                majority == CHOOSE k \in {"a", "b"} : count(k) >= PickFlipThreshold
                inbox' == inbox \ {[kind |-> "reply", src |-> n, dst |-> LoopHost(p), col |-> color[n]] : n \in sample[p]}
            IN /\ color' = [color EXCEPT ![LoopHost(p)] = majority]
               /\ sample' = [sample EXCEPT ![p] = {}]
               /\ iterCount' = [iterCount EXCEPT ![p] = iterCount[p] + 1]
               /\ pc' = IF iterCount[p] + 1 = SlushIterationCount THEN [pc EXCEPT ![p] = "done"] ELSE pc
    /\ UNCHANGED <<inbox>>

LoopTerminate ==
    /\ \E p \in LoopProcs :
         /\ pc[p] = "done"
         /\ inbox' = inbox \cup { [kind |-> "term", src |-> LoopHost(p), dst |-> LoopHost(p), col |-> NoColor] }
    /\ UNCHANGED <<color, pc, sample, iterCount>>

QueryLoopExit ==
    /\ \E q \in QueryProcs :
         /\ pc[q] = "idle"
         /\ \A p \in LoopProcs : <<p, LoopHost(p)>> \in inbox
         /\ pc' = [pc EXCEPT ![q] = "done"]
    /\ UNCHANGED <<color, inbox, sample, iterCount>>

Next ==
    \/ ClientAssignColor \/ RequireColor \/ QuerySampleSet
    \/ RespondToQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ClientAssignColor) /\ WF_vars(RequireColor)
    /\ WF_vars(QuerySampleSet) /\ WF_vars(RespondToQuery)
    /\ WF_vars(TallyReplies) /\ WF_vars(LoopTerminate) /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == \A p \in LoopProcs \cup QueryProcs : <>(pc[p] = "done")

====