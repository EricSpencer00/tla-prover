---- MODULE Slush ----
EXTENDS Naturals, FiniteSets
CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

VARIABLES color, pending, pc, sample, loops
vars == <<color, pending, pc, sample, loops>>

LoopHost(n) == CHOOSE p \in SlushLoopProcess : <<p, n>> \in HostMapping
QueryHost(n) == CHOOSE q \in SlushQueryProcess : <<q, n>> \in HostMapping

TypeOK ==
  /\ color \in [Node -> {NoColor} \cup {0, 1}]
  /\ pending \subseteq ({NoMessage} \cup [from : SlushLoopProcess \cup SlushQueryProcess, to : SlushLoopProcess \cup SlushQueryProcess, kind : {"query", "reply", "term"}, payload : {NoColor} \cup {0, 1}])
  /\ pc \in [SlushLoopProcess -> {"waitingColor", "collecting", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ loops \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ pending = {}
  /\ pc = [p \in SlushLoopProcess |-> "waitingColor"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ loops = [p \in SlushLoopProcess |-> 0]

AssignColor ==
  /\ \E n \in Node, c \in {0, 1} :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<pending, pc, sample, loops>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "waitingColor"
       /\ color[LoopHost(p)] # NoColor
       /\ pc' = [pc EXCEPT ![p] = "collecting"]
  /\ UNCHANGED <<color, pending, sample, loops>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "collecting"
       /\ loops[p] < SlushIterationCount
       /\ sample' = [sample EXCEPT ![p] = {n \in Node : n # LoopHost(p)}]
       /\ pending' = pending \cup { [from |-> p, to |-> QueryHost(n), kind |-> "query", payload |-> color[LoopHost(p)]] : n \in {n \in Node : n # LoopHost(p)} }
  /\ UNCHANGED <<color, pc, loops>>

RespondToQuery ==
  /\ \E m \in pending :
       /\ m.kind = "query"
       /\ LET q == m.to IN
            /\ color' = IF color[QueryHost(q)] = NoColor THEN [color EXCEPT ![QueryHost(q)] = m.payload] ELSE color
            /\ pending' = (pending \ {m}) \cup {[from |-> q, to |-> m.from, kind |-> "reply", payload |-> IF color[QueryHost(q)] = NoColor THEN m.payload ELSE color[QueryHost(q)]]}
  /\ UNCHANGED <<pc, sample, loops>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "collecting"
       /\ \A n \in sample[p] : [from |-> QueryHost(n), to |-> p, kind |-> "reply"] \in pending
       /\ LET ca == Cardinality({n \in sample[p] : [from |-> QueryHost(n), to |-> p, kind |-> "reply", payload |-> 0] \in pending})
            cb == Cardinality({n \in sample[p] : [from |-> QueryHost(n), to |-> p, kind |-> "reply", payload |-> 1] \in pending})
       /\ color' = IF ca >= PickFlipThreshold THEN [color EXCEPT ![LoopHost(p)] = 0]
                   ELSE IF cb >= PickFlipThreshold THEN [color EXCEPT ![LoopHost(p)] = 1]
                   ELSE color
       /\ pending' = {m \in pending : ~ (m.kind = "reply" /\ m.to = p)}
       /\ sample' = [sample EXCEPT ![p] = {}]
       /\ loops' = [loops EXCEPT ![p] = @ + 1]
  /\ UNCHANGED pc

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "collecting"
       /\ loops[p] = SlushIterationCount
       /\ pc' = [pc EXCEPT ![p] = "done"]
       /\ pending' = pending \cup {[from |-> p, to |-> NoMessage, kind |-> "term", payload |-> NoColor]}
  /\ UNCHANGED <<color, sample, loops>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ [from |-> q, to |-> NoMessage, kind |-> "term", payload |-> NoColor] \in pending
       /\ pending' = pending \ {[from |-> q, to |-> NoMessage, kind |-> "term", payload |-> NoColor]}
  /\ UNCHANGED <<color, pc, sample, loops>>

Next ==
  \/ AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
  \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
Termination == <>(\A p \in SlushLoopProcess : pc[p] = "done")
====