---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush: the simplest member of the Snow family of probabilistic consensus
\* protocols (Avalanche, 2018).  This spec is written as PlusCal that has been
\* hand-translated to TLA+.  TLA+ has no notion of probability, so convergence
\* cannot be expressed here; what we model is the message passing and the
\* fact that every process eventually reaches a done state.

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

None == "none"
Colors == {"c1", "c2"}

ASSUME /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
       /\ Cardinality(Node) = Cardinality(SlushQueryProcess)

Msgs == [kind: {"query", "reply", "term"}, from: Node, to: Node, col: Colors \union {NoColor}]

VARIABLES nodeColor, msgs, pc, sample, loopsDone

vars == <<nodeColor, msgs, pc, sample, loopsDone>>

TypeOK ==
  /\ nodeColor \in [Node -> Colors \union {NoColor}]
  /\ msgs \subseteq Msgs
  /\ pc \in [SlushLoopProcess \union SlushQueryProcess \union {"client"} -> {"idle", "busy", "done"}]
  /\ sample \in [SlushLoopProcess -> SUBSET Node]
  /\ loopsDone \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ nodeColor = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [p \in (SlushLoopProcess \union SlushQueryProcess \union {"client"}) |-> "idle"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ loopsDone = [p \in SlushLoopProcess |-> 0]

AssignColor ==
  /\ pc["client"] = "idle"
  /\ \E n \in Node, c \in Colors :
       /\ nodeColor[n] = NoColor
       /\ nodeColor' = [nodeColor EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = "busy"]
  /\ UNCHANGED <<msgs, sample, loopsDone>>

ClientBackToIdle ==
  /\ pc["client"] = "busy"
  /\ pc' = [pc EXCEPT !["client"] = "idle"]
  /\ UNCHANGED <<nodeColor, msgs, sample, loopsDone>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "idle"
       /\ \E n \in Node :
            /\ <<n, p>> \in HostMapping
            /\ nodeColor[n] # NoColor
            /\ pc' = [pc EXCEPT ![p] = "busy"]
       /\ UNCHANGED <<nodeColor, msgs, sample, loopsDone>>

SendQuery ==
  /\ \E p \in SlushLoopProcess :
       /\ pc[p] = "busy"
       /\ loopsDone[p] < SlushIterationCount
       /\ sample[p] = {}
       /\ \E peers \in SUBSET (Node \ {CHOOSE n \in Node : <<n, p>> \in HostMapping}) :
            /\ Cardinality(peers) = SampleSetSize
            /\ sample' = [sample EXCEPT ![p] = peers]
            /\ msgs' = msgs \union {
                 [kind |-> "query", from |-> CHOOSE n \in Node : <<n, p>> \in HostMapping,
                  to |-> q, col |-> nodeColor[CHOOSE n \in Node : <<n, p>> \in HostMapping]]
                 : q \in peers}
       /\ UNCHANGED <<nodeColor, pc, loopsDone>>

Reply ==
  /\ \E q \in SlushQueryProcess :
       /\ \E m \in msgs :
            /\ m.kind = "query"
            /\ <<m.to, q>> \in HostMapping
            /\ nodeColor' = IF nodeColor[m.to] = NoColor THEN [nodeColor EXCEPT ![m.to] = m.col] ELSE nodeColor
            /\ msgs' = (msgs \ {m}) \union {
                 [kind |-> "reply", from |-> m.to, to |-> m.from, col |-> nodeColor[m.to]]
               }
       /\ UNCHANGED <<pc, sample, loopsDone>>

Tally ==
  /\ \E p \in SlushLoopProcess :
       /\ sample[p] # {}
       /\ \E replies \in SUBSET Msgs :
            /\ replies \subseteq {m \in msgs : m.kind = "reply" /\ m.to = CHOOSE n \in Node : <<n, p>> \in HostMapping}
            /\ \A q \in sample[p] : \E m \in replies : m.from = q
            /\ LET count(c) == Cardinality({m \in replies : m.col = c}) IN
                 IF \E c \in Colors : count(c) >= PickFlipThreshold
                 THEN nodeColor' = [nodeColor EXCEPT ![CHOOSE n \in Node : <<n, p>> \in HostMapping] =
                          CHOOSE c \in Colors : count(c) >= PickFlipThreshold]
                 ELSE nodeColor' = nodeColor
            /\ msgs' = msgs \ replies
       /\ sample' = [sample EXCEPT ![p] = {}]
       /\ loopsDone' = [loopsDone EXCEPT ![p] = @ + 1]
       /\ UNCHANGED pc

LoopTerminate ==
  /\ \E p \in SlushLoopProcess :
       /\ loopsDone[p] = SlushIterationCount
       /\ pc[p] # "done"
       /\ pc' = [pc EXCEPT ![p] = "done"]
       /\ msgs' = msgs \union {[kind |-> "term", from |-> CHOOSE n \in Node : <<n, p>> \in HostMapping,
                                to |-> NoMessage, col |-> NoColor]}
       /\ UNCHANGED <<nodeColor, sample, loopsDone>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess :
       /\ pc[q] = "busy"
       /\ \A p \in SlushLoopProcess : pc[p] = "done"
       /\ pc' = [pc EXCEPT ![q] = "done"]
       /\ UNCHANGED <<nodeColor, msgs, sample, loopsDone>>

Next == AssignColor \/ ClientBackToIdle \/ RequireColor \/ SendQuery \/ Reply \/ Tally \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(AssignColor \/ ClientBackToIdle \/ RequireColor \/ SendQuery \/ Reply \/ Tally \/ LoopTerminate \/ QueryLoopExit)

TypeInvariant == TypeOK

Terminate == <>(\A p \in (SlushLoopProcess \union SlushQueryProcess \union {"client"}) : pc[p] = "done")

====