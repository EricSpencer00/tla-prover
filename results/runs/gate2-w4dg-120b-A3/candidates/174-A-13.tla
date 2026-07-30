---- MODULE Slush ----
EXTENDS Integers, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess,
  HostMapping, SlushIterationCount, SampleSetSize,
  PickFlipThreshold, NoColor, NoMessage

\* Loop-process host, query-process host, and the full set of active nodes
\* must agree in size -- this is what keeps the network connected for the
\* sample set.
Nodes == { p[1] : p \in HostMapping }

MessageDomain == [from : SlushLoopProcess, to : SlushQueryProcess, kind : {"query", "reply", "term"}, ref : NoMessage \cup Node]

VARIABLES
  color, msg, pc, samples, loops

vars == << color, msg, pc, samples, loops >>

TypeOK ==
  /\ color \in [Node -> {NoColor} \union {"colorA", "colorB"}]
  /\ msg \subseteq MessageDomain
  /\ pc \in [SlushLoopProcess \union SlushQueryProcess \union {"client"} -> {"idle", "done"}]
  /\ samples \in [SlushLoopProcess -> SUBSET Node]
  /\ loops \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msg = {}
  /\ pc = [p \in SlushLoopProcess \union SlushQueryProcess \union {"client"} |-> "idle"]
  /\ samples = [p \in SlushLoopProcess |-> {}]
  /\ loops = [p \in SlushLoopProcess |-> 0]

\* The client process does not wait for anything; it just keeps seeding
\* uncolored nodes until the network has a full assignment.
AssignColor ==
  /\ pc["client"] = "idle"
  /\ \E n \in Node, c \in {"colorA", "colorB"} :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ pc' = [pc EXCEPT !["client"] = "done"]
  /\ UNCHANGED << msg, samples, loops >>

RequireColor ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "idle"
       /\ color[lp[1]] # NoColor
       /\ pc' = [pc EXCEPT ![lp] = "done"]
  /\ UNCHANGED << color, msg, samples, loops >>

\* The loop process builds a fixed-size peer sample and dispatches one query
\* per sampled peer. Each query records the loop process' current color as a
\* reference, which is what will be tallied back to it.
QuerySampleSet ==
  /\ \E lp \in SlushLoopProcess :
       /\ pc[lp] = "done"
       /\ loops[lp] < SlushIterationCount
       /\ \E Q \in SUBSET (Nodes \ {lp[1]}):
            /\ Cardinality(Q) = SampleSetSize
            /\ samples' = [samples EXCEPT ![lp] = Q]
            /\ msg' = msg \union { [from |-> lp, to |-> [lp[1], n], kind |-> "query", ref |-> color[lp[1]]] : n \in Q }
  /\ UNCHANGED << color, pc, loops >>

RespondToQuery ==
  /\ \E qp \in SlushQueryProcess :
       /\ \E m \in msg :
            /\ m.kind = "query"
            /\ m.to = qp
            /\ color' = IF color[qp[2]] = NoColor THEN [color EXCEPT ![qp[2]] = m.ref] ELSE color
            /\ msg' = (msg \ {m}) \union {[from |-> m.from, to |-> m.from, kind |-> "reply", ref |-> color[qp[2]]]}
  /\ UNCHANGED << pc, samples, loops >>

TallyReplies ==
  /\ \E lp \in SlushLoopProcess :
       /\ \E m \in msg :
            /\ m.kind = "reply"
            /\ m.from = lp
            /\ m.ref \in {"colorA", "colorB"}
            /\ \A n \in samples[lp] : \E mm \in msg : mm.kind = "reply" /\ mm.from = [lp[1], n] /\ mm.ref # NoColor
            /\ LET counts == [c \in {"colorA", "colorB"} |-> Cardinality({n \in samples[lp] : [lp[1], n] \in {mm.from : mm \in msg /\ mm.kind = "reply" /\ mm.ref = c}}) ] IN
                 color' = IF counts["colorA"] >= PickFlipThreshold THEN [color EXCEPT ![lp[1]] = "colorA"]
                          ELSE IF counts["colorB"] >= PickFlipThreshold THEN [color EXCEPT ![lp[1]] = "colorB"]
                          ELSE color
            /\ msg' = {mm \in msg : mm.kind # "reply" \/ mm.from # lp}
            /\ samples' = [samples EXCEPT ![lp] = {}]
            /\ loops' = [loops EXCEPT ![lp] = loops[lp] + 1]
  /\ UNCHANGED pc

LoopTerminate ==
  /\ \E lp \in SlushLoopProcess :
       /\ loops[lp] = SlushIterationCount
       /\ pc[lp] = "done"
       /\ msg' = msg \union {[from |-> lp, to |-> lp, kind |-> "term", ref |-> NoMessage]}
       /\ UNCHANGED << color, pc, samples, loops >>

QueryLoopExit ==
  /\ \A qp \in SlushQueryProcess : pc[qp] = "idle"
  /\ \E qp \in SlushQueryProcess :
       /\ \E m \in msg : m.kind = "term" /\ m.from = qp
       /\ pc' = [pc EXCEPT ![qp] = "done"]
  /\ UNCHANGED << color, msg, samples, loops >>

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars

TypeInvariant == TypeOK

\* Termination is defined just as every process reaching its done state --
\* the probabilistic convergence claim cannot be expressed in plain TLA+.
AllProcessesTerminate ==
  \A lp \in SlushLoopProcess, qp \in SlushQueryProcess : pc[lp] = "done" /\ pc[qp] = "done"

====