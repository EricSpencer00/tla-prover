---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

\* Slush: a metastable consensus protocol from the Avalanche whitepaper.
\* Each node has a loop process that samples peers and adopts a majority-flipping
\* opinion, plus a query process that answers color queries. NoColor marks an
\* uncolored node; NoMessage is a placeholder message. The model is fully
\* deterministic (no probabilities) -- convergence is a liveness property
\* outside TLA+'s expressive power, so only a type-correctness check is given.
CONSTANTS Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
          SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

Message == [to : SlushQueryProcess, from : SlushLoopProcess, color : 0..2]
Reply == [to : SlushLoopProcess, from : SlushQueryProcess, color : 0..2]
TermMsg == [to : SlushLoopProcess, from : SlushLoopProcess]

Vars == <<colorOf, messages, step, sample, iter>>

TypeInvariant ==
  /\ colorOf \in [Node -> 0..2]
  /\ messages \subseteq (Message \cup Reply \cup TermMsg)
  /\ step \in [SlushLoopProcess \cup SlushQueryProcess \cup {"client"} -> 0..2]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ iter \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ colorOf = [n \in Node |-> NoColor]
  /\ messages = {}
  /\ step = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> 0]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iter = [p \in SlushLoopProcess |-> 0]

AssignColor(n, c) ==
  /\ step["client"] = 0
  /\ colorOf[n] = NoColor
  /\ colorOf' = [colorOf EXCEPT ![n] = c]
  /\ step' = [step EXCEPT !["client"] = 0]
  /\ UNCHANGED <<messages, sample, iter>>

StartIteration(p) ==
  /\ step[p] = 0
  /\ (\E n \in Node : [lp |-> p, qp |-> n] \in HostMapping /\ colorOf[n] # NoColor)
  /\ step' = [step EXCEPT ![p] = 1]
  /\ UNCHANGED <<colorOf, messages, sample, iter>>

SelectSample(p) ==
  /\ step[p] = 1
  /\ \E q \subseteq SlushQueryProcess :
       /\ Cardinality(q) = SampleSetSize
       /\ \A qp \in q : [lp |-> p, qp |-> qp] \in HostMapping
       /\ sample' = [sample EXCEPT ![p] = q]
  /\ messages' = messages \cup {[to |-> qp, from |-> p, color |-> colorOf[CHOOSE n \in Node :
                                                                      [lp |-> p, qp |-> qp] \in HostMapping]} : qp \in q]
  /\ step' = [step EXCEPT ![p] = 2]
  /\ UNCHANGED <<colorOf, iter>>

\* A query process adopts the query's color if it is uncolored, then replies.
AnswerQuery(m) ==
  /\ m \in messages
  /\ step[m.to] = 0
  /\ LET n == CHOOSE n \in Node : [lp |-> m.from, qp |-> n] \in HostMapping
     nc == IF colorOf[n] = NoColor THEN m.color ELSE colorOf[n]
     m2 == [to |-> m.from, from |-> m.to, color |-> nc]
  IN /\ colorOf' = [colorOf EXCEPT ![n] = nc]
     /\ messages' = (messages \ {m}) \cup {m2}
  /\ step' = [step EXCEPT ![m.to] = 1]
  /\ UNCHANGED <<sample, iter>>

TallyReplies(p) ==
  /\ step[p] = 2
  /\ \A qp \in sample[p] : \E m \in messages : m.to = p /\ m.from = qp
  /\ LET votes == [c \in 0..2 |-> Cardinality({m \in messages : m \in Reply /\ m.to = p /\ m.color = c})]
         newc == CHOOSE c \in 0..2 : votes[c] >= PickFlipThreshold
     IN colorOf' = [colorOf EXCEPT ![CHOOSE n \in Node : [lp |-> p, qp |-> n] \in HostMapping] = newc]
  /\ messages' = {m \in messages : ~(m \in Reply /\ m.to = p)}
  /\ sample' = [sample EXCEPT ![p] = {}]
  /\ iter' = [iter EXCEPT ![p] = (IF iter[p] = SlushIterationCount THEN 0 ELSE iter[p] + 1)]
  /\ step' = [step EXCEPT ![p] = 0]

Terminate(p) ==
  /\ step[p] = 0
  /\ iter[p] = SlushIterationCount
  /\ step' = [step EXCEPT ![p] = 2]
  /\ UNCHANGED <<colorOf, messages, sample, iter>>

ExitQueryLoop ==
  /\ \A qp \in SlushQueryProcess : step[qp] = 1
  /\ \A p \in SlushLoopProcess : step[p] = 2
  /\ step' = [step EXCEPT ![qp] = 2 : qp \in SlushQueryProcess]
  /\ UNCHANGED <<colorOf, messages, sample, iter>>

Next ==
  \/ \E n \in Node, c \in 0..2 : AssignColor(n, c)
  \/ \E p \in SlushLoopProcess : StartIteration(p) \/ TallyReplies(p) \/ Terminate(p)
  \/ \E p \in SlushLoopProcess : SelectSample(p)
  \/ \E m \in messages : AnswerQuery(m)
  \/ ExitQueryLoop

Spec == Init /\ [][Next]_Vars /\ WF_Vars(ExitQueryLoop)

AllProcessesDone == \A p \in (SlushLoopProcess \cup SlushQueryProcess) : step[p] = 2

SpecTermination == <>AllProcessesDone

====