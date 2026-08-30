---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping, SlushIterationCount,
  SampleSetSize, PickFlipThreshold, NoColor, NoMessage

Colors == {"Red", "Blue"}
Processes == SlushLoopProcess \cup SlushQueryProcess \cup {"client"}
MessageType == {"query", "reply", "term"}

VARIABLES
  color, message, prog, sampleSet, loopIteration

vars == <<color, message, prog, sampleSet, loopIteration>>

Host(p) == CHOOSE n \in Node : <<n, p, "owns">> \in HostMapping

TypeOK ==
  /\ color \in [Node -> Colors \cup {NoColor}]
  /\ message \subseteq [proc: Processes, kind: MessageType, col: Colors \cup {NoColor}]
  /\ prog \in [Processes -> {"start", "working", "done"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIteration \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ message = {}
  /\ prog = [p \in Processes |-> "start"]
  /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
  /\ loopIteration = [lp \in SlushLoopProcess |-> 0]

AssignColor ==
  /\ prog["client"] = "start"
  /\ \E n \in Node, c \in Colors :
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ prog' = [prog EXCEPT !["client"] = "working"]
  /\ UNCHANGED <<message, sampleSet, loopIteration>>

RequireColor ==
  /\ \E lp \in SlushLoopProcess :
       /\ prog[lp] = "start"
       /\ color[Host(lp)] # NoColor
       /\ prog' = [prog EXCEPT ![lp] = "working"]
  /\ UNCHANGED <<color, message, sampleSet, loopIteration>>

QuerySampleSet ==
  /\ \E lp \in SlushLoopProcess :
       /\ prog[lp] = "working"
       /\ loopIteration[lp] < SlushIterationCount
       /\ sampleSet[lp] = {}
       /\ \E Q \in SUBSET SlushQueryProcess :
            /\ Cardinality(Q) = SampleSetSize
            /\ sampleSet' = [sampleSet EXCEPT ![lp] = Q]
            /\ message' = message \cup
                 {[proc |-> q, kind |-> "query", col |-> color[Host(lp)]] : q \in Q}
  /\ UNCHANGED <<color, prog, loopIteration>>

ReplyQuery ==
  /\ \E m \in message :
       /\ m.kind = "query"
       /\ prog[m.proc] = "working"
       /\ (color[Host(m.proc)] = NoColor \/ color[Host(m.proc)] # m.col)
       /\ color' = [color EXCEPT ![Host(m.proc)] =
                      IF color[Host(m.proc)] = NoColor THEN m.col ELSE color[Host(m.proc)]]
       /\ message' = (message \ {m}) \cup
            {[proc |-> Host(m), kind |-> "reply", col |-> color[Host(m.proc)]]}
  /\ UNCHANGED <<prog, sampleSet, loopIteration>>

TallyReplies ==
  /\ \E lp \in SlushLoopProcess :
       /\ prog[lp] = "working"
       /\ loopIteration[lp] < SlushIterationCount
       /\ sampleSet[lp] # {}
       /\ \A q \in sampleSet[lp] : \E m \in message :
            m.kind = "reply" /\ m.proc = q
       /\ \E c \in Colors :
            LET count == Cardinality({q \in sampleSet[lp] :
                  \E m \in message : m.kind = "reply" /\ m.proc = q /\ m.col = c})
            IN IF count >= PickFlipThreshold
               THEN color' = [color EXCEPT ![Host(lp)] = c]
               ELSE UNCHANGED color
       /\ message' = {m \in message : m.kind # "reply"}
       /\ sampleSet' = [sampleSet EXCEPT ![lp] = {}]
       /\ loopIteration' = [loopIteration EXCEPT ![lp] = @ + 1]
  /\ UNCHANGED prog

LoopTerminate ==
  /\ \E lp \in SlushLoopProcess :
       /\ prog[lp] = "working"
       /\ loopIteration[lp] = SlushIterationCount
       /\ prog' = [prog EXCEPT ![lp] = "done"]
       /\ message' = message \cup
            {[proc |-> lp, kind |-> "term", col |-> NoColor]}
  /\ UNCHANGED <<color, sampleSet, loopIteration>>

QueryLoopExit ==
  /\ \A q \in SlushQueryProcess : prog[q] = "working"
  /\ \A lp \in SlushLoopProcess : prog[lp] = "done"
  /\ prog' = [p \in Processes |-> IF prog[p] = "working" THEN "done" ELSE prog[p]]
  /\ UNCHANGED <<color, message, sampleSet, loopIteration>>

Next ==
  \/ AssignColor \/ RequireColor \/ QuerySampleSet \/ ReplyQuery
  \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopTerminate) /\ WF_vars(QueryLoopExit)

TypeInvariant == TypeOK

Termination == \A p \in Processes : prog[p] = "done"

====