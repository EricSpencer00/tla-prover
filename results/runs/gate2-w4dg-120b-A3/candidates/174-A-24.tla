---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold, NoColor, NoMessage

VARIABLES
  color, msgs, pc, sample, loops

MsgTypes == {"query", "reply", "done"}
LoopSteps == {"awaiting", "sampling", "tallying", "done"}
QuerySteps == {"replying", "done"}
RequestSteps == {"ready", "done"}

TypeInvariant ==
  /\ color \in [Node -> {NoColor} \union {0, 1}]
  /\ msgs \subseteq [type: MsgTypes, src: SlushLoopProcess \union SlushQueryProcess,
                     dst: SlushLoopProcess \union SlushQueryProcess, payload: {NoMessage} \union {0, 1}]
  /\ pc \in [SlushLoopProcess -> LoopSteps]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loops \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ pc = [lp \in SlushLoopProcess |-> "awaiting"]
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ loops = [lp \in SlushLoopProcess |-> 0]

\* The client hands an uncolored node its first color.
AssignColor ==
  /\ \E n \in Node, c \in {0, 1}:
       /\ color[n] = NoColor
       /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, pc, sample, loops>>

RequireColor ==
  /\ \E lp \in SlushLoopProcess:
       /\ pc[lp] = "awaiting"
       /\ /\ color[HostMapping[lp].node] # NoColor
          /\ pc' = [pc EXCEPT ![lp] = "sampling"]
  /\ UNCHANGED <<color, msgs, sample, loops>>

\* Sample a random peer set and issue a query to each.
QuerySampleSet ==
  /\ \E lp \in SlushLoopProcess:
       /\ pc[lp] = "sampling"
       /\ Cardinality(sample[lp]) < SampleSetSize
       /\ \E qp \in SlushQueryProcess:
            /\ qp \notin sample[lp]
            /\ sample' = [sample EXCEPT ![lp] = sample[lp] \union {qp}]
            /\ msgs' = msgs \union {[type |-> "query", src |-> lp, dst |-> qp,
                                     payload |-> color[HostMapping[lp].node]]}
  /\ UNCHANGED <<color, pc, loops>>

\* A query process adopts the sender's color if still uncolored, then replies.
RespondToQuery ==
  /\ \E qp \in SlushQueryProcess:
       /\ \E m \in msgs:
            /\ m.type = "query"
            /\ m.dst = qp
            /\ msgs' = (msgs \ {m}) \union {[type |-> "reply", src |-> qp, dst |-> m.src,
                                            payload |-> IF color[HostMapping[qp].node] = NoColor
                                                          THEN (color' = [color EXCEPT ![HostMapping[qp].node] = m.payload])
                                                          ELSE color]}
  /\ UNCHANGED <<pc, sample, loops>>

\* The loop process waits for its entire sample's replies, then flips if a
\* color has reached the pick flip threshold.
TallyReplies ==
  /\ \E lp \in SlushLoopProcess:
       /\ pc[lp] = "sampling"
       /\ \A qp \in sample[lp]: \E m \in msgs: m.type = "reply" /\ m.dst = lp /\ m.src = qp
       /\ LET tally(c) == Cardinality({qp \in sample[lp] : \E m \in msgs: m.type = "reply" /\ m.dst = lp /\ m.src = qp /\ m.payload = c})
          IN
            /\ IF loops[lp] < SlushIterationCount
               THEN /\ IF tally(0) >= PickFlipThreshold
                       THEN color' = [color EXCEPT ![HostMapping[lp].node] = 0]
                       ELSE IF tally(1) >= PickFlipThreshold
                            THEN color' = [color EXCEPT ![HostMapping[lp].node] = 1]
                            ELSE color' = color
                    /\ pc' = [pc EXCEPT ![lp] = "tallying"]
                    /\ loops' = [loops EXCEPT ![lp] = loops[lp] + 1]
               ELSE pc' = [pc EXCEPT ![lp] = "done"]
            /\ sample' = [sample EXCEPT ![lp] = {}]
            /\ msgs' = {m \in msgs : m.dst # lp}
  /\ UNCHANGED <<loops>>

\* Once a loop process has finished all iterations it sends a termination
\* message to the query processes.
LoopTerminate ==
  /\ \E lp \in SlushLoopProcess:
       /\ pc[lp] = "done"
       /\ \A qp \in SlushQueryProcess: \E m \in msgs: m.type = "done" /\ m.dst = qp
       /\ UNCHANGED <<color, msgs, pc, sample, loops>>

QueryLoopExit ==
  /\ \E qp \in SlushQueryProcess:
       /\ \A m \in msgs: m.dst = qp => m.type = "done"
       /\ UNCHANGED <<color, msgs, pc, sample, loops>>

Next == AssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery \/ TallyReplies \/ LoopTerminate \/ QueryLoopExit

Spec == Init /\ [][Next]_<<color, msgs, pc, sample, loops>>

AllProcessesDone == \A lp \in SlushLoopProcess: pc[lp] = "done"

Termination == AllProcessesDone

====