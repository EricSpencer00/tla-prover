---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Node,
  SlushLoopProcess,
  SlushQueryProcess,
  HostMapping,
  SlushIterationCount,
  SampleSetSize,
  PickFlipThreshold,
  NoColor,
  NoMessage

\* Process steps: client assigning colors, a loop process waiting for its node
\* to be colored, sampling peers via query messages, peers responding, tallying
\* and possibly flipping the node's color, and termination.
ProcessStep == {"done", "assignColor", "waitForColor", "querySet", "replyStep", "tally"}

\* Message types: a query from a loop process to a query process, a reply
\* carrying the respondent's color, and a termination broadcast.
MessageType == {"msgQuery", "msgReply", "msgTerminate"}

VARIABLES
  slushColor,
  slushMessage,
  slushStep,
  slushSample,
  slushIterCount

vars == <<slushColor, slushMessage, slushStep, slushSample, slushIterCount>>

TypeOK ==
  /\ slushColor \in [Node -> {NoColor} \union [SlushLoopProcess -> 1..2]]
  /\ slushMessage \subseteq [type: MessageType, from: SlushLoopProcess \union SlushQueryProcess,
                            to: SlushLoopProcess \union SlushQueryProcess, payload: 1..2]
  /\ slushStep \in [SlushLoopProcess \union SlushQueryProcess -> ProcessStep]
  /\ slushSample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ slushIterCount \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ slushColor = [n \in Node |-> NoColor]
  /\ slushMessage = {}
  /\ slushStep = [p \in SlushLoopProcess \union SlushQueryProcess |-> "assignColor"]
  /\ slushSample = [l \in SlushLoopProcess |-> {}]
  /\ slushIterCount = [l \in SlushLoopProcess |-> 0]

AssignColor ==
  /\ \E n \in Node, c \in 1..2:
       /\ slushColor[n] = NoColor
       /\ slushColor' = [slushColor EXCEPT ![n] = c]
  /\ UNCHANGED <<slushMessage, slushStep, slushSample, slushIterCount>>

RequireColor ==
  /\ \E l \in SlushLoopProcess:
       /\ slushStep[l] = "assignColor"
       /\ slushColor[CHOOSE n \in Node : <<l, n>> \in HostMapping] # NoColor
       /\ slushStep' = [slushStep EXCEPT ![l] = "waitForColor"]
  /\ UNCHANGED <<slushColor, slushMessage, slushSample, slushIterCount>>

QuerySet ==
  /\ \E l \in SlushLoopProcess:
       /\ slushStep[l] = "waitForColor"
       /\ slushIterCount[l] < SlushIterationCount
       /\ \E s \in SUBSET SlushQueryProcess:
            /\ Cardinality(s) = SampleSetSize
            /\ s \subseteq SlushQueryProcess
            /\ slushSample' = [slushSample EXCEPT ![l] = s]
            /\ slushMessage' = slushMessage
                 \union {[type |-> "msgQuery", from |-> l, to |-> q,
                          payload |-> slushColor[CHOOSE n \in Node : <<l, n>> \in HostMapping]]
                          : q \in s}
  /\ UNCHANGED <<slushColor, slushStep, slushIterCount>>

RespondToQuery ==
  /\ \E q \in SlushQueryProcess:
       /\ slushStep[q] = "replyStep"
       /\ \E m \in slushMessage:
            /\ m.type = "msgQuery" /\ m.to = q
            /\ slushColor' = IF slushColor[CHOOSE n \in Node : <<q, n>> \in HostMapping] = NoColor
                             THEN [slushColor EXCEPT ![CHOOSE n \in Node : <<q, n>> \in HostMapping]
                                    = m.payload]
                             ELSE slushColor
            /\ slushMessage' = (slushMessage \ {m})
                 \union {[type |-> "msgReply", from |-> q, to |-> m.from, payload |-> slushColor'
                           [CHOOSE n \in Node : <<q, n>> \in HostMapping]]}
  /\ UNCHANGED <<slushStep, slushSample, slushIterCount>>

TallyReplies ==
  /\ \E l \in SlushLoopProcess:
       /\ slushStep[l] = "querySet"
       /\ \A q \in slushSample[l] : \E m \in slushMessage:
            /\ m.type = "msgReply" /\ m.from = q /\ m.to = l
       /\ LET cnt == [c \in 1..2 |-> Cardinality({q \in slushSample[l] : \E m \in slushMessage:
                                                    /\ m.type = "msgReply" /\ m.from = q
                                                    /\ m.payload = c})]
          IN IF \E c \in 1..2 : cnt[c] >= PickFlipThreshold
             THEN slushColor' = [slushColor EXCEPT ![CHOOSE n \in Node : <<l, n>> \in HostMapping]
                                   = CHOOSE c \in 1..2 : cnt[c] >= PickFlipThreshold]
             ELSE slushColor' = slushColor
       /\ slushIterCount' = [slushIterCount EXCEPT ![l] = slushIterCount[l] + 1]
       /\ slushSample' = [slushSample EXCEPT ![l] = {}]
       /\ slushMessage' = slushMessage
            \union {[type |-> "msgTerminate", from |-> l, to |-> l, payload |-> 1]}
  /\ UNCHANGED <<slushStep>>

LoopTermination ==
  /\ \E l \in SlushLoopProcess:
       /\ slushStep[l] = "querySet"
       /\ slushIterCount[l] = SlushIterationCount
       /\ slushStep' = [slushStep EXCEPT ![l] = "done"]
  /\ UNCHANGED <<slushColor, slushMessage, slushSample, slushIterCount>>

QueryLoopExit ==
  /\ \E q \in SlushQueryProcess:
       /\ slushStep[q] = "replyStep"
       /\ \A l \in SlushLoopProcess: [type |-> "msgTerminate", from |-> l, to |-> l, payload |-> 1]
            \in slushMessage
       /\ slushStep' = [slushStep EXCEPT ![q] = "done"]
  /\ UNCHANGED <<slushColor, slushMessage, slushSample, slushIterCount>>

Next ==
  \/ AssignColor \/ RequireColor \/ QuerySet \/ RespondToQuery
  \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
        /\ WF_vars(AssignColor)
        /\ WF_vars(RequireColor)
        /\ WF_vars(QuerySet)
        /\ WF_vars(RespondToQuery)
        /\ WF_vars(TallyReplies)
        /\ WF_vars(LoopTermination)
        /\ WF_vars(QueryLoopExit)

Termination ==
  /\ \A l \in SlushLoopProcess: slushStep[l] = "done"
  /\ \A q \in SlushQueryProcess: slushStep[q] = "done"

====