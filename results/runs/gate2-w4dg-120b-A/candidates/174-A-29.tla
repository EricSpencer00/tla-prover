---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

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

\* node colors: two real colors plus an uncolored value
Colors == {"colorA", "colorB", NoColor}

MessageType == {"msgQuery", "msgQueryReply", "msgTerminate"}
Message == SlushLoopProcess \X SlushQueryProcess \X Colors \X MessageType

Bump(n) == IF n < SlushIterationCount THEN n + 1 ELSE n

VARIABLES color, msgs, procPc, sampleSet, loopsCompleted
vars == <<color, msgs, procPc, sampleSet, loopsCompleted>>

TypeInvariant ==
  /\ color \in [Node -> Colors]
  /\ msgs \subseteq Message
  /\ procPc \in [SlushLoopProcess \cup SlushQueryProcess \cup {"clientReq"} -> {"pcReady", "pcQuery", "pcTally", "pcDone"}]
  /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopsCompleted \in [SlushLoopProcess -> 0..SlushIterationCount]

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ procPc = [p \in SlushLoopProcess \cup SlushQueryProcess \cup {"clientReq"} |-> "pcReady"]
  /\ sampleSet = [p \in SlushLoopProcess |-> {}]
  /\ loopsCompleted = [p \in SlushLoopProcess |-> 0]

ClientAssignColor ==
  /\ procPc["clientReq"] = "pcReady"
  /\ \E n \in Node :
       /\ color[n] = NoColor
       /\ \E c \in {"colorA", "colorB"} : color' = [color EXCEPT ![n] = c]
  /\ procPc' = [procPc EXCEPT !["clientReq"] = "pcReady"]
  /\ UNCHANGED <<msgs, sampleSet, loopsCompleted>>

RequireColor ==
  /\ \E p \in SlushLoopProcess :
       /\ procPc[p] = "pcReady"
       /\ \E n \in Node :
            /\ <<p, n>> \in HostMapping
            /\ color[n] # NoColor
            /\ procPc' = [procPc EXCEPT ![p] = "pcQuery"]
  /\ UNCHANGED <<color, msgs, sampleSet, loopsCompleted>>

QuerySampleSet ==
  /\ \E p \in SlushLoopProcess :
       /\ procPc[p] = "pcQuery"
       /\ Cardinality(sampleSet[p]) < SampleSetSize
       /\ \E n \in Node :
            /\ \E q \in SlushQueryProcess :
                 /\ <<p, q>> \in HostMapping
                 /\ <<p, q, color[CHOOSE n2 \in Node : <<p, n2>> \in HostMapping], "msgQuery">> \notin msgs
                 /\ msgs' = msgs \cup {<<p, q, color[CHOOSE n2 \in Node : <<p, n2>> \in HostMapping], "msgQuery">>}
                 /\ sampleSet' = [sampleSet EXCEPT ![p] = @ \cup {q}]
       /\ UNCHANGED <<color, procPc, loopsCompleted>>

RespondToQuery ==
  /\ \E q \in SlushQueryProcess :
       /\ \E p \in SlushLoopProcess :
            /\ <<p, q, "msgReply", "msgQuery">> \in msgs
            /\ \E n \in Node :
                 /\ <<p, n>> \in HostMapping
                 /\ LET cur == color[CHOOSE n2 \in Node : <<q, n2>> \in HostMapping]
                        newc == IF cur = NoColor THEN color[CHOOSE n2 \in Node : <<p, n2>> \in HostMapping] ELSE cur
                    IN /\ color' = [color EXCEPT ![CHOOSE n2 \in Node : <<q, n2>> \in HostMapping] = newc]
                       /\ msgs' = (msgs \ {<<p, q, "msgReply", "msgQuery">>})
                          \cup {<<p, q, newc, "msgQueryReply">>}
            /\ UNCHANGED <<procPc, sampleSet, loopsCompleted>>

TallyReplies ==
  /\ \E p \in SlushLoopProcess :
       /\ procPc[p] = "pcQuery"
       /\ \A q \in sampleSet[p] : <<p, q, "msgReply", "msgQueryReply">> \in msgs
       /\ LET count(c) == Cardinality({q \in sampleSet[p] : <<p, q, c, "msgQueryReply">> \in msgs})
              n == CHOOSE n2 \in Node : <<p, n2>> \in HostMapping
          IN /\ IF \E c \in {"colorA", "colorB"} : count(c) >= PickFlipThreshold
                THEN color' = [color EXCEPT ![n] = CHOOSE c \in {"colorA", "colorB"} : count(c) >= PickFlipThreshold]
                ELSE color' = color
             /\ sampleSet' = [sampleSet EXCEPT ![p] = {}]
             /\ loopsCompleted' = [loopsCompleted EXCEPT ![p] = Bump(@)]
             /\ procPc' = [procPc EXCEPT ![p] = IF loopsCompleted[p] = SlushIterationCount THEN "pcDone" ELSE "pcQuery"]
  /\ UNCHANGED msgs

LoopTermination ==
  /\ \E p \in SlushLoopProcess :
       /\ procPc[p] = "pcDone"
       /\ \A q \in SlushQueryProcess : <<p, q, "msgTerminate", "msgTerminate">> \notin msgs
       /\ msgs' = msgs \cup {<<p, q, NoColor, "msgTerminate">> : q \in SlushQueryProcess}
       /\ procPc' = [procPc EXCEPT ![p] = "pcDone"]
  /\ UNCHANGED <<color, sampleSet, loopsCompleted>>

QueryLoopExit ==
  /\ \A p \in SlushLoopProcess : procPc[p] = "pcDone"
  /\ \E q \in SlushQueryProcess :
       /\ procPc[q] = "pcReady"
       /\ procPc' = [procPc EXCEPT ![q] = "pcDone"]
  /\ UNCHANGED <<color, msgs, sampleSet, loopsCompleted>>

Next ==
  \/ ClientAssignColor \/ RequireColor \/ QuerySampleSet \/ RespondToQuery
  \/ TallyReplies \/ LoopTermination \/ QueryLoopExit

Spec == Init /\ [][Next]_vars
         /\ WF_vars(ClientAssignColor) /\ WF_vars(QuerySampleSet)
         /\ WF_vars(RespondToQuery) /\ WF_vars(TallyReplies) /\ WF_vars(LoopTermination)

Termination ==
  /\ \A p \in SlushLoopProcess : procPc[p] = "pcDone"
  /\ \A q \in SlushQueryProcess : procPc[q] = "pcDone"
  /\ procPc["clientReq"] = "pcReady"

====