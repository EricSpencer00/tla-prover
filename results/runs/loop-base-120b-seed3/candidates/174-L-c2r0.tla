---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

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

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)

ProcessSet == SlushLoopProcess \cup SlushQueryProcess \cup {"client"}

Red  == "Red"
Blue == "Blue"
ColorSet == {Red, Blue, NoColor}

(* Mapping from a node to its associated processes, obtained from HostMapping *)
NodeToLoop(n) ==
    CHOOSE t \in HostMapping :
        /\ t[3] = n
        /\ t[1] \in SlushLoopProcess

NodeToQuery(n) ==
    CHOOSE t \in HostMapping :
        /\ t[3] = n
        /\ t[2] \in SlushQueryProcess

NodeOfLoop(l) ==
    CHOOSE t \in HostMapping :
        /\ t[1] = l
        /\ t[3] \in Node

NodeOfQuery(q) ==
    CHOOSE t \in HostMapping :
        /\ t[2] = q
        /\ t[3] \in Node

(* ---------------------------------------------------------------------- *)
VARIABLES
    color,   \* [Node -> ColorSet]
    msgs,    \* set of messages
    pc,      \* [ProcessSet -> {"start","waitColor","sample","waitReplies","listen","done"}]
    sample,  \* [SlushLoopProcess -> SUBSET SlushQueryProcess]
    iter     \* [SlushLoopProcess -> Nat]

(* ---------------------------------------------------------------------- *)
Message == [type : {"query","reply","term"},
            src  : ProcessSet,
            dst  : ProcessSet,
            col  : ColorSet]

(* ---------------------------------------------------------------------- *)
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in ProcessSet |
                IF p = "client" THEN "start"
                ELSE IF p \in SlushLoopProcess THEN "waitColor"
                ELSE "listen"]
    /\ sample = [l \in SlushLoopProcess |-> {}]
    /\ iter = [l \in SlushLoopProcess |-> 0]

(* ---------------------------------------------------------------------- *)
(* Client assigns a random color to an uncolored node *)
ClientAssign ==
    /\ pc["client"] = "start"
    /\ \E n \in Node : color[n] = NoColor
    /\ LET n == CHOOSE n \in Node : color[n] = NoColor
           c \in {Red, Blue} IN
       /\ color' = [color EXCEPT ![n] = c]
       /\ UNCHANGED <<msgs, pc, sample, iter>>
    \/ /\ \A n \in Node : color[n] # NoColor
       /\ pc' = [pc EXCEPT !["client"] = "done"]
       /\ UNCHANGED <<color, msgs, sample, iter>>

(* ---------------------------------------------------------------------- *)
(* Loop process waits until its host node receives a color *)
LoopRequireColor(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = "waitColor"
    /\ LET n == NodeOfLoop(l) IN color[n] # NoColor
    /\ pc' = [pc EXCEPT ![l] = "sample"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

(* ---------------------------------------------------------------------- *)
(* Loop process picks a random sample of other query processes *)
LoopPickSample(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = "sample"
    /\ LET n == NodeOfLoop(l) IN
          otherQueries == { NodeToQuery(m) : m \in Node \ {n} } IN
       /\ \E S \subseteq otherQueries :
              Cardinality(S) = SampleSetSize
    /\ SAMPLE == S
    /\ sample' = [sample EXCEPT ![l] = SAMPLE]
    /\ msgs' = msgs \cup
               { [type |-> "query",
                  src  |-> l,
                  dst  |-> q,
                  col  |-> color[n]] : q \in SAMPLE }
    /\ pc' = [pc EXCEPT ![l] = "waitReplies"]
    /\ UNCHANGED <<color, iter>>

(* ---------------------------------------------------------------------- *)
(* Query process answers a query; if uncolored it adopts the query color *)
QueryRespond(q) ==
    /\ q \in SlushQueryProcess
    /\ \E m \in msgs :
          /\ m.type = "query"
          /\ m.dst = q
    /\ LET n == NodeOfQuery(q)
           m == CHOOSE m \in msgs :
                 /\ m.type = "query"
                 /\ m.dst = q
           curColor == color[n]
           queryCol == m.col
           newCol == IF curColor = NoColor THEN queryCol ELSE curColor
           reply  == [type |-> "reply",
                     src  |-> q,
                     dst  |-> m.src,
                     col  |-> newCol] IN
       /\ color' = [color EXCEPT ![n] = newCol]
       /\ msgs' = (msgs \ {m}) \cup {reply}
       /\ UNCHANGED <<pc, sample, iter>>

(* ---------------------------------------------------------------------- *)
(* Loop process tallies replies, possibly flips its color, and advances iteration *)
LoopTally(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = "waitReplies"
    /\ sample[l] # {}
    /\ LET n == NodeOfLoop(l)
           replyColors == { 
               LET q == qv IN
               LET nodeQ == NodeOfQuery(q) IN
               color[nodeQ]
               : qv \in sample[l] }
           cntRed  == Cardinality({c \in replyColors : c = Red})
           cntBlue == Cardinality({c \in replyColors : c = Blue})
           newCol  == IF cntRed >= PickFlipThreshold THEN Red
                     ELSE IF cntBlue >= PickFlipThreshold THEN Blue
                     ELSE color[n]
           newIter == iter[l] + 1
           nextPc  == IF newIter >= SlushIterationCount THEN "done" ELSE "sample"
           termMsg == IF newIter >= SlushIterationCount
                     THEN { [type |-> "term", src |-> l, dst |-> "client", col |-> NoMessage] }
                     ELSE {} IN
       /\ color' = [color EXCEPT ![n] = newCol]
       /\ iter' = [iter EXCEPT ![l] = newIter]
       /\ sample' = [sample EXCEPT ![l] = {}]
       /\ pc' = [pc EXCEPT ![l] = nextPc]
       /\ msgs' = msgs \cup termMsg

(* ---------------------------------------------------------------------- *)
(* All query processes become done once every loop process is done *)
QueryTerminate ==
    /\ \A l \in SlushLoopProcess : pc[l] = "done"
    /\ \E q \in SlushQueryProcess : pc[q] = "listen"
    /\ pc' = [p \in ProcessSet |
                IF p \in SlushQueryProcess THEN "done"
                ELSE pc[p]]
    /\ UNCHANGED <<color, msgs, sample, iter>>

(* ---------------------------------------------------------------------- *)
Next ==
    \/ ClientAssign
    \/ \E l \in SlushLoopProcess : LoopRequireColor(l)
    \/ \E l \in SlushLoopProcess : LoopPickSample(l)
    \/ \E q \in SlushQueryProcess : QueryRespond(q)
    \/ \E l \in SlushLoopProcess : LoopTally(l)
    \/ QueryTerminate

(* ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iter>>

(* ---------------------------------------------------------------------- *)
TypeInvariant ==
    /\ color \in [Node -> ColorSet]
    /\ msgs \subseteq Message
    /\ pc \in [ProcessSet -> {"start","waitColor","sample","waitReplies","listen","done"}]
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iter \in [SlushLoopProcess -> Nat]

=============================================================================