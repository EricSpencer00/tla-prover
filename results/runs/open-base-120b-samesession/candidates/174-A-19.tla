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

(* --------------------------------------------------------------------- *)
(*   Basic sets                                                          *)
(* --------------------------------------------------------------------- *)

ColorSet == {"Red", "Blue"}

(* --------------------------------------------------------------------- *)
(*   Host mapping helpers                                                *)
(* --------------------------------------------------------------------- *)

LoopNode(l) ==
    CHOOSE n \in Node : <<n, l, q>> \in HostMapping

QueryNode(q) ==
    CHOOSE n \in Node : <<n, l, q>> \in HostMapping

(* --------------------------------------------------------------------- *)
(*   Message definition                                                  *)
(* --------------------------------------------------------------------- *)

Message ==
    [type : {"Query", "Reply", "Term"},
     src  : (SlushLoopProcess \cup SlushQueryProcess),
     dst  : (SlushLoopProcess \cup SlushQueryProcess),
     col  : ColorSet \cup {NoColor}]

(* --------------------------------------------------------------------- *)
(*   Variables                                                          *)
(* --------------------------------------------------------------------- *)

VARIABLES
    color,   \* [node \in Node |-> color or NoColor]
    msgs,    \* Set of Message
    pc,      \* [proc \in ProcSet |-> label]
    sample,  \* [loop \in SlushLoopProcess |-> SUBSET Node]  (current sample)
    iter     \* [loop \in SlushLoopProcess |-> Nat]        (iterations done)

ProcSet == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

(* --------------------------------------------------------------------- *)
(*   Initial state                                                      *)
(* --------------------------------------------------------------------- *)

Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ pc     = [p \in ProcSet |-> "Init"]
    /\ sample = [l \in SlushLoopProcess |-> {}]
    /\ iter   = [l \in SlushLoopProcess |-> 0]

(* --------------------------------------------------------------------- *)
(*   Actions                                                            *)
(* --------------------------------------------------------------------- *)

(* --- Client actions --------------------------------------------------- *)

ClientAssign ==
    /\ pc["Client"] = "Init"
    /\ \E n \in Node : color[n] = NoColor
    /\ LET n == CHOOSE n \in Node : color[n] = NoColor
           c == CHOOSE c \in ColorSet
       IN
          /\ color' = [color EXCEPT ![n] = c]
          /\ pc'    = [pc EXCEPT !["Client"] = "Init"]
          /\ UNCHANGED <<msgs, sample, iter>>

ClientDone ==
    /\ pc["Client"] = "Init"
    /\ \A n \in Node : color[n] # NoColor
    /\ pc' = [pc EXCEPT !["Client"] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

(* --- Loop process actions --------------------------------------------- *)

LoopRequireColor(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = "Init"
    /\ color[LoopNode(l)] # NoColor
    /\ pc' = [pc EXCEPT ![l] = "Sample"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

LoopSample(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = "Sample"
    /\ iter[l] < SlushIterationCount
    /\ LET otherNodes == Node \ {LoopNode(l)}
           sampleSet  == CHOOSE s \subseteq otherNodes :
                         Cardinality(s) = SampleSetSize
           queryMsgs  == { [type |-> "Query",
                            src  |-> l,
                            dst  |-> q,
                            col  |-> color[LoopNode(l)] ] :
                           q \in SlushQueryProcess :
                           QueryNode(q) \in sampleSet }
       IN
          /\ sample' = [sample EXCEPT ![l] = sampleSet]
          /\ msgs'   = msgs \cup queryMsgs
          /\ pc'     = [pc EXCEPT ![l] = "WaitReplies"]
          /\ UNCHANGED <<color, iter>>

LoopCollect(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = "WaitReplies"
    /\ LET s == sample[l]
           replies == { m \in msgs :
                         m.type = "Reply" /\ m.dst = l /\ QueryNode(m.src) \in s }
       IN
          /\ Cardinality(replies) = SampleSetSize
          /\ LET reds   == { m \in replies : m.col = "Red" }
                 blues  == { m \in replies : m.col = "Blue" }
                 redCnt == Cardinality(reds)
                 blueCnt== Cardinality(blues)
                 newCol == IF redCnt >= PickFlipThreshold THEN "Red"
                          ELSE IF blueCnt >= PickFlipThreshold THEN "Blue"
                          ELSE color[LoopNode(l)]
             IN
                /\ color' = [color EXCEPT ![LoopNode(l)] = newCol]
          /\ msgs'   = msgs \ replies
          /\ sample' = [sample EXCEPT ![l] = {}]
          /\ iter'   = [iter EXCEPT ![l] = @ + 1]
          /\ pc' = IF iter'[l] = SlushIterationCount
                   THEN [pc EXCEPT ![l] = "Terminate"]
                   ELSE [pc EXCEPT ![l] = "Sample"]
          /\ UNCHANGED <<>>

LoopTerminate(l) ==
    /\ l \in SlushLoopProcess
    /\ pc[l] = "Terminate"
    /\ LET termMsgs == { [type |-> "Term",
                          src  |-> l,
                          dst  |-> q,
                          col  |-> NoColor] :
                         q \in SlushQueryProcess }
       IN
          /\ msgs' = msgs \cup termMsgs
          /\ pc'   = [pc EXCEPT ![l] = "Done"]
          /\ UNCHANGED <<color, sample, iter>>

(* --- Query process actions -------------------------------------------- *)

QueryHandle(q) ==
    /\ q \in SlushQueryProcess
    /\ pc[q] = "Init"
    /\ \E m \in msgs :
         /\ m.type = "Query"
         /\ m.dst = q
    /\ LET m == CHOOSE m \in msgs :
                 m.type = "Query" /\ m.dst = q
           n  == QueryNode(q)
           curColor == color[n]
           newColor == IF curColor = NoColor THEN m.col ELSE curColor
           reply   == [type |-> "Reply",
                       src  |-> q,
                       dst  |-> m.src,
                       col  |-> newColor]
       IN
          /\ color' = [color EXCEPT ![n] = newColor]
          /\ msgs'   = (msgs \ {m}) \cup {reply}
          /\ pc'     = [pc EXCEPT ![q] = "Init"]
          /\ UNCHANGED <<sample, iter>>

QueryExit(q) ==
    /\ q \in SlushQueryProcess
    /\ pc[q] # "Done"
    /\ \A l \in SlushLoopProcess : pc[l] = "Done"
    /\ pc' = [pc EXCEPT ![q] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

(* --------------------------------------------------------------------- *)
(*   Next relation                                                     *)
(* --------------------------------------------------------------------- *)

Next ==
    \/ \E l \in SlushLoopProcess : LoopRequireColor(l)
    \/ \E l \in SlushLoopProcess : LoopSample(l)
    \/ \E q \in SlushQueryProcess : QueryHandle(q)
    \/ \E l \in SlushLoopProcess : LoopCollect(l)
    \/ \E l \in SlushLoopProcess : LoopTerminate(l)
    \/ \E q \in SlushQueryProcess : QueryExit(q)
    \/ ClientAssign
    \/ ClientDone

(* --------------------------------------------------------------------- *)
(*   Specification                                                     *)
(* --------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iter>>

(* --------------------------------------------------------------------- *)
(*   Invariant                                                         *)
(* --------------------------------------------------------------------- *)

TypeInvariant ==
    /\ \A n \in Node : color[n] \in ColorSet \cup {NoColor}
    /\ \A m \in msgs :
          /\ m.type \in {"Query", "Reply", "Term"}
          /\ m.src  \in (SlushLoopProcess \cup SlushQueryProcess)
          /\ m.dst  \in (SlushLoopProcess \cup SlushQueryProcess)
          /\ m.col  \in ColorSet \cup {NoColor}

====