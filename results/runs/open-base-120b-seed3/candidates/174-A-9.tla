---- MODULE Slush ----
EXTENDS Integers, FiniteSets, Sequences, TLC

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

(* ------------------------------------------------------------------------ *)
(* Basic domains *)

Colors        == {"Red", "Blue"}
ColorOrNone   == Colors \cup {NoColor}

Message ==
  [type  : {"query", "reply", "term"},
   src   : (SlushLoopProcess \cup SlushQueryProcess),
   dst   : (SlushLoopProcess \cup SlushQueryProcess),
   color : ColorOrNone \cup {NoMessage}]

MessageSet ==
  { m \in Message :
        (m.type = "query" => m.color \in ColorOrNone) /\
        (m.type = "reply" => m.color \in ColorOrNone) /\
        (m.type = "term"  => m.color = NoMessage) }

(* ------------------------------------------------------------------------ *)
(* Helper functions to navigate HostMapping (set of <<node, loop, query>> triples) *)

HostNode(p) ==
  CHOOSE n \in Node : \E q \in SlushQueryProcess : <<n, p, q>> \in HostMapping

QueryProc(n) ==
  CHOOSE q \in SlushQueryProcess : <<n, _, q>> \in HostMapping

LoopProc(n) ==
  CHOOSE lp \in SlushLoopProcess : <<n, lp, _>> \in HostMapping

(* ------------------------------------------------------------------------ *)
(* Variables *)

VARIABLES 
    color,   \* [Node -> ColorOrNone]
    msgs,    \* set of Message
    sample,  \* [SlushLoopProcess -> SUBSET Node]
    iter,    \* [SlushLoopProcess -> Nat]
    pc       \* [ (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) -> Nat ]

vars == <<color, msgs, sample, iter, pc>>

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs  = {}
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ iter   = [p \in SlushLoopProcess |-> 0]
  /\ pc     = [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> 0]

(* ------------------------------------------------------------------------ *)
(* Actions *)

ClientAssign ==
  /\ pc["Client"] = 0
  /\ \E n \in Node :
        /\ color[n] = NoColor
        /\ c \in Colors
        /\ color' = [color EXCEPT ![n] = c]
  /\ UNCHANGED <<msgs, sample, iter, pc>>

LoopStart ==
  /\ \E p \in SlushLoopProcess :
        /\ pc[p] = 0
        /\ LET n == HostNode(p) IN color[n] # NoColor
        /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED <<color, msgs, sample, iter>>

LoopQuery ==
  /\ \E p \in SlushLoopProcess :
        /\ pc[p] = 1
        /\ LET n == HostNode(p) IN
           curColor == color[n]
        /\ S \in SUBSET (Node \ {n})
        /\ Cardinality(S) = SampleSetSize
        /\ newMsgs == { [type  |-> "query",
                         src   |-> p,
                         dst   |-> QueryProc(n2),
                         color |-> curColor] :
                         n2 \in S }
        /\ sample' = [sample EXCEPT ![p] = S]
        /\ msgs'   = msgs \cup newMsgs
        /\ pc'     = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<color, iter>>

QueryRespond ==
  /\ \E m \in msgs :
        /\ m.type = "query"
        /\ LET q == m.dst IN
           n  == CHOOSE node \in Node : QueryProc(node) = q
        /\ curColor == color[n]
        /\ newColor == IF curColor = NoColor THEN m.color ELSE curColor
        /\ color' = [color EXCEPT ![n] = newColor]
        /\ reply  == [type  |-> "reply",
                      src   |-> q,
                      dst   |-> m.src,
                      color |-> newColor]
        /\ msgs' = (msgs \ {m}) \cup {reply}
  /\ UNCHANGED <<sample, iter, pc>>

LoopTally ==
  /\ \E p \in SlushLoopProcess :
        /\ pc[p] = 2
        /\ LET S == sample[p] IN
           /\ S # {}
        /\ replies ==
            { m \in msgs :
                /\ m.type = "reply"
                /\ m.dst = p
                /\ CHOOSE node \in Node :
                       QueryProc(node) = m.src \in S }
        /\ Cardinality(replies) = SampleSetSize
        /\ redCnt  == Cardinality({ r \in replies : r.color = "Red" })
        /\ blueCnt == Cardinality({ r \in replies : r.color = "Blue" })
        /\ curNode == HostNode(p)
        /\ curCol  == color[curNode]
        /\ newCol ==
            IF redCnt >= PickFlipThreshold THEN "Red"
            ELSE IF blueCnt >= PickFlipThreshold THEN "Blue"
            ELSE curCol
        /\ color'  = [color EXCEPT ![curNode] = newCol]
        /\ iter'   = [iter EXCEPT ![p] = @ + 1]
        /\ sample' = [sample EXCEPT ![p] = {}]
        /\ msgs'   = msgs \ replies
        /\ pc'     = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED <<>>

LoopTerminate ==
  /\ \E p \in SlushLoopProcess :
        /\ pc[p] = 2
        /\ LET S == sample[p] IN
           /\ Cardinality(S) = SampleSetSize
        /\ replies ==
            { m \in msgs :
                /\ m.type = "reply"
                /\ m.dst = p
                /\ CHOOSE node \in Node :
                       QueryProc(node) = m.src \in S }
        /\ Cardinality(replies) = SampleSetSize
        /\ iter[p] + 1 = SlushIterationCount
        /\ color'  = color
        /\ iter'   = [iter EXCEPT ![p] = @ + 1]
        /\ sample' = [sample EXCEPT ![p] = {}]
        /\ termMsgs == { [type  |-> "term",
                          src   |-> p,
                          dst   |-> q,
                          color |-> NoMessage] :
                          q \in SlushQueryProcess }
        /\ msgs'   = (msgs \ replies) \cup termMsgs
        /\ pc'     = [pc EXCEPT ![p] = 3]
  /\ UNCHANGED <<>>

QueryExit ==
  /\ \E q \in SlushQueryProcess :
        /\ pc[q] = 0
        /\ \A p \in SlushLoopProcess :
              \E m \in msgs :
                 m.type = "term" /\ m.dst = q /\ m.src = p
        /\ pc' = [pc EXCEPT ![q] = 1]
  /\ UNCHANGED <<color, msgs, sample, iter>>

Next ==
  \/ ClientAssign
  \/ LoopStart
  \/ LoopQuery
  \/ QueryRespond
  \/ LoopTally
  \/ LoopTerminate
  \/ QueryExit

(* ------------------------------------------------------------------------ *)

Spec == Init /\ [](Next)

TypeInvariant ==
  /\ color \in [Node -> ColorOrNone]
  /\ msgs  \subseteq MessageSet

=============================================================================