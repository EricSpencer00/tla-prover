---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

(* --------------------------------------------------------------------- *)
(* Helper definitions *)

ColorSet == {"Red", "Blue"}

(* Host of a loop process *)
HostLoop(lp) == (CHOOSE t \in HostMapping : t[2] = lp).1

(* Host of a query process *)
HostQuery(qp) == (CHOOSE t \in HostMapping : t[3] = qp).1

(* The query process that belongs to a node *)
QueryProc(n) == (CHOOSE t \in HostMapping : t[1] = n).3

(* --------------------------------------------------------------------- *)
(* Variables *)

VARIABLES color, msgs, pc, sample, iter

vars == <<color, msgs, pc, sample, iter>>

(* --------------------------------------------------------------------- *)
(* Initial state *)

Init ==
  /\ color = [n \in Node |-> NoColor]
  /\ msgs = {}
  /\ sample = [lp \in SlushLoopProcess |-> {}]
  /\ iter = [lp \in SlushLoopProcess |-> 0]
  /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |
            IF p \in SlushLoopProcess THEN "WaitColor"
            ELSE IF p \in SlushQueryProcess THEN "ReplyLoop"
            ELSE "Assign"]

(* --------------------------------------------------------------------- *)
(* Actions *)

ClientAssign ==
  \E n \in Node :
    /\ color[n] = NoColor
    /\ \E c \in ColorSet :
         /\ color' = [color EXCEPT ![n] = c]
         /\ UNCHANGED <<msgs, pc, sample, iter>>

RequireColor ==
  \E lp \in SlushLoopProcess :
    /\ pc[lp] = "WaitColor"
    /\ color[HostLoop(lp)] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = "Sample"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

QuerySample ==
  \E lp \in SlushLoopProcess :
    /\ pc[lp] = "Sample"
    /\ LET thisNode == HostLoop(lp) IN
       \E S \subseteq (Node \ {thisNode}) :
         /\ Cardinality(S) = SampleSetSize
         /\ LET qs == { QueryProc(n) : n \in S } IN
            /\ msgs' = msgs \cup
                 { [type |-> "query",
                    src   |-> lp,
                    dst   |-> qp,
                    color |-> color[thisNode]] : qp \in qs }
            /\ sample' = [sample EXCEPT ![lp] = S]
            /\ pc' = [pc EXCEPT ![lp] = "Collect"]
            /\ UNCHANGED <<color, iter>>

RespondQuery ==
  \E qp \in SlushQueryProcess, m \in msgs :
    /\ m.type = "query"
    /\ m.dst = qp
    /\ LET n == HostQuery(qp) IN
       /\ IF color[n] = NoColor
            THEN color' = [color EXCEPT ![n] = m.color]
            ELSE color' = color
       /\ LET reply == [type |-> "reply",
                        src   |-> qp,
                        dst   |-> m.src,
                        color |-> color[n]] IN
          msgs' = (msgs \ {m}) \cup {reply}
       /\ UNCHANGED <<pc, sample, iter>>

ProcessReplies ==
  \E lp \in SlushLoopProcess :
    /\ pc[lp] = "Collect"
    /\ LET S == sample[lp] IN
       LET replies == { r \in msgs :
                         r.type = "reply" /\ r.dst = lp /\
                         r.src \in { QueryProc(n) : n \in S } } IN
       /\ Cardinality(replies) = SampleSetSize
       /\ LET redCnt  == Cardinality({ r \in replies : r.color = "Red" })
              blueCnt == Cardinality({ r \in replies : r.color = "Blue" })
              curNode == HostLoop(lp)
              newCol  ==
                IF redCnt >= PickFlipThreshold THEN "Red"
                ELSE IF blueCnt >= PickFlipThreshold THEN "Blue"
                ELSE color[curNode] IN
          /\ color' = [color EXCEPT ![curNode] = newCol]
          /\ msgs' = msgs \ replies
          /\ sample' = [sample EXCEPT ![lp] = {}]
          /\ iter' = [iter EXCEPT ![lp] = @ + 1]
          /\ IF iter'[lp] = SlushIterationCount
                THEN pc' = [pc EXCEPT ![lp] = "Terminate"]
                ELSE pc' = [pc EXCEPT ![lp] = "Sample"]
          /\ UNCHANGED <<>>

LoopTerminate ==
  \E lp \in SlushLoopProcess :
    /\ pc[lp] = "Terminate"
    /\ LET term == [type |-> "term", src |-> lp, dst |-> "All"] IN
         msgs' = msgs \cup {term}
    /\ pc' = [pc EXCEPT ![lp] = "Done"]
    /\ UNCHANGED <<color, sample, iter>>

QueryLoopExit ==
  /\ \A lp \in SlushLoopProcess : pc[lp] = "Done"
  /\ \E qp \in SlushQueryProcess :
        /\ pc[qp] = "ReplyLoop"
        /\ pc' = [pc EXCEPT ![qp] = "Done"]
        /\ UNCHANGED <<color, msgs, sample, iter>>

NoOp ==
  UNCHANGED vars

Next ==
  \/ ClientAssign
  \/ RequireColor
  \/ QuerySample
  \/ RespondQuery
  \/ ProcessReplies
  \/ LoopTerminate
  \/ QueryLoopExit
  \/ NoOp

(* --------------------------------------------------------------------- *)
(* Specification *)

Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(* Type invariant *)

MessageSet ==
  { [type |-> "query",
     src   |-> SlushLoopProcess,
     dst   |-> SlushQueryProcess,
     color |-> (ColorSet \cup {NoColor})] } \/
  { [type |-> "reply",
     src   |-> SlushQueryProcess,
     dst   |-> SlushLoopProcess,
     color |-> (ColorSet \cup {NoColor})] } \/
  { [type |-> "term",
     src   |-> SlushLoopProcess,
     dst   |-> "All"] }

TypeInvariant ==
  /\ color \in [Node -> (ColorSet \cup {NoColor})]
  /\ msgs \subseteq MessageSet

====