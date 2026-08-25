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

(* --------------------------------------------------------------------- *)
(*  Derived sets and helper functions                                    *)
(* --------------------------------------------------------------------- *)

Colors == {"Red", "Blue"}

Message == [type  : {"query", "reply", "term"},
            src   : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
            dst   : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
            color : (Colors \cup {NoColor})]

(* Mapping from processes to the node they host *)
LoopNode == [l \in SlushLoopProcess |-> 
               CHOOSE n \in Node : 
                 \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping]

QueryNode == [q \in SlushQueryProcess |-> 
                CHOOSE n \in Node : 
                  \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping]

(* --------------------------------------------------------------------- *)
(*  VARIABLES                                                            *)
(* --------------------------------------------------------------------- *)

VARIABLES
    color,      \* [Node -> (Colors \cup {NoColor})]
    msgs,       \* SUBSET Message
    sample,     \* [SlushLoopProcess -> SUBSET Node]  (current sample set)
    iter        \* [SlushLoopProcess -> Nat]          (iterations done)

vars == <<color, msgs, sample, iter>>

(* --------------------------------------------------------------------- *)
(*  INITIAL STATE                                                       *)
(* --------------------------------------------------------------------- *)

Init ==
    /\ color  = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [l \in SlushLoopProcess |-> {}]
    /\ iter   = [l \in SlushLoopProcess |-> 0]

(* --------------------------------------------------------------------- *)
(*  ACTIONS                                                             *)
(* --------------------------------------------------------------------- *)

(* 1. Client assigns a colour to an uncoloured node *)
ClientAssign ==
    \E n \in Node :
        /\ color[n] = NoColor
        /\ \E c \in Colors :
              /\ color' = [color EXCEPT ![n] = c]
              /\ UNCHANGED <<msgs, sample, iter>>

(* 2. Loop process samples a set of peers and sends queries *)
LoopQuery ==
    \E l \in SlushLoopProcess :
        LET n == LoopNode[l] IN
        /\ color[n] # NoColor
        /\ iter[l] < SlushIterationCount
        /\ sample[l] = {}
        /\ LET peers == Node \ {n} IN
           \E s \subseteq peers :
               /\ Cardinality(s) = SampleSetSize
               /\ LET qs == { q \in SlushQueryProcess : QueryNode[q] \in s } IN
                  /\ msgs'   = msgs \cup {
                                 [type  |-> "query",
                                  src   |-> l,
                                  dst   |-> q,
                                  color |-> color[n]] : q \in qs }
                  /\ sample' = [sample EXCEPT ![l] = s]
                  /\ UNCHANGED <<color, iter>>

(* 3. Query process replies to a query (adopting colour if uncoloured) *)
QueryReply ==
    \E q \in SlushQueryProcess :
        \E m \in msgs :
            /\ m.type = "query"
            /\ m.dst  = q
            LET n == QueryNode[q] IN
            LET incColor == m.color IN
            LET newColor == IF color[n] = NoColor THEN incColor ELSE color[n] IN
            LET reply == [type  |-> "reply",
                          src   |-> q,
                          dst   |-> m.src,
                          color |-> newColor] IN
            /\ color' = [color EXCEPT ![n] = newColor]
            /\ msgs'   = (msgs \ {m}) \cup {reply}
            /\ UNCHANGED <<sample, iter>>

(* 4. Loop process tallies replies and possibly flips its colour *)
LoopTally ==
    \E l \in SlushLoopProcess :
        LET n == LoopNode[l] IN
        LET s == sample[l] IN
        /\ s # {}
        /\ \A q \in SlushQueryProcess :
               (QueryNode[q] \in s) => 
                 \E m \in msgs :
                     /\ m.type = "reply"
                     /\ m.dst  = l
                     /\ m.src  = q
        /\ LET replies == { m \in msgs : m.type = "reply" /\ m.dst = l } IN
           LET redCnt  == Cardinality({ m \in replies : m.color = "Red" }) IN
           LET blueCnt == Cardinality({ m \in replies : m.color = "Blue" }) IN
           LET newCol ==
                IF redCnt >= PickFlipThreshold THEN "Red"
                ELSE IF blueCnt >= PickFlipThreshold THEN "Blue"
                ELSE color[n]
           IN
           /\ color' = [color EXCEPT ![n] = newCol]
           /\ iter'   = [iter EXCEPT ![l] = @ + 1]
           /\ sample' = [sample EXCEPT ![l] = {}]
           /\ msgs'   = msgs \ replies
           /\ UNCHANGED <<>>

(* 5. Loop process terminates after all iterations *)
LoopTerminate ==
    \E l \in SlushLoopProcess :
        /\ iter[l] = SlushIterationCount
        /\ msgs' = msgs \cup {
                     [type  |-> "term",
                      src   |-> l,
                      dst   |-> "client",
                      color |-> NoColor] }
        /\ UNCHANGED <<color, sample, iter>>

Next ==
    \/ ClientAssign
    \/ LoopQuery
    \/ QueryReply
    \/ LoopTally
    \/ LoopTerminate

(* --------------------------------------------------------------------- *)
(*  SPECIFICATION                                                       *)
(* --------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(*  TYPE INVARIANT                                                       *)
(* --------------------------------------------------------------------- *)

TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq Message

=============================================================================