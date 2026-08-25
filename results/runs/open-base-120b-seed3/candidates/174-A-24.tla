---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

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
(* Colors (two possible opinions)                                        *)
CONSTANT Colors
ASSUME Colors = {"Red", "Blue"}

(* --------------------------------------------------------------------- *)
(* Helper functions to locate the node that a loop or query process serves *)
LoopHost(p) ==
    CHOOSE n \in Node :
        \E q \in SlushQueryProcess : <<n, p, q>> \in HostMapping

QueryHost(q) ==
    CHOOSE n \in Node :
        \E p \in SlushLoopProcess : <<n, p, q>> \in HostMapping

(* --------------------------------------------------------------------- *)
(* Message record type                                                    *)
Message == [type  : {"query", "reply", "term"},
            src   : (SlushLoopProcess \cup SlushQueryProcess),
            dst   : (SlushLoopProcess \cup SlushQueryProcess) \cup {NoMessage},
            color : (Colors \cup {NoColor})]

VARIABLES
    colors,    \* [Node -> (Colors \cup {NoColor})]
    msgs,      \* set of Message
    sample,    \* [SlushLoopProcess -> SUBSET Node]  (current sample set)
    iter       \* [SlushLoopProcess -> Nat]          (iterations done)

vars == <<colors, msgs, sample, iter>>

(* --------------------------------------------------------------------- *)
(* Initial state                                                          *)
Init ==
    /\ colors = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iter   = [p \in SlushLoopProcess |-> 0]

(* --------------------------------------------------------------------- *)
(* Actions *)

(* 1. External client assigns a random color to an uncolored node *)
ClientAssign ==
    /\ \E n \in Node :
          /\ colors[n] = NoColor
          /\ \E c \in Colors :
                /\ colors' = [colors EXCEPT ![n] = c]
                /\ UNCHANGED <<msgs, sample, iter>>

(* 2. Loop process selects a random sample and sends queries *)
SendQueries ==
    /\ \E p \in SlushLoopProcess :
          /\ iter[p] < SlushIterationCount
          /\ colors[LoopHost(p)] # NoColor
          /\ sample[p] = {}
          /\ LET host   == LoopHost(p)                     \* node owned by p
                 peers  == { n \in Node : n # host }       \* all other nodes
                 s      == CHOOSE s \subseteq peers :
                               Cardinality(s) = SampleSetSize
                 qset   == { q \in SlushQueryProcess :
                               \E n \in s : <<n, p, q>> \in HostMapping }
             IN
                /\ msgs'   = msgs \cup
                               { [type  |-> "query",
                                  src   |-> p,
                                  dst   |-> q,
                                  color |-> colors[host]] : q \in qset }
                /\ sample' = [sample EXCEPT ![p] = s]
                /\ UNCHANGED <<colors, iter>>

(* 3. Query process answers a received query (adopting color if uncolored) *)
RespondToQuery ==
    /\ \E q \in SlushQueryProcess :
          /\ \E m \in msgs :
                /\ m.type = "query"
                /\ m.dst  = q
                LET host == QueryHost(q) IN
                /\ IF colors[host] = NoColor
                      THEN colors' = [colors EXCEPT ![host] = m.color]
                      ELSE colors' = colors
                /\ msgs' = (msgs \ {m}) \cup
                           { [type  |-> "reply",
                              src   |-> q,
                              dst   |-> m.src,
                              color |-> colors'[host]] }
                /\ UNCHANGED <<sample, iter>>

(* 4. Loop process tallies replies and possibly flips its node's color *)
TallyAndFlip ==
    /\ \E p \in SlushLoopProcess :
          LET s == sample[p] IN
          /\ s # {}
          /\ \A n \in s :
                \E q \in SlushQueryProcess : <<n, p, q>> \in HostMapping
          /\ \A q \in { q \in SlushQueryProcess :
                         \E n \in s : <<n, p, q>> \in HostMapping } :
                \E m \in msgs :
                    /\ m.type = "reply"
                    /\ m.dst  = p
                    /\ m.src  = q
          LET replies   == { m \in msgs :
                               m.type = "reply" /\ m.dst = p }
              redCount  == Cardinality({ m \in replies : m.color = "Red" })
              blueCount == Cardinality({ m \in replies : m.color = "Blue" })
              flipColor == IF redCount >= PickFlipThreshold THEN "Red"
                           ELSE IF blueCount >= PickFlipThreshold THEN "Blue"
                           ELSE NoColor
          IN
                /\ IF flipColor # NoColor
                       THEN colors' = [colors EXCEPT ![LoopHost(p)] = flipColor]
                       ELSE colors' = colors
                /\ msgs'   = msgs \ replies
                /\ sample' = [sample EXCEPT ![p] = {}]
                /\ iter'   = [iter EXCEPT ![p] = @ + 1]
                /\ UNCHANGED <<>>

(* 5. After finishing its allotted iterations, a loop process broadcasts termination *)
LoopTerminate ==
    /\ \E p \in SlushLoopProcess :
          /\ iter[p] = SlushIterationCount
          /\ msgs' = msgs \cup
                      { [type  |-> "term",
                         src   |-> p,
                         dst   |-> NoMessage,
                         color |-> NoColor] }
          /\ UNCHANGED <<colors, sample, iter>>

(* 6. Query processes exit once every loop process has sent a termination message *)
QueryTerminate ==
    /\ \A p \in SlushLoopProcess :
          \E m \in msgs : m.type = "term" /\ m.src = p
    /\ UNCHANGED <<colors, msgs, sample, iter>>

(* --------------------------------------------------------------------- *)
Next ==
    \/ ClientAssign
    \/ SendQueries
    \/ RespondToQuery
    \/ TallyAndFlip
    \/ LoopTerminate
    \/ QueryTerminate

Spec == Init /\ [] [Next]_vars

(* --------------------------------------------------------------------- *)
(* Type safety invariant                                                  *)
TypeInvariant ==
    /\ colors \in [Node -> (Colors \cup {NoColor})]
    /\ msgs   \subseteq Message

====