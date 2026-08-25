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
(*   Basic definitions                                                   *)
(* --------------------------------------------------------------------- *)

Color == {"Red", "Blue", NoColor}

MessageType == {"Query", "Reply", "Terminate"}

Message == [type : MessageType,
            src  : (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}),
            dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"All"}),
            col  : Color]

(* Mapping from processes to their host node *)
HostNodeOfLoop(lp) == 
    CHOOSE n \in Node : <<n, lp, _>> \in HostMapping

HostNodeOfQuery(qp) == 
    CHOOSE n \in Node : <<n, _, qp>> \in HostMapping

HostQueryNode(n) == 
    CHOOSE qp \in SlushQueryProcess : <<n, _, qp>> \in HostMapping

(* Choose a subset of a given size (nondeterministic) *)
ChooseSubset(S, k) == 
    CHOOSE sub \in SUBSET S : Cardinality(sub) = k

VARIABLES 
    color,          \* [Node -> Color]
    msgs            \* SUBSET Message

(* --------------------------------------------------------------------- *)
(*   PlusCal algorithm                                                   *)
(* --------------------------------------------------------------------- *)

(*--algorithm SlushAlg
variables 
    color = [n \in Node |-> NoColor],
    msgs  = {};

process (Client)
{
  while (TRUE) {
    if (\E n \in Node : color[n] = NoColor) {
      with n \in { n \in Node : color[n] = NoColor } do
        either
          color := [color EXCEPT ![n] = "Red"];
        [] 
          color := [color EXCEPT ![n] = "Blue"];
        end either;
      end with;
    } else {
      break;
    }
  }
}

process (lp \in SlushLoopProcess)
{
  variable hostNode = HostNodeOfLoop(lp);
  variable i = 0;
  while (color[hostNode] = NoColor) { skip; }
  while (i < SlushIterationCount) {
    variable sample = ChooseSubset(Node \\ {hostNode}, SampleSetSize);
    with peer \in sample do
      msgs := msgs \cup {
        [type |-> "Query",
         src  |-> lp,
         dst  |-> HostQueryNode(peer),
         col  |-> color[hostNode]]
      };
    end with;
    variable replies = {};
    while (Cardinality(replies) < SampleSetSize) {
      with m \in msgs :
          m.type = "Reply" /\ m.dst = lp
      do
        replies := replies \cup { m.col };
        msgs    := msgs \ { m };
      end with;
    }
    variable redCount  = Cardinality({c \in replies : c = "Red"});
    variable blueCount = Cardinality({c \in replies : c = "Blue"});
    if (redCount >= PickFlipThreshold) then
      color := [color EXCEPT ![hostNode] = "Red"];
    elsif (blueCount >= PickFlipThreshold) then
      color := [color EXCEPT ![hostNode] = "Blue"];
    end if;
    i := i + 1;
  }
  msgs := msgs \cup {
    [type |-> "Terminate",
     src  |-> lp,
     dst  |-> "All",
     col  |-> NoMessage]
  };
}

process (qp \in SlushQueryProcess)
{
  variable hostNode = HostNodeOfQuery(qp);
  while (TRUE) {
    with m \in msgs :
        m.type = "Query" /\ m.dst = qp
    do
      if (color[hostNode] = NoColor) {
        color := [color EXCEPT ![hostNode] = m.col];
      };
      msgs := msgs \cup {
        [type |-> "Reply",
         src  |-> qp,
         dst  |-> m.src,
         col  |-> color[hostNode]]
      };
      msgs := msgs \ { m };
    end with;
    if (\A lp \in SlushLoopProcess :
          \E t \in msgs : t.type = "Terminate" /\ t.src = lp) then
      break;
    end if;
  }
}
end algorithm; *)

(* --------------------------------------------------------------------- *)
(*   Specification and invariants                                         *)
(* --------------------------------------------------------------------- *)

Spec == Init /\ [] [][Next]_<<color, msgs>>

TypeInvariant ==
  /\ color \in [Node -> Color]
  /\ msgs  \subseteq Message

====