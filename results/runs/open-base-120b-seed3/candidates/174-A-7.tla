---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess, HostMapping,
  SlushIterationCount, SampleSetSize, PickFlipThreshold,
  NoColor, NoMessage

(* ---------------------------------------------------------------------- *)
(*  Basic definitions *)
(* ---------------------------------------------------------------------- *)

Color == {"Red", "Blue"}

Message == [type : {"query", "reply", "term"},
            src  : (SlushLoopProcess \cup SlushQueryProcess),
            dst  : (SlushLoopProcess \cup SlushQueryProcess),
            col  : (Color \cup {NoColor, NoMessage})]

(* Mapping helpers *)
NodeOfLoop(p) == CHOOSE t \in HostMapping : t.loop = p .node
NodeOfQuery(q) == CHOOSE t \in HostMapping : t.query = q .node

(* Choose a subset of the required size *)
PickSample(S) == CHOOSE T \in SUBSET S : Cardinality(T) = SampleSetSize

(* ---------------------------------------------------------------------- *)
(*  PlusCal algorithm *)
(* ---------------------------------------------------------------------- *)

--algorithm SlushAlg
variables
  color   \in [Node -> (Color \cup {NoColor})],
  msgs    \subseteq Message,
  sample  \in [SlushLoopProcess -> SUBSET SlushQueryProcess],
  iter    \in [SlushLoopProcess -> Nat],
  termCnt \in Nat;

process (client = "client")
begin
  while \E n \in Node : color[n] = NoColor do
    with n \in { n \in Node : color[n] = NoColor } do
      either
        color := [color EXCEPT ![n] = "Red"];
      or
        color := [color EXCEPT ![n] = "Blue"];
      end either;
    end with;
  end while;
end process;

process (lp \in SlushLoopProcess)
variables node, mySample, replies;
begin
  node := NodeOfLoop(lp);
  while color[node] = NoColor do
    skip;
  end while;

  while iter[lp] < SlushIterationCount do
    (* choose a sample of peers' query processes *)
    mySample := PickSample({ q \in SlushQueryProcess : NodeOfQuery(q) # node });
    sample := [sample EXCEPT ![lp] = mySample];

    (* send query messages *)
    with q \in mySample do
      msgs := msgs \cup {[type |-> "query", src |-> lp, dst |-> q,
                         col |-> color[node]]};
    end with;

    (* collect replies *)
    replies := {};
    while Cardinality(replies) < SampleSetSize do
      with m \in msgs do
        if /\ m.type = "reply"
           /\ m.dst = lp
        then
          replies := replies \cup {m.col};
          msgs := msgs \ {m};
        end if;
      end with;
    end while;

    (* tally and possibly flip *)
    let red  == Cardinality({c \in replies : c = "Red"});
        blue == Cardinality({c \in replies : c = "Blue"});
    in
      if red >= PickFlipThreshold then
        color := [color EXCEPT ![node] = "Red"];
      elsif blue >= PickFlipThreshold then
        color := [color EXCEPT ![node] = "Blue"];
      else
        skip;
      end if;
    end let;

    iter := [iter EXCEPT ![lp] = @ + 1];
    sample := [sample EXCEPT ![lp] = {}];
  end while;

  (* broadcast termination *)
  with q \in SlushQueryProcess do
    msgs := msgs \cup {[type |-> "term", src |-> lp, dst |-> q,
                       col |-> NoMessage]};
  end with;
end process;

process (q \in SlushQueryProcess)
variables node;
begin
  node := NodeOfQuery(q);
  while TRUE do
    either
      with m \in msgs do
        if /\ m.type = "term"
           /\ m.dst = q
        then
          termCnt := termCnt + 1;
          msgs := msgs \ {m};
          if termCnt = Cardinality(SlushLoopProcess) then
            halt;
          end if;
        elsif /\ m.type = "query"
              /\ m.dst = q
        then
          if color[node] = NoColor then
            color := [color EXCEPT ![node] = m.col];
          end if;
          msgs := msgs \cup {[type |-> "reply", src |-> q,
                             dst |-> m.src, col |-> color[node]]};
          msgs := msgs \ {m};
        end if;
      end with;
    or
      skip;
    end either;
  end while;
end process;
end algorithm;

(* ---------------------------------------------------------------------- *)
(*  Specification and invariants *)
(* ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<color, msgs, sample, iter, termCnt>>

TypeInvariant ==
  /\ color \in [Node -> (Color \cup {NoColor})]
  /\ msgs \subseteq Message

====