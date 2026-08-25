---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
  Node,                \* set of node identifiers
  SlushLoopProcess,    \* set of loop process identifiers
  SlushQueryProcess,   \* set of query process identifiers
  HostMapping,         \* set of triples <<node, loopProc, queryProc>>
  SlushIterationCount, \* number of iterations each loop process performs
  SampleSetSize,       \* size of the peer sample taken each round
  PickFlipThreshold,   \* threshold for adopting a color
  NoColor,             \* special value meaning “uncolored”
  NoMessage            \* placeholder for “no message” (unused but required)

(* --algorithm SlushAlg
variables
  color    = [n \in Node |-> NoColor],
  messages = {},
  sample   = [l \in SlushLoopProcess |-> {}],
  iter     = [l \in SlushLoopProcess |-> 0],
  termSent = {},
  queryDone = {};

define
  ColorSet    == {"Red", "Blue"};
  MessageType == {"query", "reply", "term"};
  Message == [type  : MessageType,
              src   : (SlushLoopProcess \cup SlushQueryProcess),
              dst   : (SlushLoopProcess \cup SlushQueryProcess),
              color : ColorSet \cup {NoColor}];
  ChooseSubset(S, k) == CHOOSE sub \in SUBSET S : Cardinality(sub) = k;
end define;

process (c = "client")
{
  while TRUE do
    either
      with n \in Node do
        if color[n] = NoColor then
          either
            color := [color EXCEPT ![n] = "Red"]
          or
            color := [color EXCEPT ![n] = "Blue"]
          end either;
        end if;
      end with;
    or
      if \A n \in Node: color[n] # NoColor then
        skip;
      end if;
    end either;
  end while;
}

process (l \in SlushLoopProcess)
{
  variable myNode;
  myNode := CHOOSE n \in Node : <<n, l, _>> \in HostMapping;
  while TRUE do
    if color[myNode] = NoColor then
      skip;
    else
      while iter[l] < SlushIterationCount do
        sample := [sample EXCEPT ![l] = ChooseSubset(Node \\ {myNode}, SampleSetSize)];
        with s \in sample[l] do
          let qProc == CHOOSE q \in SlushQueryProcess :
                         <<myNode, l, q>> \in HostMapping in
            messages := messages \cup
              {[type  |-> "query",
                src   |-> l,
                dst   |-> qProc,
                color |-> color[myNode]]};
          end let;
        end with;
        (* In a full model we would wait for replies, tally them,
           and possibly flip the node's color.  This is abstracted
           away here. *)
        iter := [iter EXCEPT ![l] = @ + 1];
        sample := [sample EXCEPT ![l] = {}];
      end while;
      with allQ \in SlushQueryProcess do
        messages := messages \cup
          {[type  |-> "term",
            src   |-> l,
            dst   |-> allQ,
            color |-> NoColor]};
      end with;
      termSent := termSent \cup {l};
      break;
    end if;
  end while;
}

process (q \in SlushQueryProcess)
{
  variable myNode;
  myNode := CHOOSE n \in Node : <<n, _, q>> \in HostMapping;
  while TRUE do
    either
      with m \in messages do
        if m.type = "query" /\ m.dst = q then
          if color[myNode] = NoColor then
            color := [color EXCEPT ![myNode] = m.color];
          end if;
          messages := (messages \ {m}) \cup
            {[type  |-> "reply",
              src   |-> q,
              dst   |-> m.src,
              color |-> color[myNode]]};
        end if;
      end with;
    or
      with m \in messages do
        if m.type = "term" /\ m.dst = q then
          messages := messages \ {m};
          queryDone := queryDone \cup {q};
          break;
        end if;
      end with;
    end either;
  end while;
}
end algorithm; *)

(*-------------------------------------------------------------------*)
(* The PlusCal algorithm above generates the following TLA+ symbols: *)
(*   Init, Next, and the variables listed in the algorithm's header. *)

Spec == Init /\ [][Next]_<<color, messages, sample, iter, termSent, queryDone>>

MessageSet ==
  { [type  |-> t,
     src   |-> s,
     dst   |-> d,
     color |-> c] :
      t \in MessageType,
      s \in (SlushLoopProcess \cup SlushQueryProcess),
      d \in (SlushLoopProcess \cup SlushQueryProcess),
      c \in (ColorSet \cup {NoColor}) }

TypeInvariant ==
  /\ color \in [Node -> (ColorSet \cup {NoColor})]
  /\ messages \subseteq MessageSet

=============================================================================