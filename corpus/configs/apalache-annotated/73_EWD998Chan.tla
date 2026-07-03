----------------------------- MODULE EWD998Chan -----------------------------
(***************************************************************************)
(* TLA+ specification of an algorithm for distributed termination          *)
(* detection on a ring, due to Shmuel Safra, published as EWD 998:         *)
(* Shmuel Safra's version of termination detection.                        *)
(* Contrary to EWD998, this variant models message channels as sequences.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Utils

CONSTANT
  \* @type: Int;
  N
ASSUME NAssumption == N \in Nat \ {0} \* At least one node.

Node == 0 .. N-1
Color == {"white", "black"}

VARIABLES
 \* @type: Int -> Bool;
 active,
 \* @type: Int -> Str;
 color,
 \* @type: Int -> Int;
 counter,
 \* @type: Int -> Seq({type: Str, q: Int, color: Str});
 inbox
  
vars == <<active, color, counter, inbox>>

TokenMsg == [type : {"tok"}, q : Int, color : Color]
BasicMsg == [type : {"pl"}, q : {0}, color : Color]
Message == TokenMsg \cup BasicMsg

\* Apalache scratch copy: TypeOK's last conjunct (pairwise token-uniqueness
\* across two independently node-indexed, variable-length ranges) hits a
\* documented Apalache limitation -- "Expected a constant integer range in
\* [..]" for nested \A x \in 1..Len(var) quantifiers -- see
\* https://apalache-mc.org/docs/apalache/known-issues.html . TypeOK_Bounded
\* below is TypeOK with that one conjunct removed; checked instead, and
\* labeled as a subset, not full TypeOK. See APALACHE_FINDINGS.md spec 73.
TypeOK_Bounded ==
  /\ counter \in [Node -> Int]
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ \A i \in Node : \A j \in 1..Len(inbox[i]) :
       LET m == inbox[i][j] IN
         \/ (m.type = "tok" /\ m.color \in Color)
         \/ m.type = "pl"
  \* There is always exactly one token (singleton-type).
  /\ \E i \in Node : \E j \in DOMAIN inbox[i] : inbox[i][j].type = "tok"

------------------------------------------------------------------------------
 
Init ==
  (* Rule 0 *)
  /\ counter = [i \in Node |-> 0] \* c properly initialized
\*   /\ inbox = [i \in Node |-> IF i = 0 
\*                              THEN << [type |-> "tok", q |-> 0, color |-> "black" ] >> 
\*                              ELSE <<>>] \* with empty channels.
\* The token may be at any node of the ring initially.
  /\ inbox \in { f \in 
                    [ Node -> {<<>>, <<[type |-> "tok", q |-> 0, color |-> "black" ]>> } ] : 
                        Cardinality({ i \in DOMAIN f: f[i] # <<>> }) = 1 }
  (* EWD840 *) 
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]

InitiateProbe ==
  (* Rule 1 *)
  /\ \E j \in 1..Len(inbox[0]):
      \* Token is at node 0.
      /\ inbox[0][j].type = "tok"
      /\ \* Previous round inconsistent, if:
         \/ inbox[0][j].color = "black"
         \/ color[0] = "black"
         \* Implicit stated in EWD998 as c0 + q > 0 means that termination has not 
         \* been achieved: Initiate a probe if the token's color is white but the
         \* number of in-flight messages is not zero.
         \/ counter[0] + inbox[0][j].q # 0
      /\ inbox' = [inbox EXCEPT ![N-1] = Append(@, 
           [type |-> "tok", q |-> 0,
             (* Rule 6 *)
             color |-> "white"]), 
             ![0] = RemoveAt(@, j) ] \* consume token message from inbox[0]. 
  (* Rule 6 *)
  /\ color' = [ color EXCEPT ![0] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter>>                            
  
PassToken(i) ==
  (* Rule 2 *)
  /\ ~ active[i] \* If machine i is active, keep the token.
  /\ \E j \in 1..Len(inbox[i]) : 
          /\ inbox[i][j].type = "tok"
          \* the machine nr.i+1 transmits the token to machine nr.i under q := q + c[i+1]
          /\ LET tkn == inbox[i][j]
             IN  inbox' = [inbox EXCEPT ![i-1] = 
                                       Append(@, [tkn EXCEPT !.q = tkn.q + counter[i],
                                                             !.color = IF color[i] = "black"
                                                                       THEN "black"
                                                                       ELSE tkn.color]),
                                    ![i] = RemoveAt(@, j) ] \* pass on the token.
  (* Rule 7 *)
  /\ color' = [ color EXCEPT ![i] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter>>                            

System == \/ InitiateProbe
          \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i) ==
  \* Only allowed to send msgs if node i is active.
  /\ active[i]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  \* Non-deterministically choose a receiver node.
  /\ \E j \in Node \ {i} :
          \* Send a message (not the token) to j.
          /\ inbox' = [inbox EXCEPT ![j] = Append(@, [type |-> "pl", q |-> 0, color |-> "white" ] ) ]
          \* Note that we don't blacken node i as in EWD840 if node i
          \* sends a message to node j with j > i
  /\ UNCHANGED <<active, color>>                            

RecvMsg(i) ==
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  (* Rule 3 *)
  /\ color' = [ color EXCEPT ![i] = "black" ]
  \* Receipt of a message activates i.
  /\ active' = [ active EXCEPT ![i] = TRUE ]
  \* Consume a message (not the token!).
  /\ \E j \in 1..Len(inbox[i]) : 
          /\ inbox[i][j].type = "pl"
          /\ inbox' = [inbox EXCEPT ![i] = RemoveAt(@, j) ]
  /\ UNCHANGED <<>>                           

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, inbox, counter>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------

Next ==
  System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

(***************************************************************************)
(* The number of incoming messages of a node's given inbox.                *)
(***************************************************************************)
\* @type: ({type: Str, q: Int, color: Str}) => Bool;
IsPlMsg(msg) == msg.type = "pl"

\* @type: (Seq({type: Str, q: Int, color: Str})) => Int;
NumberOfMsg(ibx) == 
  Len(SelectSeq(ibx, IsPlMsg))

(***************************************************************************)
(* Bound the otherwise infinite state space that TLC has to check.         *)
(***************************************************************************)
StateConstraint ==
  /\ \A i \in DOMAIN inbox : NumberOfMsg(inbox[i]) < 3
\*  /\ \A i \in DOMAIN inbox : Len(inbox[i]) < 3
  \* Even with the number of in-flight messages restricted, we need a bound
  \* on the number of messages ever sent to exclude behaviors where two or
  \* more nodes forever alternate between send, receive, send, ...
  /\ \A i \in DOMAIN counter : counter[i] <= 3

-----------------------------------------------------------------------------

(***************************************************************************)
(* tpos \in Node s.t. the node's inbox contains the token.                *)
(***************************************************************************)
tpos ==
  CHOOSE i \in Node : \E j \in 1..Len(inbox[i]) : inbox[i][j].type = "tok"

token ==
    LET idx == CHOOSE i \in 1 .. Len(inbox[tpos]): inbox[tpos][i].type = "tok"
    IN inbox[tpos][idx]

(***************************************************************************)
(* EWD998 with channels refines EWD998 that models channels as sets.       *)
(***************************************************************************)
\* EWD998 refinement instance stripped for Apalache scratch copy (see APALACHE_FINDINGS.md spec 73 note) -- not referenced by Init/Next/TypeOK.

=============================================================================
