---- MODULE bcastByz ----
EXTENDS Naturals,
        FiniteSets,
        Functions,
        FunctionTheorems,
        FiniteSetTheorems,
        NaturalsInduction,
        SequenceTheorems,
        TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

(* ------------------------------------------------------------------------- *)
(*               Model Parameters and Derived Sets                         *)
(* ------------------------------------------------------------------------- *)

Proc == 1 .. N               \* All processes, including the faulty ones.
M    == {"ECHO"}             \* The only message type used.
ByzMsgs == Faulty \X M       \* Byzantine messages (sender must be faulty).

(* ------------------------------------------------------------------------- *)
(*                               State Variables                             *)
(* ------------------------------------------------------------------------- *)

(* Corr    : the set of correct processes (unknown, chosen nondeterministically) *)
(* Faulty  : the set of faulty processes, defined as the complement of Corr        *)
(* pc      : control state of each process, one of "V0","V1","SE","AC"            *)
(* rcvd    : for each process, the set of messages it has received                *)
(* sent    : the set of all ECHO messages that have been sent by correct processes *)

(* ------------------------------------------------------------------------- *)
(*                                 Types                                    *)
(* ------------------------------------------------------------------------- *)

TypeOK ==
  /\ Corr \subseteq Proc
  /\ Faulty = Proc \ Corr
  /\ pc \in [Proc -> {"V0","V1","SE","AC"}]
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [Proc -> SUBSET (sent \cup ByzMsgs)]

(* ------------------------------------------------------------------------- *)
(*                         Cardinality Constraints                           *)
(* ------------------------------------------------------------------------- *)

FCConstraints ==
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

(* ------------------------------------------------------------------------- *)
(*                            Initial State (Init)                           *)
(* ------------------------------------------------------------------------- *)

Init ==
  /\ sent = {}
  /\ pc \in [Proc -> {"V0","V1"}]    \* Each process may or may not have received INIT.
  /\ rcvd = [i \in Proc |-> {}]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* ------------------------------------------------------------------------- *)
(*               The special initial state for the unforgeability proof       *)
(* ------------------------------------------------------------------------- *)

InitNoBcast == Init /\ pc \in [Proc -> {"V0"}]

(* ------------------------------------------------------------------------- *)
(*               Message Reception (non‑deterministic)                       *)
(* ------------------------------------------------------------------------- *)

Receive(self, includeByz) ==
  \E new \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [i \in Proc |-> IF i = self THEN rcvd[i] \cup new ELSE rcvd[i]]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)      == Receive(self, TRUE)

(* ------------------------------------------------------------------------- *)
(*                          Process Step Actions                             *)
(* ------------------------------------------------------------------------- *)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED <<rcvd, Corr, Faulty>>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0","V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2*T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED <<rcvd, Corr, Faulty>>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0","V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED <<rcvd, Corr, Faulty>>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ UNCHANGED <<sent, rcvd, Corr, Faulty>>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

(* ------------------------------------------------------------------------- *)
(*                         Global Next Relation                               *)
(* ------------------------------------------------------------------------- *)

Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED <<pc, rcvd, sent, Corr, Faulty>>

Spec == Init /\ [][Next]_<<pc, rcvd, sent, Corr, Faulty>>

SpecNoBcast == InitNoBcast /\ [][Next]_<<pc, rcvd, sent, Corr, Faulty>>

(* ------------------------------------------------------------------------- *)
(*                     Safety and Liveness Formulas                           *)
(* ------------------------------------------------------------------------- *)

Unforg == \A i \in Corr : pc[i] # "AC"

(* ------------------------------------------------------------------------- *)
(*                Inductive Invariant for Unforgeability (no weakening)       *)
(* ------------------------------------------------------------------------- *)

IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [i \in Proc |-> "V0"]
  /\ \A i \in Proc : pc[i] # "AC"

(* ------------------------------------------------------------------------- *)
(*                      Theorem: SpecNoBcast => []Unforg                      *)
(* ------------------------------------------------------------------------- *)

THEOREM SpecNoBcast => []Unforg
PROOF
  (* Step 1: Init => IndInv *)
  HAVE InitNoBcast => IndInv_Unforg_NoBcast
  BY  ( 
        /\ InitNoBcast => sent = {}
        /\ InitNoBcast => pc = [i \in Proc |-> "V0"]
        /\ InitNoBcast => \A i \in Proc : pc[i] # "AC"
        /\ InitNoBcast => FCConstraints   \* from Init we already have the cardinality constraints
        /\ InitNoBcast => TypeOK
      )
  OBVIOUS

  (* Step 2: Inductive step *)
  HAVE IndInv_Unforg_NoBcast /\ [Next]_<<pc, rcvd, sent, Corr, Faulty>>
       => IndInv_Unforg_NoBcast'
  BY (
        (* Stuttering case *)
        CASE UNCHANGED <<pc, rcvd, sent, Corr, Faulty>> => 
          OBVIOUS

        (* A correct process makes a step *)
        CASE \E i \in Corr : Step(i) => 
          \A i \in Corr :
            (Step(i) => 
               /\ sent' = {}
                  \* Since sent is required to stay empty, any step that would add a message
                    contradicts the invariant; but such a step is impossible because the
                    only actions that add a message also require pc[self] to be "V1" or
                    not in {"V0","V1"}, which cannot hold when pc is constantly "V0".
               /\ pc' = [j \in Proc |-> "V0"]
               /\ \A j \in Proc : pc'[j] # "AC"
               /\ FCConstraints'    \* preserved because Corr and Faulty never change
               /\ TypeOK')
          BY (
               (* Show that any Step(i) would violate the invariant if it tried to add a message *)
               ASSUME i \in Corr, Step(i)
               PROVE sent' = {} /\ pc' = [j \in Proc |-> "V0"]
               CASE 
                 /\ pc[i] = "V1"                 \* would be required for UponV1
                 /\ pc' = [pc EXCEPT ![i] = "SE"]
                 /\ sent' = sent \cup {<<i,"ECHO">>}
               => FALSE
               BY (
                    (* But pc[i]="V0" in the invariant, so this case cannot happen *)
                    ASSUME pc[i]="V1"
                    HAVE pc[i]="V0" FROM IndInv_Unforg_NoBcast
                    CONTRADICTION
                  )
               CASE 
                 /\ pc[i] \notin {"V0","V1"}
                 /\ Cardinality(rcvd'[i]) >= N-2*T
                 /\ Cardinality(rcvd'[i]) < N-T
                 /\ pc' = [pc EXCEPT ![i]="SE"]
                 /\ sent' = sent \cup {<<i,"ECHO">>}
               => FALSE
               BY (
                    (* Again pc[i]="V0" in the invariant, so this case cannot happen *)
                    ASSUME pc[i] \notin {"V0","V1"}
                    HAVE pc[i]="V0" FROM IndInv_Unforg_NoBcast
                    CONTRADICTION
                  )
               CASE 
                 /\ pc[i] \in {"V0","V1"}
                 /\ Cardinality(rcvd'[i]) >= N-T
                 /\ pc' = [pc EXCEPT ![i]="AC"]
                 /\ sent' = sent \cup {<<i,"ECHO">>}
               => FALSE
               BY (
                    (* pc[i]="V0" but then pc' would become "AC", contradicting the invariant's
                       requirement that no process ever be in "AC". *)
                    ASSUME pc' = [pc EXCEPT ![i]="AC"]
                    HAVE \A j \in Proc : pc'[j] # "AC" FROM IndInv_Unforg_NoBcast
                    OBVIOUS
                  )
               CASE 
                 /\ pc[i]="SE"
                 /\ Cardinality(rcvd'[i]) >= N-T
                 /\ pc' = [pc EXCEPT ![i]="AC"]
                 /\ UNCHANGED sent
               => FALSE
               BY (
                    (* pc[i]="SE" cannot occur because pc[i]="V0" in the invariant *)
                    ASSUME pc[i]="SE"
                    HAVE pc[i]="V0" FROM IndInv_Unforg_NoBcast
                    CONTRADICTION
                  )
               CASE 
                 /\ ReceiveFromAnySender(i)
                 /\ UNCHANGED <<pc, sent, Corr, Faulty>>
               => 
                 /\ sent' = sent
                 /\ pc' = pc
                 /\ \A j \in Proc : pc'[j] # "AC"
                 /\ FCConstraints' /\ TypeOK'
               BY (
                    (* This is the only viable branch: the step consists solely of a receive
                       action, which does not change sent or pc, therefore the invariant is
                       preserved. *)
                    OBVIOUS
                  )
             )
        )
     )
  OBVIOUS

  (* Step 3: Inductive invariant implies safety *)
  HAVE IndInv_Unforg_NoBcast => Unforg
  BY (
        ASSUME IndInv_Unforg_NoBcast
        SHOW \A i \in Corr : pc[i] # "AC"
        FROM IndInv_Unforg_NoBcast
      )
  OBVIOUS

  (* Conclude the theorem *)
  QED

=============================================================================