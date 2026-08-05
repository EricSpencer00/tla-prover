---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' that requires concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf     *)
(***************************************************************************)
EXTENDS Naturals

RecurSum(f, S) == IF S = {} THEN 0
                  ELSE LET x == CHOOSE x \in S : TRUE IN f[x] + RecurSum(f, S \ {x})

Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color
Complement(c1, c2) == IF c1 = c2
                      THEN c1
                      ELSE CHOOSE d \in Color \ {c1, c2} : TRUE

(* N = number of total meetings after which chameneoses fade; M = number of chameneoses *)
CONSTANTS N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, mall, numMeetings
vars == <<chameneoses, mall, numMeetings>>

ChameneosesID == 1..M
MallEmpty == CHOOSE e \in ChameneosesID : TRUE

TypeOK ==
  /\ chameneoses \in [ChameneosesID -> (Color \cup {Faded}) \X (0..N)]
  /\ mall \in ChameneosesID \cup {MallEmpty}

Init ==
  /\ chameneoses \in [ChameneosesID -> Color \X {0}]
  /\ mall = MallEmpty
  /\ numMeetings = 0

\* A chameneoses enters the empty meeting place or starts a meeting with one already there
Meet(c) ==
  /\ numMeetings < N
  /\ IF mall = MallEmpty
     THEN mall' = c
     ELSE /\ mall # c
          /\ LET newColor == Complement(chameneoses[c][1], chameneoses[mall][1])
          IN chameneoses' = [chameneoses EXCEPT ![c] = <<newColor, @[2] + 1>>,
                                          ![mall] = <<newColor, @[2] + 1>>]
          /\ mall' = MallEmpty
          /\ numMeetings' = numMeetings + 1
  /\ UNCHANGED <<chameneoses, mall, numMeetings>>

Next == \E c \in ChameneosesID : Meet(c)

Spec == Init /\ [][Next]_vars

\* Once N meetings have happened, every chameneoses has faded and the sum of all meetings is 2*N
SumMet == numMeetings = N => LET f[c \in ChameneosesID] == chameneoses[c][2]
                                  IN RecurSum(f, ChameneosesID) = 2 * N
====