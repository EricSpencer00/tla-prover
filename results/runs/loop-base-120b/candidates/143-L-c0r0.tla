---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ---------------------------------------------------------------------- *)
(*  Constants representing the two river banks                           *)
(* ---------------------------------------------------------------------- *)
East == "East"
West == "West"

(* ---------------------------------------------------------------------- *)
(*  Variables                                                            *)
(* ---------------------------------------------------------------------- *)
VARIABLES boat, bank

(* ---------------------------------------------------------------------- *)
(*  Helper definitions                                                   *)
(* ---------------------------------------------------------------------- *)
People == Missionaries \cup Cannibals

Opposite(b) == IF b = East THEN West ELSE East

SafeBank(bnk, b) ==
  LET m == { p \in bnk[b] : p \in Missionaries } IN
  LET c == { p \in bnk[b] : p \in Cannibals } IN
    (m = {}) \/ (Cardinality(c) <= Cardinality(m))

(* ---------------------------------------------------------------------- *)
(*  Initial state                                                        *)
(* ---------------------------------------------------------------------- *)
Init ==
  /\ boat = East
  /\ bank = [East |-> People,
             West |-> {}]

(* ---------------------------------------------------------------------- *)
(*  Move action                                                          *)
(* ---------------------------------------------------------------------- *)
Next ==
  \E g \subseteq bank[boat] :
    /\ Cardinality(g) \in 1..2
    /\ LET newBank ==
          [bank EXCEPT
             ![boat] = bank[boat] \ g,
             ![Opposite(boat)] = bank[Opposite(boat)] \cup g]
       IN
         /\ SafeBank(newBank, boat)
         /\ SafeBank(newBank, Opposite(boat))
    /\ boat' = Opposite(boat)
    /\ bank' = newBank

(* ---------------------------------------------------------------------- *)
(*  Type correctness invariant                                            *)
(* ---------------------------------------------------------------------- *)
TypeOK ==
  /\ boat \in {East, West}
  /\ bank \in [ {East, West} -> SUBSET People ]
  /\ UNION bank[East] \cup bank[West] = People
  /\ \A b \in {East, West} : SafeBank(bank, b)

(* ---------------------------------------------------------------------- *)
(*  Solution invariant (east bank empty)                                 *)
(* ---------------------------------------------------------------------- *)
Solution == bank[East] = {}

====