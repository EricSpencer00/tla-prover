---- MODULE MissionariesAndCannibals
(***************************************************************************
 * This module specifies a system that models the one described in the     *
 * missionaries and cannibals problem.  On 20 December 2018, Wikipedia     *
 * contained the following description of this problem.                    *
 *                                                                         *
 *    [T]hree missionaries and three cannibals must cross a river using    *
 *    a boat which can carry at most two people, under the constraint      *
 *    that, for both banks, if there are missionaries present on the       *
 *    bank, they cannot be outnumbered by cannibals (if they were, the     *
 *    cannibals would eat the missionaries).  The boat cannot cross the    *
 *    river by itself with no people on board.                             *
 *                                                                         *
 * As explained below, we can use the specification and the TLC model      *
 * checker to find a solution to the problem.                              *
 ***************************************************************************)

 EXTENDS Integers, FiniteSets

 CONSTRAINTS Missionaries, Cannibals

 VARIABLES bank_of_boat, who_is_on_bank

 TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in
                [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

 Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> 
                               IF i = "E" THEN Cannibals \cup Missionaries
                                          ELSE  {} ]

 IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

 OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

 Move(S,b) == /\ Cardinality(S) \in {1,2}
             /\ LET newThisBank  == who_is_on_bank[b] \ S
                    newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
                IN  /\ IsSafe(newThisBank) 
                    /\ IsSafe(newOtherBank)
                    /\ bank_of_boat' = OtherBank(b)
                    /\ who_is_on_bank' = 
                         [i \in {"E","W"} |-> IF i = b THEN newThisBank 
                                                       ELSE newOtherBank]    

 Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : 
            Move(S, bank_of_boat)

 Solution == who_is_on_bank["E"] /= {}

====