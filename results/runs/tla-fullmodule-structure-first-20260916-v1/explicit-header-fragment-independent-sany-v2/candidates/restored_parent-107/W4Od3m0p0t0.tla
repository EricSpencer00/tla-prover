---- MODULE W4Od3m0p0t0 ----
VARIABLES banks, lock, last, crashed

CONSTANTS NumBanks

vars == <<NumBanks, lock, last, crashed>>

Init == /\ lock = "none"
       /\ last = "none"
       /\ crashed = [ <<1..NumBanks>> |-> "none" ]
       /\ banks = [ <<1..NumBands>> |-> "idle" ]

Next == \/ lock' = IF banks' = banks /\ crashed' = crashed
                 THEN IF banks' = [ <<1..NumBans>> |-> "idle" ]
                          THEN "none"
                          ELSE "none"
                 ELSE "none"
            \/ lock' = "none"
            \/ last' = IF banks' = banks
                          /\ crashed' = crashed
                          /\ lock' = "none"
                          /\ \E b \in 1..NumBanks : banks' = [ b |-> "idle" ]
                          /\ \E b \in banks : banks' = [ b |->[ "idle" ] ]
                          /\ \E b \e banks : banks' = [ b -> "idle" ]
                          /\ \A b \in banks : banks' (b) # "idle"
                          /\ \A b \in 1..Numbanks : crashed' (b) # "none"
                          /\ lock = "none"
                          /\ banks' = [ b |-> IF b = last /\ crashed' (b) = "none"
                                              THEN "idle"
                                              ELSE banks' (b) ]
                          /\ last' = "none"
                          /\ UNCHANGED banks
                          /\ UNCHANGED crashed
                          /\ UNCHANGED last
                          ELSE UNCHANGED <<lock, last, crashed, banks>>

Spec == Init /\ [][Next]_vars

Spec == Init /\ [][Next](vars) /\ [][Next](vars) => Init

====