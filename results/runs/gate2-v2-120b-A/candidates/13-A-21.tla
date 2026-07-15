---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, MaxNat, Nat

(*--algorithm Bakery
variables
  flag   = [i \in 1..N |-> FALSE],
  ticket = [i \in 1..N |-> 0];

define
  TypeOK == 
    /\ flag \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> Nat]
    /\ \A i \in 1..N: ticket[i] \in 0..MaxNat

  MutualExclusion == 
    \A i, j \in 1..N : i # j => 
      ~ ( ( flag[i] /\ \A k \in 1..N : (k # i => 
          ( ticket[k] = 0 ) \/ 
          ( ticket[k] # ticket[i] ) \/ 
          ( k > i ) ) ) 
          /\ 
          ( flag[j] /\ \A k \in 1..N : (k # j => 
          ( ticket[k] = 0 ) \/ 
          ( ticket[k] # ticket[j] ) \/ 
          ( k > j ) ) ) )

  Inv == TypeOK /\ MutualExclusion

  Init == 
    /\ flag = [i \in 1..N |-> FALSE]
    /\ ticket = [i \in 1..N |-> 0]
    /\ TypeOK

  Request(i) ==
    /\ flag[i] = FALSE
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ ticket' = [ticket EXCEPT ![i] = 
        IF MaxNat = 0 THEN 1 
        ELSE 1 + Max({ ticket[j] : j \in 1..N })]
    /\ UNCHANGED << >>

  Release(i) ==
    /\ flag[i] = TRUE
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED << >>

  Next ==
    \E i \in 1..N : Request(i) \/ Release(i)

  ISpec == Init /\ [][Next]_<<flag, ticket>>
end define;

(* Export the required identifiers *)
Spec == ISpec

====