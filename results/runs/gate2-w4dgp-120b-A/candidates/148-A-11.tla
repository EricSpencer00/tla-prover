---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME CalculateHash \in [PUBLIC, PUBLIC -> PUBLIC]

Recipient == Node \cup {NoHash}

RECURSIVE Sum(_)
Sum(S) == IF S = {} THEN 0
          ELSE LET x == CHOOSE e \in S : TRUE IN x + Sum(S \ {x})

RECURSIVE BalanceAt(_, _)
BalanceAt(h, c) == IF h = NoHash THEN 0
  ELSE IF h = NoBlockVal THEN 0
  ELSE IF h = NoHashVal THEN c
  ELSE IF h[3] = c THEN h[6] + BalanceAt(h[4], c)
  ELSE BalanceAt(h[4], c)

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeInvariant ==
  /\ lastHash \in PUBLIC \cup {NoHashVal}
  /\ ledger \in [Node -> [PUBLIC -> PUBLIC]]
  /\ received \in [Node -> SUBSET PUBLIC]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in PUBLIC |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock(n) ==
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash([NoHashVal, NoHashVal, NoHashVal, NoHashVal, NoHashVal, 0, GenesisBalance])
  /\ ledger' = [n \in Node |-> [h \in PUBLIC |->
         IF h = lastHash' THEN [NoHashVal, NoHashVal, NoHashVal, NoHashVal, NoHashVal, 0, GenesisBalance]
         ELSE ledger[n][h] ] ]
  /\ UNCHANGED received

CreateSendBlock(n, m) ==
  /\ lastHash # NoHashVal
  /\ BalanceAt(lastHash, n) >= 1
  /\ lastHash' = CalculateHash([lastHash, NoHashVal, m, NoHashVal, NoHashVal,
                        BalanceAt(lastHash, n) - 1, BalanceAt(lastHash, n) - 1])
  /\ ledger' = [n1 \in Node |-> IF n1 = n THEN [ledger[n1] EXCEPT ![lastHash'] =
                     [lastHash, NoHashVal, m, NoHashVal, NoHashVal, BalanceAt(lastHash, n) - 1, BalanceAt(lastHash, n) - 1]]
                     ELSE ledger[n1] ]
  /\ received' = [n1 \in Node |-> @ \cup {lastHash'}]

CreateOpenBlock(n) ==
  /\ lastHash # NoHashVal
  /\ BalanceAt(lastHash, n) = 0
  /\ \E x \in PUBLIC : ledger[n][x] # NoBlockVal /\ ledger[n][x][3] = n
  /\ LET x == CHOOSE y \in PUBLIC : ledger[n][y] # NoBlockVal /\ ledger[n][y][3] = n
     IN /\ BalanceAt(x, n) > 0
        /\ lastHash' = CalculateHash([lastHash, NoHashVal, NoHashVal, NoHashVal, x,
                         BalanceAt(x, n), BalanceAt(x, n)])
        /\ ledger' = [n1 \in Node |-> IF n1 = n THEN [ledger[n1] EXCEPT ![lastHash'] =
                     [lastHash, NoHashVal, NoHashVal, NoHashVal, x,
                      BalanceAt(x, n), BalanceAt(x, n)]]
                     ELSE ledger[n1] ]
        /\ received' = [n1 \in Node |-> @ \cup {lastHash'}]

CreateReceiveBlock(n, x) ==
  /\ lastHash # NoHashVal
  /\ ledger[n][x] # NoBlockVal
  /\ ledger[n][x][3] = n
  /\ BalanceAt(x, n) # 0
  /\ \A y \in PUBLIC : IF y # x THEN ledger[n][y] # NoBlockVal
        ELSE ledger[n][y][3] = NoHashVal
  /\ lastHash' = CalculateHash([lastHash, NoHashVal, NoHashVal, x, NoHashVal,
                    BalanceAt(x, n) + BalanceAt(lastHash, n), BalanceAt(x, n) + BalanceAt(lastHash, n)])
  /\ ledger' = [n1 \in Node |-> IF n1 = n THEN [ledger[n1] EXCEPT ![lastHash'] =
                     [lastHash, NoHashVal, NoHashVal, x, NoHashVal,
                      BalanceAt(x, n) + BalanceAt(lastHash, n), BalanceAt(x, n) + BalanceAt(lastHash, n)]]
                     ELSE ledger[n1] ]
  /\ received' = [n1 \in Node |-> @ \cup {lastHash'}]

CreateChangeRepresentativeBlock(n, r) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHash([lastHash, NoHashVal, NoHashVal, NoHashVal, r,
                        BalanceAt(lastHash, n), BalanceAt(lastHash, n)])
  /\ ledger' = [n1 \in Node |-> IF n1 = n THEN [ledger[n1] EXCEPT ![lastHash'] =
                     [lastHash, NoHashVal, NoHashVal, NoHashVal, r,
                      BalanceAt(lastHash, n), BalanceAt(lastHash, n)]]
                     ELSE ledger[n1] ]
  /\ received' = [n1 \in Node |-> @ \cup {lastHash'}]

Validate(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] # NoBlockVal
  /\ ledger' = [n1 \in Node |-> IF n1 = n THEN [ledger[n1] EXCEPT ![h] = @]
                     ELSE ledger[n1] ]
  /\ received' = [n1 \in Node |-> IF n1 = n THEN @ \ {h} ELSE @ ]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesisBlock(n)
  \/ \E n \in Node, m \in Node : CreateSendBlock(n, m)
  \/ \E n \in Node : CreateOpenBlock(n)
  \/ \E n \in Node, x \in PUBLIC : CreateReceiveBlock(n, x)
  \/ \E n \in Node, r \in PUBLIC : CreateChangeRepresentativeBlock(n, r)
  \/ \E n \in Node, h \in PUBLIC : Validate(n, h)

Spec == Init /\ [][Next]_vars

BalanceInvariant == Sum({BalanceAt(lastHash, c) : c \in Node}) <= GenesisBalance

SafetyInvariant ==
  \A n \in Node : \A h \in PUBLIC : ledger[n][h] # NoBlockVal => ledger[n][h][1] = NoHash

====