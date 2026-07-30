---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node,
    GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME GenesisBalance \in Nat

\* Block type with an explicit arithmetic weight, to keep the chain bounded.
BlockType == [weight : Nat]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

RECURSIVE ChainWeight(_)
ChainWeight(h) == IF h = NoHashVal THEN 0
                  ELSE LET b == ledger[NoHash][h] IN b.weight + ChainWeight(b.prev)

RECURSIVE Balance(_)
Balance(h) == IF h = NoHashVal THEN 0
              ELSE LET b == ledger[NoHash][h] IN b.delta + Balance(b.prev)

TypeInvariant ==
    /\ lastHash \in {NoHashVal} \cup Hash
    /\ ledger \in [Hash -> [Hash -> BlockType \cup {NoBlockVal}]]
    /\ received \in [Node -> SUBSET Hash]

\* A block's signature must be authentic and its balance must still fit.
SafetyInvariant ==
    \A n \in Hash :
        /\ (ledger[NoHash][n] # NoBlockVal => ledger[NoHash][n].owner \in {ledger[NoHash][n].rep})
        /\ (ledger[NoHash][n] # NoBlockVal => ChainWeight(n) <= GenesisBalance)

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Hash |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock(n, k) ==
    /\ lastHash = NoHashVal
    /\ CHOOSE h \in Hash :
        /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![NoHash][h] = [owner |-> k, delta |-> GenesisBalance, prev |-> NoHashVal, rep |-> {k}]]
    /\ received' = [x \in Node |-> received[x] \cup {h}]

CreateSendBlock(n, from, k, to) ==
    /\ lastHash # NoHashVal
    /\ ledger[NoHash][lastHash].owner = from
    /\ Balance(lastHash) >= k
    /\ CHOOSE h \in Hash :
        /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![NoHash][h] = [owner |-> from, delta |-> -k, prev |-> lastHash, rep |-> {from}]]
    /\ received' = [x \in Node |-> received[x] \cup {h}]

CreateOpenBlock(n, from, k) ==
    /\ lastHash # NoHashVal
    /\ ledger[NoHash][lastHash].owner = from
    /\ ledger[NoHash][lastHash].delta = -k
    /\ CHOOSE h \in Hash :
        /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![NoHash][h] = [owner |-> k, delta |-> k, prev |-> NoHashVal, rep |-> {k}]]
    /\ received' = [x \in Node |-> received[x] \cup {h}]

CreateReceiveBlock(n, from, k) ==
    /\ lastHash # NoHashVal
    /\ ledger[NoHash][lastHash].owner = from
    /\ ledger[NoHash][lastHash].delta = k
    /\ CHOOSE h \in Hash :
        /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![NoHash][h] = [owner |-> k, delta |-> -k, prev |-> lastHash, rep |-> {k}]]
    /\ received' = [x \in Node |-> received[x] \cup {h}]

CreateChangeRepBlock(n, k) ==
    /\ lastHash # NoHashVal
    /\ ledger[NoHash][lastHash].owner = k
    /\ CHOOSE h \in Hash :
        /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![NoHash][h] = [owner |-> k, delta |-> 0, prev |-> lastHash, rep |-> {k}]]
    /\ received' = [x \in Node |-> received[x] \cup {h}]

Validate(n, h) ==
    /\ h \in received[n]
    /\ ledger' = [ledger EXCEPT ![NoHash][h] = ledger[NoHash][h]]
    /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
    /\ UNCHANGED lastHash

Next ==
    \/ \E n \in Node, k \in PublicKey : CreateGenesisBlock(n, k) \/ CreateChangeRepBlock(n, k)
    \/ \E n \in Node, f \in PublicKey, k \in 1..GenesisBalance :
           CreateSendBlock(n, f, k, f) \/ CreateOpenBlock(n, f, k) \/ CreateReceiveBlock(n, f, k)
    \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

====