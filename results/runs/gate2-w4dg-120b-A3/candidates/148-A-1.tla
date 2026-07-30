---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
    CalculateHash, NoHash, NoBlock

VARIABLES
    lastHash, ledger, received

vars == <<lastHash, ledger, received>>

HashCodes == Hash \cup {NoHash}

SignedBlock ==
    [hash: HashCodes, acct: PublicKey, prev: HashCodes,
     kind: {"genesis", "send", "open", "receive", "change"},
     target: PublicKey, amount: Nat]

\* Balance of an account is the sum of amounts on its own chain, walked recursively.
RECURSIVE Balance(_)
Balance(pk) ==
    IF \E b \in Hash : b \in ledger[Node][NoHash] /\ b.acct = pk
    THEN LET b == CHOOSE x \in Hash : x \in ledger[Node][NoHash] /\ x.acct = pk
         IN IF b.kind = "send" THEN 0 ELSE b.amount + Balance(b.prev) - (IF b.kind = "receive" THEN b.amount ELSE 0)
    ELSE 0

RECURSIVE TotalBalance(_)
TotalBalance(S) ==
    IF S = {} THEN 0
    ELSE LET pk == CHOOSE x \in S : TRUE IN Balance(pk) + TotalBalance(S \ {pk})

Owner(pk) == CHOOSE k \in PrivateKey : PK(k) = pk

TypeInvariant ==
    /\ lastHash \in HashCodes
    /\ ledger \in [Node -> [HashCodes -> SignedBlock \cup {NoBlockVal}]]
    /\ received \in [Node -> SUBSET SignedBlock]

\* Signature validation: every recorded block's signature must come from the key
\* that owns the account chain the block sits on.
SafetyInvariant ==
    \A n \in Node : \A h \in HashCodes :
        ledger[n][h] # NoBlockVal => Owner(ledger[n][h].acct) \in PrivateKey

Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [n \in Node |-> [h \in HashCodes |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

CreateGenesisBlock ==
    /\ lastHash = NoHashVal
    /\ \E k \in PrivateKey :
         /\ \E h \in Hash :
              /\ lastHash' = h
              /\ \A n \in Node :
                   ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![h] = [hash |-> h, acct |-> PK(k), prev |-> NoHash, kind |-> "genesis", target |-> "none", amount |-> GenesisBalance]]]
              /\ received' = [received EXCEPT ![n] = { [hash |-> h, acct |-> PK(k), prev |-> NoHash, kind |-> "genesis", target |-> "none", amount |-> GenesisBalance] } \cup @]
    /\ UNCHANGED <<>>

CreateSendBlock ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node, k \in PrivateKey, amt \in Nat, tgt \in PublicKey :
         /\ k \in Owner(n)
         /\ amt > 0 /\ amt <= Balance(PK(k))
         /\ \E h \in Hash :
              /\ lastHash' = h
              /\ ledger' = [ledger EXCEPT ![n][h] = [hash |-> h, acct |-> PK(k), prev |-> lastHash, kind |-> "send", target |-> tgt, amount |-> amt]]
              /\ received' = [received EXCEPT ![n] = @ \cup { [hash |-> h, acct |-> PK(k), prev |-> lastHash, kind |-> "send", target |-> tgt, amount |-> amt] }]
    /\ UNCHANGED <<>>

CreateOpenBlock ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node, k \in PrivateKey, ref \in SignedBlock :
         /\ k \in Owner(n)
         /\ ref.kind = "send" /\ ref.target = PK(k)
         /\ \E h \in Hash :
              /\ lastHash' = h
              /\ ledger' = [ledger EXCEPT ![n][h] = [hash |-> h, acct |-> PK(k), prev |-> lastHash, kind |-> "open", target |-> ref.acct, amount |-> ref.amount]]
              /\ received' = [received EXCEPT ![n] = @ \cup { [hash |-> h, acct |-> PK(k), prev |-> lastHash, kind |-> "open", target |-> ref.acct, amount |-> ref.amount] }]
    /\ UNCHANGED <<>>

CreateReceiveBlock ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node, k \in PrivateKey, ref \in SignedBlock :
         /\ k \in Owner(n)
         /\ ref.kind = "send" /\ ref.target = PK(k)
         /\ \E h \in Hash :
              /\ lastHash' = h
              /\ ledger' = [ledger EXCEPT ![n][h] = [hash |-> h, acct |-> PK(k), prev |-> lastHash, kind |-> "receive", target |-> ref.acct, amount |-> ref.amount]]
              /\ received' = [received EXCEPT ![n] = @ \cup { [hash |-> h, acct |-> PK(k), prev |-> lastHash, kind |-> "receive", target |-> ref.acct, amount |-> ref.amount] }]
    /\ UNCHANGED <<>>

CreateChangeRepresentative ==
    /\ lastHash # NoHashVal
    /\ \E n \in Node, k \in PrivateKey :
         /\ k \in Owner(n)
         /\ \E h \in Hash :
              /\ lastHash' = h
              /\ ledger' = [ledger EXCEPT ![n][h] = [hash |-> h, acct |-> PK(k), prev |-> lastHash, kind |-> "change", target |-> "none", amount |-> 0]]
              /\ received' = [received EXCEPT ![n] = @ \cup { [hash |-> h, acct |-> PK(k), prev |-> lastHash, kind |-> "change", target |-> "none", amount |-> 0] }]
    /\ UNCHANGED <<>>

ValidateBlock ==
    \E n \in Node, blk \in received[n] :
         /\ \A k \in Node : blk \notin received[k]
         /\ ledger' = [ledger EXCEPT ![n] = @ [blk.hash |-> blk]]
         /\ received' = [received EXCEPT ![n] = @]
         /\ UNCHANGED <<lastHash>>

Next ==
    \/ CreateGenesisBlock \/ CreateSendBlock \/ CreateOpenBlock
    \/ CreateReceiveBlock \/ CreateChangeRepresentative \/ ValidateBlock

Spec == Init /\ [][Next]_vars

====