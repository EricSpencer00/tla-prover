---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Cryptographic primitives are abstracted as deterministic functions from
\* input data and the previous hash; this is what keeps the model finite.
HashFunction == [key: PrivateKey, prev: Hash, data: PUBLIC] ->
                    CalculateHash(key, prev, data)

\* Each account's balance is the sum of its chain's block amounts, in order.
RECURSIVE ChainBalance(_)
ChainBalance(s) == IF s = <<>> THEN 0 ELSE Head(s) + ChainBalance(Tail(s))

VARIABLES lastHash, ledger, received, privateKey

vars == <<lastHash, ledger, received, privateKey>>

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> NoBlockVal \cup [pubKey: PublicKey, data: PUBLIC, sig: PrivateKey]]]
    /\ received \in [Node -> SUBSET (Hash \X PUBLIC)]
    /\ privateKey \in [Node -> PrivateKey]

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]
    /\ privateKey = [n \in Node |-> CHOOSE k \in PrivateKey : TRUE]

\* A node is slow and drops a received block rather than confirming it.
DropSlow(n) == \E hb \in received[n] : received' = [received EXCEPT ![n] = @ \ {hb}]
    /\ UNCHANGED <<lastHash, ledger, privateKey>>

BuildChain(n) ==
    LET hlist ==
        SelectSeq([h \in Hash |-> IF ledger[n][h] # NoBlock
                                 THEN h ELSE NoHashVal],
                  [i \in 1..Cardinality(Hash) |-> i])
    IN ChainBalance(hlist)

\* A block is validated against the local ledger and the chain it extends.
ValidateBlock(n, h, pub, data, sig) ==
    /\ ledger[n][h] = NoBlock
    /\ sig = privateKey[n]
    /\ publicKey[sig] = pub
    /\ LET src == IF data.type = "send" THEN data.to ELSE pub
           bal == (IF src = pub THEN 0 ELSE BuildChain(n))
       IN \/ data.type \in {"send", "open", "receive", "changeRep"}
          \/ (data.type = "send" => data.amount <= bal)
          \/ (data.type = "open" => \E m \in Node : ledger[m][pub] # NoBlock)
    /\ ledger' = [ledger EXCEPT ![n][h] = [pubKey |-> pub, data |-> data, sig |-> sig]]
    /\ received' = [received EXCEPT ![n] = @ \ {<<h, data>>}]
    /\ UNCHANGED <<lastHash, privateKey>>

Broadcast(h, data) ==
    /\ received' = [n \in Node |-> received[n] \cup {<<h, data>>}]
    /\ UNCHANGED <<lastHash, ledger, privateKey>>

\* The genesis block also sets the first replica's whole ledger.
CreateGenesis(n) ==
    /\ lastHash = NoHash
    /\ LET h == HashFunction[@][key |-> privateKey[n], prev |-> NoHash, data |-> [type |-> "genesis", amount |-> GenesisBalance]]
       IN /\ lastHash' = h
          /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![h] = [pubKey |-> publicKey[privateKey[n]], data |-> [type |-> "genesis", amount |-> GenesisBalance], sig |-> privateKey[n]]]]
          /\ received' = [received EXCEPT ![n] = @ \ {<<h, [type |-> "genesis", amount |-> GenesisBalance]>>}]
    /\ UNCHANGED privateKey

CreateSend(n) ==
    /\ lastHash # NoHash
    /\ \E to \in Node, amt \in 1..GenesisBalance :
         /\ LET h == HashFunction[@][key |-> privateKey[n], prev |-> lastHash,
                                      data |-> [type |-> "send", to |-> publicKey[privateKey[to]], amount |-> amt]]
                in /\ lastHash' = h
                   /\ ledger' = [ledger EXCEPT ![n][h] = [pubKey |-> publicKey[privateKey[n]], data |-> [type |-> "send", to |-> publicKey[privateKey[to]], amount |-> amt], sig |-> privateKey[n]]]
                   /\ received' = [received EXCEPT ![to] = @ \ {<<h, [type |-> "send", to |-> publicKey[privateKey[to]], amount |-> amt]>>}]
    /\ UNCHANGED privateKey

CreateOpen(n) ==
    /\ lastHash # NoHash
    /\ \E h \in Hash :
         /\ ledger[n][h] = NoBlock
         /\ \E m \in Node :
              /\ ledger[m][h] # NoBlock
              /\ ledger[m][h].data.type = "send"
              /\ ledger[m][h].data.to = publicKey[privateKey[n]]
         /\ LET nh == HashFunction[@][key |-> privateKey[n], prev |-> lastHash,
                                      data |-> [type |-> "open"]]
                in /\ lastHash' = nh
                   /\ ledger' = [ledger EXCEPT ![n][nh] = [pubKey |-> publicKey[privateKey[n]], data |-> [type |-> "open"], sig |-> privateKey[n]]]
                   /\ received' = [received EXCEPT ![n] = @ \ {<<nh, [type |-> "open"]>>}]
    /\ UNCHANGED privateKey

CreateReceive(n) ==
    /\ lastHash # NoHash
    /\ \E h \in Hash :
         /\ ledger[n][h] = NoBlock
         /\ \E m \in Node :
              /\ ledger[m][h] # NoBlock
              /\ ledger[m][h].data.type = "send"
              /\ ledger[m][h].data.to = publicKey[privateKey[n]]
         /\ LET nh == HashFunction[@][key |-> privateKey[n], prev |-> lastHash,
                                      data |-> [type |-> "receive", from |-> ledger[m][h].pubKey, amount |-> ledger[m][h].data.amount]]
                in /\ lastHash' = nh
                   /\ ledger' = [ledger EXCEPT ![n][nh] = [pubKey |-> publicKey[privateKey[n]], data |-> [type |-> "receive", from |-> ledger[m][h].pubKey, amount |-> ledger[m][h].data.amount], sig |-> privateKey[n]]]
                   /\ received' = [received EXCEPT ![n] = @ \ {<<nh, [type |-> "receive", from |-> ledger[m][h].pubKey, amount |-> ledger[m][h].data.amount]>>}]
    /\ UNCHANGED privateKey

CreateChangeRep(n) ==
    /\ lastHash # NoHash
    /\ LET h == HashFunction[@][key |-> privateKey[n], prev |-> lastHash,
                                data |-> [type |-> "changeRep"]]
       IN /\ lastHash' = h
          /\ ledger' = [ledger EXCEPT ![n][h] = [pubKey |-> publicKey[privateKey[n]], data |-> [type |-> "changeRep"], sig |-> privateKey[n]]]
          /\ received' = [received EXCEPT ![n] = @ \ {<<h, [type |-> "changeRep"]>>}]
    /\ UNCHANGED privateKey

Next ==
    \/ \E n \in Node : DropSlow(n)
    \/ \E n \in Node, h \in Hash, pub \in PublicKey, data \in PUBLIC, sig \in PrivateKey :
         ValidateBlock(n, h, pub, data, sig)
    \/ \E h \in Hash, data \in PUBLIC : Broadcast(h, data)
    \/ \E n \in Node : CreateGenesis(n)
    \/ \E n \in Node : CreateSend(n)
    \/ \E n \in Node : CreateOpen(n)
    \/ \E n \in Node : CreateReceive(n)
    \/ \E n \in Node : CreateChangeRep(n)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger carries a valid signature from the
\* account it belongs to; no forged or corrupted block is ever recorded.
SafetyInvariant == \A n \in Node : \A h \in Hash :
    ledger[n][h] # NoBlock => publicKey[ledger[n][h].sig] = ledger[n][h].pubKey
====