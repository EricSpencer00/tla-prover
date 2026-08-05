---- MODULE Nano ----
EXTENDS Naturals, Bags

CONSTANTS
    Hash,
    CalculateHash(_,_,_),
    PrivateKey,
    PublicKey,
    KeyPair,
    Node,
    GenesisBalance,
    Ownership

VARIABLES lastHash, distributedLedger, received

ASSUME
    /\ \A data, oldHash, newHash : CalculateHash(data, oldHash, newHash) \in BOOLEAN
    /\ KeyPair \in [PrivateKey -> PublicKey]
    /\ GenesisBalance \in Nat
    /\ Ownership \in [Node -> PrivateKey]

Signature ==
    [data : Hash, signedWith : PrivateKey]

NoBlock == CHOOSE b \in [type : {"ignore"}, account : PublicKey, balance : 0..GenesisBalance,
                         previous : Hash, source : Hash, rep : PublicKey] : TRUE

NoHash == CHOOSE h \in Hash : TRUE

Ledger == [Hash -> [block : [type : {"ignore","genesis","open","send","receive","change"},
                             account : PublicKey, balance : 0..GenesisBalance,
                             previous : Hash, source : Hash, rep : PublicKey],
                  signature : Signature] \cup {NoBlock}]

BLOCKREC == [type : {"genesis","open","send","receive","change"},
             account : PublicKey, balance : 0..GenesisBalance,
             previous : Hash, source : Hash, rep : PublicKey]

SignHash(h, k) == [data |-> h, signedWith |-> k]

ValidateSignature(sig, expectedKey, expectedHash) ==
    LET publicKey == KeyPair[sig.signedWith] IN
    /\ publicKey = expectedKey
    /\ sig.data = expectedHash

RECURSIVE PublicKeyOf(_, _)
PublicKeyOf(led, h) ==
    LET block == led[h].block IN
    IF block.type \in {"genesis","open"}
    THEN block.account
    ELSE PublicKeyOf(led, block.previous)

AccountOpen(led, a) == \E h \in Hash : led[h].block.type \in {"genesis","open"}
                        /\ led[h].block.account = a

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> Ledger]
    /\ received \in [Node -> SUBSET [block : BLOCKREC, signature : Signature]]

ValidGenesis == \A node \in Node : AccountOpen(distributedLedger[node], PublicKey)

RECURSIVE BalanceAt(_, _)
ValueSent(_, _)
BalanceAt(led, h) ==
    LET block == led[h].block IN
    CASE block.type = "open" -> ValueSent(led, block.source)
    [] block.type = "send" -> block.balance
    [] block.type = "receive" ->
        BalanceAt(led, block.previous) + ValueSent(led, block.source)
    [] block.type = "change" -> BalanceAt(led, block.previous)
    [] block.type = "genesis" -> block.balance

ValueSent(led, h) ==
    LET block == led[h].block IN BalanceAt(led, block.previous) - block.balance

RECURSIVE SumBag(_)
SumBag(B) ==
    LET S == BagToSet(B) IN IF S = {} THEN 0 ELSE LET e \in S : e + SumBag(B \ {e})

BalanceConserved ==
    /\ ValidGenesis
    /\ \A node \in Node :
        LET led == distributedLedger[node]
            accounts == {a \in PublicKey : AccountOpen(led, a)}
            topBlocks == {CHOOSE h \in Hash :
                            led[h].block.account \in accounts
                            /\ (h = led[h].block.previous \/ led[h].block.type = "genesis")}
            bal == BagOfAll(BalanceAt(led), SetToBag(topBlocks))
            topBalances == {BalanceAt(led, h) : h \in topBlocks}
        IN SumBag(bal) <= GenesisBalance /\ \A a \in accounts : BalanceAt(led, a) \in topBalances)

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> [block |-> NoBlock, signature |-> SignHash(NoHash, CHOOSE k \in PrivateKey : TRUE)]]]
    /\ received = [n \in Node |-> {}]

CreateBlock(node) ==
    /\ \E rep \in PublicKey, src \in Hash :
        /\ (src = NoHash \/ distributedLedger[node][src].block.type = "send")
        /\ \E bal \in 0..GenesisBalance :
            LET blk == [type |-> "open", account |-> KeyPair[Ownership[node]],
                        balance |-> bal, previous |-> src, source |-> NoHash, rep |-> rep]
                hsh == CHOOSE h \in Hash : TRUE
            IN /\ \A h2 \in Hash : h2 # h => ~CalculateHash(blk, h2, h)
               /\ distributedLedger' = [distributedLedger EXCEPT ![node][h] =
                        [block |-> blk, signature |-> SignHash(h, Ownership[node])]]
               /\ lastHash' = h
    /\ UNCHANGED received

ProcessBlock ==
    /\ \E node \in Node, h \in Hash :
        /\ \E blk \in received[node] :
            LET ldr == distributedLedger[node] IN
            /\ ldr[h].block = NoBlock
            /\ \A h2 \in Hash : h2 # h => ~CalculateHash(blk.block, h2, h)
            /\ ValidateSignature(blk.signature, KeyPair[Ownership[node]], h)
            /\ distributedLedger' = [distributedLedger EXCEPT ![node][h] = blk]
            /\ received' = [received EXCEPT ![node] = @ \ {blk}]
            /\ lastHash' = h
    /\ UNCHANGED <<>>

Next == CreateBlock("n1") \/ ProcessBlock

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

=============================================================================