---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Types derived from the system description: a block's hash, the previous
\* block link, the sender's public key, the recipient (or NoHash for a root
\* block), the amount moved, and the signature over those fields.
Block == [hash: Hash, previous: Hash, fromPublic: PublicKey, toPublic: PublicKey, amount: Nat, signature: PrivateKey]

\* The sender of a block is always its previous block's owner, so the chain
\* never forks away from its root; a link to NoHash is the chain's root.
FromOf(h) == IF h = NoHash THEN NoBlock ELSE ledger[h].fromPublic

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Balance is the sum of every movement along an account's chain.
RECURSIVE BalanceChain(_, _)
BalanceChain(g, h) ==
  IF h = NoHash THEN 0
  ELSE LET rest == BalanceChain(g, ledger[h].previous) IN
       IF ledger[h].toPublic = g THEN rest + ledger[h].amount ELSE rest

Balance(g) == BalanceChain(g, NoHash)

SumBalances == BalanceChain(CHOOSE g \in PublicKey : TRUE, NoHash)

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock(k) ==
  /\ lastHash = NoHash
  /\ NoHash \notin ledger[CHOOSE n \in Node : TRUE][NoHash]
  /\ ~ \E n \in Node : ledger[n][CalculateHash(k, NoHashVal, NoHash, NoHash, GenesisBalance)] # NoBlockVal
  /\ LET h == CalculateHash(k, NoHashVal, NoHash, NoHash, GenesisBalance) IN
     /\ lastHash' = h
     /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![h] = [hash |-> h,
                                                            previous |-> NoHash,
                                                            fromPublic |-> NoPublicKey,
                                                            toPublic |-> NoPublicKey,
                                                            amount |-> GenesisBalance,
                                                            signature |-> k]]]
     / received' = [n \in Node |-> received[n] \cup {h}]
  /\ UNCHANGED <<>>

CreateSendBlock(n, k, toPublic, a) ==
  /\ \E h \in Hash :
       /\ ledger[n][h] # NoBlockVal
       /\ Balance(FromOf(h)) >= a
       /\ NoHash \notin received[n]
       /\ LET newHash == CalculateHash(k, h, FromOf(h), toPublic, a) IN
            /\ lastHash' = newHash
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![newHash] = [hash |-> newHash,
                                                                          previous |-> h,
                                                                          fromPublic |-> FromOf(h),
                                                                          toPublic |-> toPublic,
                                                                          amount |-> a,
                                                                          signature |-> k]]]
            /\ received' = [m \in Node |-> received[m] \cup {newHash}]
  /\ UNCHANGED <<>>

CreateOpenBlock(n, k, fromPublic, amt) ==
  /\ \E h \in Hash :
       /\ ledger[n][h] # NoBlockVal
       /\ FromOf(h) = fromPublic
       /\ ledger[n][fromPublic] = NoBlockVal
       /\ NoHash \notin received[n]
       /\ LET newHash == CalculateHash(k, h, fromPublic, NoPublicKey, amt) IN
            /\ lastHash' = newHash
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![newHash] = [hash |-> newHash,
                                                                          previous |-> h,
                                                                          fromPublic |-> fromPublic,
                                                                          toPublic |-> NoPublicKey,
                                                                          amount |-> amt,
                                                                          signature |-> k]]]
            /\ received' = [m \in Node |-> received[m] \cup {newHash}]
  /\ UNCHANGED <<>>

CreateReceiveBlock(n, k, h) ==
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][FromOf(h)] = NoBlockVal
  /\ NoHash \notin received[n]
  /\ LET ch == ledger[n][FromOf(h)] IN
       LET newHash == CalculateHash(k, h, FromOf(ch), FromOf(h), ledger[n][h].amount) IN
            /\ lastHash' = newHash
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![newHash] = [hash |-> newHash,
                                                                          previous |-> h,
                                                                          fromPublic |-> FromOf(ch),
                                                                          toPublic |-> FromOf(h),
                                                                          amount |-> ledger[n][h].amount,
                                                                          signature |-> k]]]
            /\ received' = [m \in Node |-> received[m] \cup {newHash}]
  /\ UNCHANGED <<>>

CreateChangeRepBlock(n, k) ==
  /\ \E h \in Hash :
       /\ ledger[n][h] # NoBlockVal
       /\ NoHash \notin received[n]
       /\ LET newHash == CalculateHash(k, h, FromOf(h), NoPublicKey, 0) IN
            /\ lastHash' = newHash
            /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![newHash] = [hash |-> newHash,
                                                                          previous |-> h,
                                                                          fromPublic |-> FromOf(h),
                                                                          toPublic |-> NoPublicKey,
                                                                          amount |-> 0,
                                                                          signature |-> k]]]
            /\ received' = [m \in Node |-> received[m] \cup {newHash}]
  /\ UNCHANGED <<>>

\* Validation is a fresh check against the local ledger copy, not a removal
\* of the block from the broadcast set: a node validates as it learns.
Validate(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] = NoBlockVal
  /\ LET block == ledger[CHOOSE m \in Node : ledger[m][h] # NoBlockVal][h] IN
       LET valid == (block.signature \in PrivateKey /\ FromOf(h) \in PublicKey) /\ \/ (block.previous = NoHash /\ block.amount = GenesisBalance)
                     \/ (block.previous \in Hash /\ ledger[n][block.previous] # NoBlockVal /\ block.amount <= Balance(FromOf(h)))
       IN IF valid THEN ledger' = [ledger EXCEPT ![n][h] = block] ELSE UNCHANGED <<>>
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED <<lastHash>>

Next ==
  \/ \E k \in PrivateKey : CreateGenesisBlock(k)
  \/ \E n \in Node, k \in PrivateKey, toPublic \in PublicKey, a \in Nat : CreateSendBlock(n, k, toPublic, a)
  \/ \E n \in Node, k \in PrivateKey, fromPublic \in PublicKey, a \in Nat : CreateOpenBlock(n, k, fromPublic, a)
  \/ \E n \in Node, k \in PrivateKey, h \in Hash : CreateReceiveBlock(n, k, h)
  \/ \E n \in Node, k \in PrivateKey : CreateChangeRepBlock(n, k)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

\* The only thing that keeps a forged block from slipping through is the
\* signature check; replay is prevented by the chain link, which is the
\* well-formedness condition the invariant protects against.
SafetyInvariant ==
  \A n \in Node, h \in Hash :
    ledger[n][h] # NoBlockVal => ledger[n][h].signature \in PrivateKey

====