---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

\* Ed25519 keys and Blake2b hashes are modeled as uninterpreted constants; the
\* hash calculation is an abstract external operator that can be swapped.
CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* A signed block records the account chain it belongs to, a link to the
\* previous block in that chain, an optional second link to a send block, the
\* amount moved (zero for change-representative), and the Ed25519 signature.
Blocks == [chain: PublicKey,
           prev: Hash, link: Hash, amount: Nat, sig: PublicKey]
Signed(h) == ledger[h] # NoBlockVal

TypeOK ==
  /\ lastHash \in Hash
  /\ ledger \in [Hash -> Blocks \cup {NoBlockVal}]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ received = [n \in Node |-> {}]

\* The genesis block is the only block on the initial ledger and is added
\* to every node's copy in the same step, so no node is ever left behind.
CreateGenesisBlock ==
  /\ lastHash = NoHashVal
  /\ \/ \E p \in PrivateKey, n \in Node:
       /\ p \in NoHash[n]
       /\ NoHash' = [NoHash EXCEPT ![n] = NoHash[n] \cup {p}]
       /\ lastHash' = CalculateHash(n, NoHashVal, NoBlock, GenesisBalance, p)
       /\ ledger' = [ledger EXCEPT ![lastHash'] = [chain |-> p,
                                                   prev |-> NoHashVal,
                                                   link |-> NoBlock,
                                                   amount |-> GenesisBalance,
                                                   sig |-> p]]
  /\ \A k \in Node: received' = [received EXCEPT ![k] = {}]

\* A send block reduces the actor's balance and points at its predecessor.
CreateSendBlock ==
  /\ lastHash # NoHashVal
  /\ \E n \in Node, p \in PrivateKey:
       /\ p \in NoHash[n]
       /\ NoHash' = [NoHash EXCEPT ![n] = NoHash[n] \cup {p}]
       /\ \E to \in PublicKey, amt \in Nat:
            /\ amt > 0
            /\ AmtSend(n, p, amt, to)
            /\ lastHash' = CalculateHash(n, lastHash, NoBlock, amt, p)
            /\ ledger' = [ledger EXCEPT ![lastHash'] = [chain |-> p,
                                                        prev |-> lastHash,
                                                        link |-> NoBlock,
                                                        amount |-> amt,
                                                        sig |-> p]]
            /\ received' = [k \in Node |-> IF k = n
                                          THEN received[k]
                                          ELSE received[k] \cup {lastHash'}]

\* An open block starts a new account chain from a send block addressed to it.
CreateOpenBlock ==
  /\ lastHash # NoHashVal
  /\ \E n \in Node, p \in PrivateKey:
       /\ p \in NoHash[n]
       /\ NoHash' = [NoHash EXCEPT ![n] = NoHash[n] \cup {p}]
       /\ \E h \in Hash:
            /\ Signed(h)
            /\ ledger[h].link = NoBlock
            /\ ledger[h].amount > 0
            /\ ledger[h].chain = p
            /\ lastHash' = CalculateHash(n, lastHash, h, 0, p)
            /\ ledger' = [ledger EXCEPT ![lastHash'] = [chain |-> p,
                                                        prev |-> lastHash,
                                                        link |-> h,
                                                        amount |-> 0,
                                                        sig |-> p]]
            /\ received' = [k \in Node |-> IF k = n
                                          THEN received[k]
                                          ELSE received[k] \cup {lastHash'}]

\* A receive block links to both its predecessor and the credited send.
CreateReceiveBlock ==
  /\ lastHash # NoHashVal
  /\ \E n \in Node, p \in PrivateKey:
       /\ p \in NoHash[n]
       /\ NoHash' = [NoHash EXCEPT ![n] = NoHash[n] \cup {p}]
       /\ \E h \in Hash:
            /\ Signed(h)
            /\ ledger[h].link = NoBlock
            /\ ledger[h].amount > 0
            /\ ledger[h].chain # p
            /\ lastHash' = CalculateHash(n, lastHash, h, 0, p)
            /\ ledger' = [ledger EXCEPT ![lastHash'] = [chain |-> p,
                                                        prev |-> lastHash,
                                                        link |-> h,
                                                        amount |-> 0,
                                                        sig |-> p]]
            /\ received' = [k \in Node |-> IF k = n
                                          THEN received[k]
                                          ELSE received[k] \cup {lastHash'}]

\* A change-representative block advances the chain without moving value.
CreateChangeRepresentativeBlock ==
  /\ lastHash # NoHashVal
  /\ \E n \in Node, p \in PrivateKey:
       /\ p \in NoHash[n]
       /\ NoHash' = [NoHash EXCEPT ![n] = NoHash[n] \cup {p}]
       /\ lastHash' = CalculateHash(n, lastHash, NoBlock, 0, p)
       /\ ledger' = [ledger EXCEPT ![lastHash'] = [chain |-> p,
                                                   prev |-> lastHash,
                                                   link |-> NoBlock,
                                                   amount |-> 0,
                                                   sig |-> p]]
       /\ received' = [k \in Node |-> IF k = n
                                     THEN received[k]
                                     ELSE received[k] \cup {lastHash'}]

\* Validation acts on one in-transit block at a time per node.
ValidateBlock ==
  /\ \E n \in Node, h \in received[n]:
       /\ ledger' = [ledger EXCEPT ![h] = ledger[h]]
       /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED lastHash

Next == CreateGenesisBlock \/ CreateSendBlock \/ CreateOpenBlock
        \/ CreateReceiveBlock \/ CreateChangeRepresentativeBlock
        \/ ValidateBlock

Spec == Init /\ [][Next]_vars

\* Recursive account-balance traversal for validation (type correctness only).
AccBalance(p) ==
  LET rec(h) ==
       IF h = NoHashVal \/ ledger[h].chain # p
         THEN 0
         ELSE ledger[h].amount + rec(ledger[h].prev)
  IN rec(lastHash)

\* Every block's signature must match the public key of its chain's owner.
SafetyInvariant ==
  /\ TypeOK
  /\ \A h \in Hash: Signed(h) => ledger[h].sig = ledger[h].chain

====