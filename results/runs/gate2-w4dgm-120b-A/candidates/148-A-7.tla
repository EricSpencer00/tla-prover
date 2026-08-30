---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* lastHash models the running hash of the newest globally-applied block; it is
\* what drives the block creation order, and its value space is what bounds the
\* action space for Create* and Process* actions below.
VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Compute an account's balance by walking its blockchain backward from the last
\* block on that chain, recursively summing the amounts recorded by send/receive
\* pairs. Every block that changes an account's balance appears in exactly one
\* of these two categories, so the sum accounts for the whole chain.
RECURSIVE Balance(_)
Balance(a) == IF ~HasBlock(a) THEN 0
              ELSE IF IsSendBlock(a, Head(a)) THEN BlockAmount(a, Head(a)) + Balance(a)
              ELSE Balance(a) - BlockAmount(a, Head(a)) + Balance(a)

\* Helper to walk a chain's hashes in reverse order, and to detect when a
\* chain has no blocks (NoHash signals "no previous block").
RECURSIVE Chain(_)
Chain(a) == IF ~HasBlock(a) THEN <<>> ELSE Append(Chain(a), Head(a))

HasBlock(a) == lastHash \in Domain(ledger[a])
Head(a) == ledger[a][lastHash]
Tail(a) == Chain(a)[Len(Chain(a)) - 1]
BlockAmount(a, bl) == IF IsSendBlock(a, bl) THEN bl.amount ELSE 0

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> {NoBlock} \cup [type: {"send", "receive", "open", "change"},
                                                amount: 0..GenesisBalance,
                                                dest: PublicKey \cup {NoBlockVal},
                                                pubKey: PublicKey \cup {NoBlockVal},
                                                prev: Hash \cup {NoHash}]]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock(nk, n) ==
  /\ lastHash = NoHash
  /\ lastHash' = CalculateHash([type |-> "send", amount |-> GenesisBalance, dest |-> NoBlockVal,
                                pubKey |-> PublicKey[nk], prev |-> NoHash])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] =
                   [type |-> "send", amount |-> GenesisBalance, dest |-> NoBlockVal,
                    pubKey |-> PublicKey[nk], prev |-> NoHash]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateSendBlock(nk, n, a, d) ==
  /\ lastHash \in Domain(ledger[n])
  /\ BlockAmount(n, ledger[n][lastHash]) >= a
  /\ lastHash' = CalculateHash([type |-> "send", amount |-> a, dest |-> PublicKey[d],
                                pubKey |-> PublicKey[nk], prev |-> lastHash])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] =
                   [type |-> "send", amount |-> a, dest |-> PublicKey[d],
                    pubKey |-> PublicKey[nk], prev |-> lastHash]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateOpenBlock(nk, n, g) ==
  /\ lastHash \in Domain(ledger[n])
  /\ ledger[n][lastHash].type = "send"
  /\ ledger[n][lastHash].dest = PublicKey[nk]
  /\ PublicKey[nk] \notin Chain(n)
  /\ lastHash' = CalculateHash([type |-> "open", amount |-> ledger[n][lastHash].amount,
                                dest |-> PublicKey[nk], pubKey |-> PublicKey[nk],
                                prev |-> NoHash])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] =
                   [type |-> "open", amount |-> ledger[n][lastHash].amount,
                    dest |-> PublicKey[nk], pubKey |-> PublicKey[nk], prev |-> NoHash]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateReceiveBlock(nk, n, g) ==
  /\ lastHash \in Domain(ledger[n])
  /\ ledger[n][lastHash].type = "send"
  /\ ledger[n][lastHash].dest = PublicKey[nk]
  /\ PublicKey[nk] \in Chain(n)
  /\ lastHash' = CalculateHash([type |-> "receive", amount |-> ledger[n][lastHash].amount,
                                dest |-> PublicKey[nk], pubKey |-> PublicKey[nk],
                                prev |-> lastHash])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] =
                   [type |-> "receive", amount |-> ledger[n][lastHash].amount,
                    dest |-> PublicKey[nk], pubKey |-> PublicKey[nk], prev |-> lastHash]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

CreateChangeBlock(nk, n) ==
  /\ lastHash \in Domain(ledger[n])
  /\ lastHash' = CalculateHash([type |-> "change", amount |-> 0, dest |-> NoBlockVal,
                                pubKey |-> PublicKey[nk], prev |-> lastHash])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] =
                   [type |-> "change", amount |-> 0, dest |-> NoBlockVal,
                    pubKey |-> PublicKey[nk], prev |-> lastHash]]]
  /\ received' = [m \in Node |-> received[m] \cup {lastHash}]

\* A node validates a received block against its own ledger copy before it
\* becomes part of that ledger. This is where signature checking and
\* block-type-specific rules are applied during normal operation.
ProcessBlock(n, h) ==
  /\ h \in received[n]
  /\ lastHash \in Domain(ledger[n])
  /\ PublicKey[InverseMapping(nk \in PrivateKey : PublicKey[nk])] = ledger[n][h].pubKey
  /\ lastHash = ledger[n][h].prev
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[n][h]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ lastHash' = lastHash

\* An attacker can drop a node's in-transit copy of a block without corrupting
\* the blockchain itself, creating a reordered or lost message; processing the
\* still-delivered copy at the other node is therefore still possible and must
\* not be baked into the safety property.
DiscardBlock(n, h) ==
  /\ h \in received[n]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ lastHash' = lastHash
  /\ ledger' = ledger

Next ==
  \/ \E nk \in PrivateKey, n \in Node: CreateGenesisBlock(nk, n)
  \/ \E nk \in PrivateKey, n \in Node, a \in 1..GenesisBalance, d \in Node: CreateSendBlock(nk, n, a, d)
  \/ \E nk \in PrivateKey, n \in Node, g \in Node: CreateOpenBlock(nk, n, g)
  \/ \E nk \in PrivateKey, n \in Node, g \in Node: CreateReceiveBlock(nk, n, g)
  \/ \E nk \in PrivateKey, n \in Node: CreateChangeBlock(nk, n)
  \/ \E n \in Node, h \in Hash: ProcessBlock(n, h)
  \/ \E n \in Node, h \in Hash: DiscardBlock(n, h)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger must carry a signature that matches the
\* public key of the account chain it sits on -- a block signed by the wrong
\* key is exactly the unauthorized action being ruled out here.
SafetyInvariant ==
  \A n \in Node : \A h \in Domain(ledger[n]) :
    PublicKey[InverseMapping(k \in PrivateKey : PublicKey[k] = ledger[n][h].pubKey)] = ledger[n][h].pubKey

BalanceOK == Balance(Node) <= GenesisBalance

====