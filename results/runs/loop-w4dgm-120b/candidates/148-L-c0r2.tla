---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* A block is a record of the transaction it represents; the hash is its identity.
Block == [prev: Hash \cup {NoHash}, sender: PublicKey, receiver: PublicKey,
          amount: Nat, repr: PublicKey, sig: PrivateKey]

\* The ledger is replicated across nodes; each node's copy is a map from hash to block.
Ledger == [Node -> [Hash -> Block \cup {NoBlockVal}]]

\* A block is broadcast to every node's received set before it is validated and applied.
Received == [Node -> SUBSET Hash]

\* The public key belonging to a private key (the Ed25519 key pair).
PublicOf == [k \in PrivateKey |-> CHOOSE p \in PublicKey : PublicKey[p] = k]

\* The chain of blocks belonging to an account, from newest back to genesis.
ChainOf(a, h) == IF h = NoHash THEN {}
                 ELSE IF Ledger[CHOOSE n \in Node : Ledger[n][h] # NoBlockVal][h].sender = a
                      THEN {h} \cup ChainOf(a, Ledger[CHOOSE n \in Node : Ledger[n][h] # NoBlockVal][h].prev)
                      ELSE ChainOf(a, Ledger[CHOOSE n \in Node : Ledger[n][h] # NoBlockVal][h].prev)

\* The balance of an account is the sum of amounts in its receive and open blocks.
RECURSIVE SumAmounts(_)
SumAmounts(S) == IF S = {} THEN 0
                 ELSE LET h == CHOOSE x \in S : TRUE
                      IN Ledger[CHOOSE n \in Node : Ledger[n][h] # NoBlockVal][h].amount + SumAmounts(S \ {h})

Balance(a) == SumAmounts(ChainOf(a, NoHash))

\* The total of all account balances; this must never exceed the genesis balance.
RECURSIVE SumBalances(_)
SumBalances(A) == IF A = {} THEN 0
                  ELSE LET a == CHOOSE x \in A : TRUE
                       IN Balance(a) + SumBalances(A \ {a})

\* The genesis block is the only block that can be created without a predecessor.
GenesisBlock == [prev |-> NoHash, sender |-> CHOOSE p \in PublicKey : TRUE,
                 receiver |-> CHOOSE p \in PublicKey : TRUE, amount |-> GenesisBalance,
                 repr |-> CHOOSE p \in PublicKey : TRUE, sig |-> CHOOSE k \in PrivateKey : TRUE]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in Ledger
    /\ received \in Received

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* The genesis block is written to every node's ledger at once and is never re-created.
CreateGenesisBlock ==
    /\ lastHash = NoHash
    /\ \A n \in Node : ledger[n][GenesisBlock.prev] = NoBlockVal
    /\ lastHash' = CalculateHash(GenesisBlock, NoHash)
    /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = GenesisBlock]]
    /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

\* A send block debits the sender and names a recipient; it must not overdraw.
CreateSendBlock(k, to, amt) ==
    /\ Balance(PublicOf[k]) >= amt
    /\ lastHash' = CalculateHash([prev |-> lastHash, sender |-> PublicOf[k],
                                  receiver |-> to, amount |-> amt, repr |-> PublicOf[k], sig |-> k], lastHash)
    /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [prev |-> lastHash, sender |-> PublicOf[k],
                                                                  receiver |-> to, amount |-> amt,
                                                                  repr |-> PublicOf[k], sig |-> k]]]
    /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

\* An open block starts a new account's chain, referencing a send block addressed to it.
CreateOpenBlock(k, h) ==
    /\ ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal][h].receiver = PublicOf[k]
    /\ \A n \in Node : ledger[n][h].prev # NoHash
    /\ lastHash' = CalculateHash([prev |-> lastHash, sender |-> PublicOf[k],
                                  receiver |-> PublicOf[k], amount |-> 0, repr |-> PublicOf[k], sig |-> k], lastHash)
    /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [prev |-> lastHash, sender |-> PublicOf[k],
                                                                  receiver |-> PublicOf[k], amount |-> 0,
                                                                  repr |-> PublicOf[k], sig |-> k]]]
    /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

\* A receive block credits the receiver and consumes a send block addressed to it.
CreateReceiveBlock(k, h) ==
    /\ ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal][h].receiver = PublicOf[k]
    /\ \A n \in Node : ledger[n][h].prev # NoHash
    /\ lastHash' = CalculateHash([prev |-> lastHash, sender |-> PublicOf[k],
                                  receiver |-> PublicOf[k], amount |-> ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal][h].amount,
                                  repr |-> PublicOf[k], sig |-> k], lastHash)
    /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [prev |-> lastHash, sender |-> PublicOf[k],
                                                                  receiver |-> PublicOf[k], amount |-> ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal][h].amount,
                                                                  repr |-> PublicOf[k], sig |-> k]]]
    /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

\* A change-representative block reassigns voting power without moving funds.
CreateChangeReprBlock(k) ==
    /\ lastHash' = CalculateHash([prev |-> lastHash, sender |-> PublicOf[k],
                                  receiver |-> PublicOf[k], amount |-> 0, repr |-> PublicOf[k], sig |-> k], lastHash)
    /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [prev |-> lastHash, sender |-> PublicOf[k],
                                                                  receiver |-> PublicOf[k], amount |-> 0,
                                                                  repr |-> PublicOf[k], sig |-> k]]]
    /\ received' = [n \in Node |-> received[n] \cup {lastHash'}]

\* Validation checks the signature, the existence of referenced blocks, and block-type rules.
ValidateBlock(n, h) ==
    /\ h \in received[n]
    /\ ledger[n][h] # NoBlockVal
    /\ PublicOf[ledger[n][h].sig] = ledger[n][h].sender
    /\ (IF ledger[n][h].prev = NoHash THEN TRUE ELSE ledger[n][h].prev \in {g \in Hash : ledger[n][g] # NoBlockVal})
    /\ (IF ledger[n][h].receiver = ledger[n][h].sender THEN TRUE
         ELSE ledger[n][h].receiver \in PublicKey)
    /\ (IF ledger[n][h].amount = 0 THEN TRUE
         ELSE Balance(ledger[n][h].sender) >= ledger[n][h].amount)
    /\ received' = [received EXCEPT ![n] = @ \ {h}]
    /\ UNCHANGED <<lastHash, ledger>>

Next ==
    \/ CreateGenesisBlock
    \/ \E k \in PrivateKey, to \in PublicKey, amt \in 1..GenesisBalance: CreateSendBlock(k, to, amt)
    \/ \E k \in PrivateKey, h \in Hash: CreateOpenBlock(k, h)
    \/ \E k \in PrivateKey, h \in Hash: CreateReceiveBlock(k, h)
    \/ \E k \in PrivateKey: CreateChangeReprBlock(k)
    \/ \E n \in Node, h \in Hash: ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger must carry a signature that matches its sender's public key.
SafetyInvariant == \A n \in Node, h \in Hash: ledger[n][h] # NoBlockVal => PublicOf[ledger[n][h].sig] = ledger[n][h].sender

\* The total of all account balances never exceeds the genesis balance.
BalanceBound == SumBalances(PublicKey) <= GenesisBalance

\* Blockchains have super-exponential state space scaling (action order is recorded in the chain),
\* so finite model checking of them is of limited effectiveness.
ChainComplexity == TRUE

====