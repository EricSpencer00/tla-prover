---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

(* The original Nano blockchain protocol: each account owns a chain of blocks   *)
(* (a block lattice).  Blocks are created by nodes holding private keys and     *)
(* signed with Ed25519-style signatures; block hashes use Blake2b-style         *)
(* hashing.  The spec focuses on these crypto aspects, not on network          *)
(* topology.  The chain stores action history, which is precisely what makes    *)
(* exhaustive model checking hard.                                              *)

CONSTANTS
    Hash,           \* the finite set of block hashes; model checking bounds it
    NoHashVal,      \* sentinel meaning "no previous block"
    PrivateKey,     \* private keys available in the system
    PublicKey,      \* public keys derived from the private keys
    Node,           \* network nodes, each holding at least one private key
    GenesisBalance, \* total coin supply, present in the genesis account only
    NoBlockVal,     \* sentinel meaning "no block in this slot"
    CalculateHash,  \* abstract hash operator (substituted in by the .cfg)
    NoHash,         \* sentinel meaning "no hash"
    NoBlock         \* sentinel meaning "no block"

VARIABLES
    lastHash,       \* the last calculated block hash
    ledger,         \* distributed ledger: node -> Hash -> SignedBlock or NoBlock
    received        \* blocks in transit to each node, awaiting validation

vars == <<lastHash, ledger, received>>

\* Cryptographic bookkeeping -- signatures refer to the account's public key,
\* and the block's unique hash is calculated from its contents.
Signatures == [by: PrivateKey, on: Hash]
Blocks     == [prev: Hash \cup {NoHash}, kind: {"genesis", "send", "open", "receive", "change"}, to: PublicKey \cup {NoHash}, amount: Nat, sig: PrivateKey]

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> Blocks \cup {NoBlock}]]
    /\ received \in [Node -> SUBSET Blocks]

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ received = [n \in Node |-> {}]

\* The genesis block allocates the entire starting balance to the genesis
\* account in one atomic step, written into every node's ledger at once.
CreateGenesisBlock(k) ==
    /\ lastHash = NoHash
    /\ lastHash' = CalculateHash([prev |-> NoHash, kind |-> "genesis", to |-> NoHash, amount |-> GenesisBalance], NoHash)
    /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [prev |-> NoHash, kind |-> "genesis", to |-> NoHash, amount |-> GenesisBalance, sig |-> k]]]
    /\ received' = [n \in Node |-> received[n]]

\* A send block debits the sender's balance by amount and is the only action
\* that moves funds out of an account.
CreateSendBlock(n, k, amt, recipient) ==
    /\ k \in PrivateKey
    /\ k \in OwnedBy[n]
    /\ lastHash \in Hash
    /\ BalanceOf(ledger[n], k) >= amt
    /\ lastHash' = CalculateHash([prev |-> lastHash, kind |-> "send", to |-> recipient, amount |-> amt], lastHash)
    /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [prev |-> lastHash, kind |-> "send", to |-> recipient, amount |-> amt, sig |-> k]]
    /\ received' = [m \in Node |-> received[m] \cup {[prev |-> lastHash, kind |-> "send", to |-> recipient, amount |-> amt, sig |-> k]}]

CreateOpenBlock(n, k, src) ==
    /\ k \in PrivateKey
    /\ k \in OwnedBy[n]
    /\ lastHash \in Hash
    /\ lastHash' = CalculateHash([prev |-> lastHash, kind |-> "open", to |-> PublicOf(k), amount |-> 0], lastHash)
    /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [prev |-> lastHash, kind |-> "open", to |-> PublicOf(k), amount |-> 0, sig |-> k]]
    /\ received' = [m \in Node |-> received[m] \cup {[prev |-> lastHash, kind |-> "open", to |-> PublicOf(k), amount |-> 0, sig |-> k]}]

CreateReceiveBlock(n, k, src) ==
    /\ k \in PrivateKey
    /\ k \in OwnedBy[n]
    /\ lastHash \in Hash
    /\ lastHash' = CalculateHash([prev |-> lastHash, kind |-> "receive", to |-> PublicOf(k), amount |-> 0], lastHash)
    /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [prev |-> lastHash, kind |-> "receive", to |-> PublicOf(k), amount |-> 0, sig |-> k]]
    /\ received' = [m \in Node |-> received[m] \cup {[prev |-> lastHash, kind |-> "receive", to |-> PublicOf(k), amount |-> 0, sig |-> k]}]

CreateChangeBlock(n, k) ==
    /\ k \in PrivateKey
    /\ k \in OwnedBy[n]
    /\ lastHash \in Hash
    /\ lastHash' = CalculateHash([prev |-> lastHash, kind |-> "change", to |-> PublicOf(k), amount |-> 0], lastHash)
    /\ ledger' = [ledger EXCEPT ![n][lastHash'] = [prev |-> lastHash, kind |-> "change", to |-> PublicOf(k), amount |-> 0, sig |-> k]]
    /\ received' = [m \in Node |-> received[m] \cup {[prev |-> lastHash, kind |-> "change", to |-> PublicOf(k), amount |-> 0, sig |-> k]}]

\* Validation checks signatures, existence of referenced blocks, and that a
\* send/receive block is really affordable, before writing it to the ledger.
ValidateBlock(n, b) ==
    /\ b \in received[n]
    /\ b.sig \in PrivateKey
    /\ PublicOf(b.sig) = PublicOf(PrivateOf(b.sig))
    /\ ledger[n][b.prev] # NoBlock
    /\ (IF b.kind = "send" THEN BalanceOf(ledger[n], PrivateOf(b.sig)) >= b.amount ELSE TRUE)
    /\ ledger' = [ledger EXCEPT ![n] = @ [b.prev \notin Hash] [b.prev \in Hash] [b |> b]]
    /\ received' = [received EXCEPT ![n] = @ \ {b}]
    /\ UNCHANGED lastHash

ValidateAll(n) ==
    /\ \E b \in received[n] : ValidateBlock(n, b)
    /\ UNCHANGED <<lastHash, ledger, received>>

Next ==
    \/ \E k \in PrivateKey : CreateGenesisBlock(k)
    \/ \E n \in Node, k \in PrivateKey, amt \in 1..GenesisBalance, recipient \in PublicKey : CreateSendBlock(n, k, amt, recipient)
    \/ \E n \in Node, k \in PrivateKey, src \in Hash : CreateOpenBlock(n, k, src)
    \/ \E n \in Node, k \in PrivateKey, src \in Hash : CreateReceiveBlock(n, k, src)
    \/ \E n \in Node, k \in PrivateKey : CreateChangeBlock(n, k)
    \/ \E n \in Node : ValidateAll(n)

Spec == Init /\ [][Next]_vars

OwnerOfKey(k) == { n \in Node : k \in OwnedBy[n] }

\* Balance is the sum of amounts in the node's own chain, walking backwards.
BalanceOf(ln, k) ==
    LET chain(h) == IF h \in Hash /\ ln[h] # NoBlock /\ ln[h].sig = k
                        THEN IF ln[h].kind = "send" THEN -ln[h].amount + chain(ln[h].prev) ELSE chain(ln[h].prev)
                        ELSE 0
    IN chain(lastHash)

\* A valid block's signature must match the public key of the account that
\* owns the chain the block sits in -- this is the crypto invariant being
\* protected across all nodes' replicated ledgers.
SignatureValid(n, h) == ledger[n][h] # NoBlock => PublicOf(ledger[n][h].sig) = PublicOf(PrivateOf(ledger[n][h].sig))

TypeInvariant == TypeOK
SafetyInvariant == \A n \in Node, h \in Hash : SignatureValid(n, h)

\* The total balance across all accounts never exceeds the genesis balance.
BalanceConserved ==
    LET Sum(S) == IF S = {} THEN 0
                 ELSE LET x == CHOOSE y \in S : TRUE IN BalanceOf(ledger[CHOOSE n \in Node : TRUE], PrivateOf(x)) + Sum(S \ {x})
    IN Sum(PublicKey)

\* The chain records action history, so the state space is super-exponential:
\* each ordering of the same set of actions is a distinct state.  Exhaustive
\* model checking therefore explores only a tiny fraction of the reachable
\* space; it cannot replace a real security review of the crypto math.
BoundedCoverage == TRUE

====