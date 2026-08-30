---- MODULE Nano ----
EXTENDS Naturals, Sequences

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Model of the Nano block-lattice protocol (original version), with a focus
\* on hash functions and Ed25519-style signatures. The state is kept as a
\* replicated ledger (one copy per node) plus a per-node set of received
\* blocks waiting to be validated/added to the ledger.
\* Safety property: every ledger entry has a valid Ed25519 signature.
\* Liveness properties: none are defined for this protocol (it is never
\* stuck, and none are required by the assignment).

VARIABLES lastHash, ledger, received

\* Blocks are indexed by their (cryptographic) hash. NoHash is a special
\* marker meaning "this account has no previous block in its chain".
\* NoBlock is a sentinel for "no block has been recorded yet".
\* SendHash is the hash of the send block that the block at [h] is
\* replying to (empty for genesis, open and change-representative).
\* Amount is the value sent/received (zero for receive/open/change).
\* Signature is the Ed25519 signature over the block contents.
\* Owner is the account (public key) whose chain this block belongs to.
\* Sender is the account that originated the money this block is dealing
\* with (empty except for send blocks).
Block == [h : Hash, prev : Hash \cup {NoHash}, sendHash : Hash \cup {NoHash}, amount : Nat, signature : PublicKey, owner : PublicKey, sender : PublicKey]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Block]

\* Sum of all account balances (computed by walking each account's chain,
\* starting from the hash that account's chain begins at). The chain
\* contains every received block exactly once, so the per-account sums
\* add up to the total money held across the whole lattice.
RECURSIVE BalanceOf(_)
BalanceOf(ledger) ==
    LET accounts == PublicKey IN
    LET rec(a) == BalanceOfSeq(ledger, ChainHashes(ledger, a)) IN
    LET add[S \in SUBSET accounts] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in accounts : y \in S IN rec(x) + add(S \ {x})
    IN add(accounts)

RECURSIVE BalanceOfSeq(_)
BalanceOfSeq(seq) ==
    IF seq = <<>> THEN 0
    ELSE LET h == Head(seq) IN
         IF ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal][h].owner = Head(accounts)
            THEN seq[1].amount + BalanceOfSeq(Tail(seq))
            ELSE BalanceOfSeq(Tail(seq))

\* ChainHashes walks an account chain backward from a starting hash, then
\* returns the hashes in head-to-tail order (the order the money moved).
RECURSIVE ChainHashes(_)
ChainHashes(ledger, a) ==

RECURSIVE WalkChain(_)
WalkChain(h) ==
    IF h = NoHash THEN <<>>
    ELSE LET b == ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal][h] IN
         WalkChain(b.prev) \o <<b>>

ChainHashes(ledger, a) == WalkChain(a)

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

GenesisBlock(k) ==
  /\ lastHash = NoHash
  /\ lastHash' = CalculateHash([prev |-> NoHash, amount |-> GenesisBalance, owner |-> k])
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash] = [h |-> lastHash, prev |-> NoHash, sendHash |-> NoHash, amount |-> GenesisBalance, signature |-> k, owner |-> k, sender |-> NoHash]]]
  /\ received' = [n \in Node |-> [m \in Node |-> IF m # n THEN {[h |-> lastHash, prev |-> NoHash, sendHash |-> NoHash, amount |-> GenesisBalance, signature |-> k, owner |-> k, sender |-> NoHash]} ELSE {}]]

SendBlock(n, a, amt, k) ==
  /\ ledger[n][a] # NoBlockVal
  /\ a # NoHash
  /\ amt \in 1..BalanceOf(ledger, a)
  /\ lastHash' = CalculateHash([prev |-> a, amount |-> amt, owner |-> k])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [h |-> lastHash, prev |-> a, sendHash |-> NoHash, amount |-> amt, signature |-> k, owner |-> k, sender |-> k]]]
  /\ received' = [m \in Node |-> [x \in Node |->
                     IF x = n THEN received[x] \cup {[h |-> lastHash, prev |-> a, sendHash |-> NoHash, amount |-> amt, signature |-> k, owner |-> k, sender |-> k]}
                     ELSE received[x]]]

OpenBlock(n, a, s, k) ==
  /\ ledger[n][a] # NoBlockVal
  /\ a # NoHash
  /\ lastHash' = CalculateHash([prev |-> a, amount |-> 0, owner |-> k])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [h |-> lastHash, prev |-> a, sendHash |-> s, amount |-> 0, signature |-> k, owner |-> k, sender |-> k]]]
  /\ received' = [m \in Node |-> [x \in Node |->
                     IF x = n THEN received[x] \cup {[h |-> lastHash, prev |-> a, sendHash |-> s, amount |-> 0, signature |-> k, owner |-> k, sender |-> k]}
                     ELSE received[x]]]

ReceiveBlock(n, a, s, k) ==
  /\ s # NoHash
  /\ ledger[n][s] # NoBlockVal
  /\ ledger[n][s].owner = k
  /\ ledger[n][a] # NoBlockVal
  /\ a # NoHash
  /\ lastHash' = CalculateHash([prev |-> a, amount |-> ledger[n][s].amount, owner |-> k])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [h |-> lastHash, prev |-> a, sendHash |-> s, amount |-> ledger[n][s].amount, signature |-> k, owner |-> k, sender |-> k]]]
  /\ received' = [m \in Node |-> [x \in Node |->
                     IF x = n THEN received[x] \cup {[h |-> lastHash, prev |-> a, sendHash |-> s, amount |-> ledger[n][s].amount, signature |-> k, owner |-> k, sender |-> k]}
                     ELSE received[x]]]

ChangeRepBlock(n, a, k) ==
  /\ ledger[n][a] # NoBlockVal
  /\ a # NoHash
  /\ lastHash' = CalculateHash([prev |-> a, amount |-> 0, owner |-> k])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] = [h |-> lastHash, prev |-> a, sendHash |-> NoHash, amount |-> 0, signature |-> k, owner |-> k, sender |-> k]]]
  /\ received' = [m \in Node |-> [x \in Node |->
                     IF x = n THEN received[x] \cup {[h |-> lastHash, prev |-> a, sendHash |-> NoHash, amount |-> 0, signature |-> k, owner |-> k, sender |-> k]}
                     ELSE received[x]]]

ProcessBlock(n, b) ==
  /\ b \in received[n]
  /\ ledger[n][b.h] = NoBlockVal
  /\ b.signature = b.owner
  /\ b.owner \in PublicKey
  /\ \E a \in PrivateKey : PublicKey[a] = b.owner
  /\ b.prev \in Hash \cup {NoHash}
  /\ IF b.prev = NoHash THEN b.h = CalculateHash([prev |-> NoHash, amount |-> b.amount, owner |-> b.owner])
     ELSE ledger[n][b.prev] # NoBlockVal /\ b.h = CalculateHash([prev |-> b.prev, amount |-> b.amount, owner |-> b.owner])
  /\ IF b.sendHash \in Hash THEN ledger[n][b.sendHash] # NoBlockVal /\ ledger[n][b.h].amount = b.amount
     ELSE b.sendHash = NoHash
  /\ ledger' = [ledger EXCEPT ![n][b.h] = b]
  /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
  /\ lastHash' = lastHash

Next ==
  \/ \E k \in PrivateKey : GenesisBlock(k)
  \/ \E n \in Node, a \in Hash \cup {NoHash}, amt \in 1..GenesisBalance, k \in PrivateKey : SendBlock(n, a, amt, k)
  \/ \E n \in Node, a \in Hash \cup {NoHash}, s \in Hash \cup {NoHash}, k \in PrivateKey : OpenBlock(n, a, s, k)
  \/ \E n \in Node, a \in Hash \cup {NoHash}, s \in Hash \cup {NoHash}, k \in PrivateKey : ReceiveBlock(n, a, s, k)
  \/ \E n \in Node, a \in Hash \cup {NoHash}, k \in PrivateKey : ChangeRepBlock(n, a, k)
  \/ \E n \in Node, b \in Block : ProcessBlock(n, b)

Spec ==
  /\ Init
  /\ [][Next]_<<lastHash, ledger, received>>
  /\ WF_vars(\E k \in PrivateKey : GenesisBlock(k))

\* Safety: signatures are always valid in every node's ledger copy.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].signature = ledger[n][h].owner

\* Type checking of the entire state.
TypeInvariant == TypeOK

====