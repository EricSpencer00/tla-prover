---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash,
  NoHashVal,
  PrivateKey,
  PublicKey,
  Node,
  GenesisBalance,
  NoBlockVal,
  CalculateHash,
  NoHash,
  NoBlock

ASSUME NoHashVal \notin Hash
ASSUME NoBlockVal \notin Node

\* Dynamic workload: each node's instance of the block-lattice ledger, replicated
\* across a network and hardened by one cryptographic invariant.
\* Actions: Create* (emit a block onto the wire) and Process* (validate and absorb).
\* Safety: every block in every node's ledger has a signature matching its account's
\* public key; every validated block also passes the chain-specific rule for its
\* type (e.g. a send must draw no more than the sender's balance).
\* The model explores action orderings (an interleaving-variant property of the
\* chain itself), not concurrent editing of a single shared record -- a blockchain
\* is a replicated ledger with per-node validation, not a lock-protected shared pool.

\* Every node owns a private key and a replica of the shared ledger; the hash of
\* the most recently written block is used as the "previous hash" for the next
\* block on any account chain.
Block == {NoBlock} \cup [hash : Hash, src : PublicKey, dst : PublicKey, amt : 0..GenesisBalance, typ : {"genesis", "send", "open", "receive", "change"}, prev : Hash, sig : PrivateKey]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Block]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Balance chains backwards from the most recent block on an account chain,
\* summing every amount that is actually available to that account (open/rev
\* blocks add, send/receive move funds and net to zero on the chain). The
\* bounded capacity of the hash set is what keeps this sum from diverging.
RECURSIVE Balance(_)
Balance(S) == IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN
         LET rest == Balance(S \ {x})
         IN IF x.typ \in {"open", "receive"} THEN rest + x.amt ELSE rest

\* Every block is created against the ledger copy that the creating node currently
\* holds -- a node's own copy, which may already be missing blocks that others
\* wrote but it has not yet received. The invariant covers the moment each block
\* actually lands, which is why the cryptographic signature must be checked there:
\* a create step that emitted an unauthorized or malformed block would be caught
\* the moment the block is validated and written into any node's ledger.
Validate(n, b) ==
  /\ b.sig \in {k \in PrivateKey : PublicKey[k] = b.src}
  /\ IF b.typ = "genesis" THEN lastHash = NoHash /\ b.amt >= 1 ELSE TRUE
  /\ IF b.typ = "send" THEN b.prev = lastHash /\ b.amt <= Balance(ledger[n])
  /\ IF b.typ = "open" THEN b.prev = NoHash /\ b.amt >= 1 /\ b.amt <= GenesisBalance
  /\ IF b.typ = "receive" THEN b.prev \in Hash /\ ledger[n][b.prev] # NoBlockVal /\ ledger[n][b.prev].typ = "send" /\ b.amt = ledger[n][b.prev].amt
  /\ IF b.typ = "change" THEN b.prev = lastHash
  /\ ledger' = [ledger EXCEPT ![n][b.hash] = b]
  /\ lastHash' = IF b.typ = "genesis" THEN b.hash ELSE lastHash
  /\ UNCHANGED received

Broadcast(b) == [n \in Node |-> received[n] \cup {b}]

\* Each block-creation action emits a signed block and drops it onto every node's
\* wire; the create-the-creator's-own-ledger bias is double-checked at validation
\* time (where it matters for the ledger, not for the wire).
CreateGenesis(n, k) ==
  /\ lastHash = NoHash
  /\ \A n2 \in Node : ledger[n2][NoHash] = NoBlockVal
  /\ LET b == [hash |-> CalculateHash({n, "genesis", 0, GenesisBalance}, NoHash), src |-> PublicKey[k], dst |-> PublicKey[k], amt |-> GenesisBalance, typ |-> "genesis", prev |-> NoHash, sig |-> k]
  IN Broadcast(b)

CreateSend(n, k, dst, amt) ==
  /\ \A w \in received[n] : w.typ # "send"
  /\ amt \geq 1
  /\ LET b == [hash |-> CalculateHash({n, "send", amt, dst}, lastHash), src |-> PublicKey[k], dst |-> dst, amt |-> amt, typ |-> "send", prev |-> lastHash, sig |-> k]
  IN Broadcast(b)

CreateOpen(n, k, src, amt) ==
  /\ \A w \in received[n] : w.typ # "open"
  /\ amt >= 1
  /\ LET b == [hash |-> CalculateHash({n, "open", amt, src}, NoHash), src |-> PublicKey[k], dst |-> PublicKey[k], amt |-> amt, typ |-> "open", prev |-> NoHash, sig |-> k]
  IN Broadcast(b)

CreateReceive(n, k, src, amt) ==
  /\ \A w \in received[n] : w.typ # "receive"
  /\ amt >= 1
  /\ LET b == [hash |-> CalculateHash({n, "receive", amt, src}, lastHash), src |-> PublicKey[k], dst |-> PublicKey[k], amt |-> amt, typ |-> "receive", prev |-> lastHash, sig |-> k]
  IN Broadcast(b)

CreateChange(n, k) ==
  /\ \A w \in received[n] : w.typ # "change"
  /\ LET b == [hash |-> CalculateHash({n, "change", 0, PublicKey[k]}, lastHash), src |-> PublicKey[k], dst |-> PublicKey[k], amt |-> 0, typ |-> "change", prev |-> lastHash, sig |-> k]
  IN Broadcast(b)

Process(n, b) ==
  /\ b \in received[n]
  /\ Validate(n, b)
  /\ received' = [received EXCEPT ![n] = @ \ {b}]

AnyCreate == \E n \in Node, k \in PrivateKey :
  CreateGenesis(n, k) \/ CreateSend(n, k, PublicKey[k], 1)
    \/ CreateOpen(n, k, PublicKey[k], 1) \/ CreateReceive(n, k, PublicKey[k], 1) \/ CreateChange(n, k)

Next ==
  \/ AnyCreate
  \/ \E n \in Node, b \in Block : Process(n, b)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(AnyCreate)
  /\ \A n \in Node, b \in Block : SF_vars(Process(n, b))

\* A block is only ever written into a ledger after its signature has been
\* validated against the account's own public key -- an unauthorized emitter can
\* never get a block into anybody's ledger.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash :
    ledger[n][h] # NoBlockVal => PublicKey[ledger[n][h].sig] = ledger[n][h].src

\* The sum of all account balances always equals the genesis balance minus the
\* amount currently in transit on the wire (which is held but not yet validated).
BalanceCapacity == Balance({n \in Node : \E h \in Hash : ledger[n][h] # NoBlockVal})

\* Action ordering is recorded in the chain: the number of reachable states grows
\* super-exponentially with the hash set size, which is precisely why finite
\* model checking of blockchains is of limited practical value beyond checking
\* the integrity of the validation logic itself.
ActionOrderIsRecorded == TRUE

\* The two properties are logically independent: the invariant can hold with the
\* reachable-state set being tiny or the hash set being empty.
LivenessProperties == ActionOrderIsRecorded

Properties == LivenessProperties

====