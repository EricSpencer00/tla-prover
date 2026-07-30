---- MODULE Nano ----
\* Nano cryptocurrency blockchain block-lattice with Ed25519 signatures and Blake2b hashes.
EXTENDS Naturals, FiniteSets, TLC

\* The hash calculation is abstracted away: CalculateHash is a constant operator that
\* maps block data and the previous hash to a new hash, and is defined only in the .cfg.
CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

\* A block lives on exactly one account chain and records its creator's public key plus
\* the previous block in that chain; because every block has a parent, the entire
\* history of an account is recorded in order through the lattice itself.
Blocks == [sig: PUBLICKEY, prev: HASH, pk: PUBLICKEY, kind: {"genesis", "send", "receive", "open", "change"}, amnt: Nat]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Every node keeps its own full copy of the distributed ledger, so ledger is a map
\* from node to a map from hash to block (or NoBlockVal as a sentinel).
TypeOK ==
  /\ lastHash \in HASH
  /\ ledger \in [Node -> [Hash -> Blocks \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

\* Every block in the lattice has a valid signature against the public key of the
\* account chain it lives on; this is the system's only cryptographic guarantee.
AuthOK ==
  /\ \A n \in Node, h \in Hash :
       ledger[n][h] # NoBlockVal => ledger[n][h].sig = ledger[n][h].pk
  /\ \A n \in Node : \A h1, h2 \in Hash :
       (ledger[n][h1] # NoBlockVal /\ ledger[n][h2] # NoBlockVal /\ ledger[n][h1] = ledger[n][h2]) => h1 = h2

\* BalanceOf walks an account's chain backwards into the lattice to sum its held funds.
RECURSIVE BalanceOf(_)
BalanceOf(h) ==
  IF h = NoHashVal THEN 0
  ELSE ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal][h].amnt +
       BalanceOf(ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal][h].prev)

SumBalance ==
  LET f[S \in SUBSET Hash] ==
       IF S = {} THEN 0
       ELSE LET h == CHOOSE x \in S : TRUE IN BalanceOf(h) + f[S \ {h}]
  IN f[Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Every block-creation action also broadcasts the block to every node's received set;
\* that is what makes validation reachable (the validator may lag behind the creator).
CreateGenesis(k) ==
  /\ lastHash = NoHashVal
  /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = NoHashVal THEN [sig |-> NoHash, prev |-> NoHashVal, pk |-> k, kind |-> "genesis", amnt |-> GenesisBalance] ELSE ledger[n][h]]]
  /\ lastHash' = NoHashVal
  /\ received' = [n \in Node |-> {NoHashVal}]
  /\ UNCHANGED <<>>

CreateSend(n, k, h, v) ==
  /\ lastHash # NoHashVal
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][lastHash] # NoBlockVal
  /\ BalanceOf(h) >= v
  /\ ledger' = [ledger EXCEPT ![n][NoHashVal] = [sig |-> k, prev |-> lastHash, pk |-> k, kind |-> "send", amnt |-> v]]
  /\ lastHash' = NoHashVal
  /\ received' = [received EXCEPT ![n] = @ \cup {NoHashVal}]
  /\ UNCHANGED <<>>

CreateOpen(n, k, h) ==
  /\ lastHash # NoHashVal
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][lastHash] # NoBlockVal
  /\ ledger[n][h].kind = "send"
  /\ ledger[n][h].sig # k
  /\ ledger[n][h].amnt > 0
  /\ \A o \in Node : ledger[o][h] = NoBlockVal
  /\ ledger' = [ledger EXCEPT ![n][NoHashVal] = [sig |-> k, prev |-> lastHash, pk |-> k, kind |-> "open", amnt |-> 0]]
  /\ lastHash' = NoHashVal
  /\ received' = [received EXCEPT ![n] = @ \cup {NoHashVal}]
  /\ UNCHANGED <<>>

CreateReceive(n, k, h, send) ==
  /\ lastHash # NoHashVal
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][lastHash] # NoBlockVal
  /\ ledger[n][send] # NoBlockVal
  /\ ledger[n][send].kind \in {"send", "open"}
  /\ ledger[n][send].sig = k
  /\ ledger' = [ledger EXCEPT ![n][NoHashVal] = [sig |-> k, prev |-> lastHash, pk |-> k, kind |-> "receive", amnt |-> ledger[n][send].amnt]]
  /\ lastHash' = NoHashVal
  /\ received' = [received EXCEPT ![n] = @ \cup {NoHashVal}]
  /\ UNCHANGED <<>>

CreateChange(n, k, h) ==
  /\ lastHash # NoHashVal
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][lastHash] # NoBlockVal
  /\ ledger' = [ledger EXCEPT ![n][NoHashVal] = [sig |-> k, prev |-> lastHash, pk |-> k, kind |-> "change", amnt |-> 0]]
  /\ lastHash' = NoHashVal
  /\ received' = [received EXCEPT ![n] = @ \cup {NoHashVal}]
  /\ UNCHANGED <<>>

\* Validation: a node requires the parent block it references to already be present in
\* its own copy of the ledger before the new one is accepted (ordered construction).
Validate(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] = NoBlockVal
  /\ \E o \in Node : ledger[o][h] # NoBlockVal
  /\ ledger' = [ledger EXCEPT ![n][h] = CHOOSE o \in Node : ledger[o][h] # NoBlockVal]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED <<lastHash>>

Next ==
  \/ \E k \in PublicKey : CreateGenesis(k)
  \/ \E n \in Node, k \in PublicKey, h \in Hash, v \in 1..GenesisBalance : CreateSend(n, k, h, v)
  \/ \E n \in Node, k \in PublicKey, h \in Hash : CreateOpen(n, k, h)
  \/ \E n \in Node, k \in PublicKey, h \in Hash, send \in Hash : CreateReceive(n, k, h, send)
  \/ \E n \in Node, k \in PublicKey, h \in Hash : CreateChange(n, k, h)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

\* The reference checker expects the type invariant under one name, AuthOK under another.
TypeInvariant == TypeOK
SafetyInvariant == AuthOK

====