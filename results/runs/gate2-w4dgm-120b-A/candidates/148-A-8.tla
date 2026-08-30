---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

(* A model of the Nano blockchain's original block-lattice protocol.  Every      *)
(* account has its own chain of blocks, and each block is cryptographically      *)
(* signed and carries a hash derived from its predecessor.  The invariant        *)
(* protects that each node's replicated ledger only ever holds blocks with a    *)
(* signature that matches the account that owns the chain the block sits in.     *)

CONSTANTS
  Hash,         \* the set of all possible block hashes
  NoHashVal,    \* a sentinel meaning "no hash" (start of a chain)
  PrivateKey,   \* the set of private keys in the system
  PublicKey,    \* the set of public keys in the system
  Node,         \* the set of network nodes participating in the protocol
  GenesisBalance, \* the total coin supply seeded at the start
  NoBlockVal,   \* a sentinel value meaning "no block"
  CalculateHash, \* hash operator (abstract; overridden by CalculateHashImpl)
  NoHash,       \* a sentinel value meaning "no previous hash"
  NoBlock       \* a sentinel value meaning "no block"

ASSUME NoHash \notin Hash /\ NoBlock \notin Node

\* A private/public key mapping; private keys are the source of signatures.
KeyOf == [p \in PrivateKey |-> p]  \* identity mapping serving as placeholder

\* Block data: the account (public key) it belongs to, its predecessor's hash,
\* an optional second predecessor (for receive blocks), and its signature.
Block == [owner : PublicKey, prev : Hash \cup {NoHash},
           prev2 : Hash \cup {NoHash}, sig : PrivateKey]

\* The invariant sum of all account balances never exceeds the genesis balance.
RECURSIVE SumBalances(_)
SumBalances(S) ==
  IF S = {} THEN 0
  ELSE LET a == CHOOSE x \in S : TRUE
       IN BalanceOf(a) + SumBalances(S \ {a})

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Balance of an account = the genesis balance plus amounts credited by receive
\* blocks minus amounts debited by send blocks, summed over that account's chain.
RECURSIVE BalanceOf(_)
BalanceOf(a) == BalanceOfRec(a, NoHash)

RECURSIVE BalanceOfRec(_,_)
BalanceOfRec(a, h) ==
  IF h = NoHash THEN 0
  ELSE LET blk == ledger[h]
           rest == BalanceOfRec(a, blk.prev)
       IN IF blk = NoBlock THEN rest
          ELSE IF blk.owner = a
                 THEN IF blk.prev2 # NoHash
                         THEN rest + 1
                         ELSE rest - 1
               ELSE rest

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Hash -> Block \cup {NoBlockVal}]
  /\ received \in [Node -> SUBSET [hash : Hash, from : Node]]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ received = [n \in Node |-> {}]

\* The genesis block seeds the first account's chain with the whole supply.
CreateGenesis(p, n) ==
  /\ lastHash = NoHashVal
  /\ lastHash' = CalculateHash([owner |-> KeyOf[p], prev |-> NoHash,
                                prev2 |-> NoHash, sig |-> p], NoHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [owner |-> KeyOf[p], prev |-> NoHash,
                                             prev2 |-> NoHash, sig |-> p]]
  /\ \A m \in Node : received' = [received EXCEPT ![m] = @ \cup
                                   {[hash |-> lastHash', from |-> n]}]
  /\ UNCHANGED <<>>

\* A send block debits the sender's account by one and names a recipient.
CreateSend(p, n, recipient) ==
  /\ lastHash # NoHashVal
  /\ BalanceOf(KeyOf[p]) > 0
  /\ lastHash' = CalculateHash([owner |-> KeyOf[p], prev |-> lastHash,
                                prev2 |-> NoHash, sig |-> p], lastHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [owner |-> KeyOf[p],
                                             prev |-> lastHash, prev2 |-> NoHash,
                                             sig |-> p]]
  /\ \A m \in Node : received' = [received EXCEPT ![m] = @ \cup
                                   {[hash |-> lastHash', from |-> n]}]
  /\ UNCHANGED <<>>

\* An open block starts a new account's chain by linking to an incoming send.
CreateOpen(p, n, sendHash) ==
  /\ lastHash # NoHashVal
  /\ ledger[sendHash] # NoBlockVal
  /\ ledger[sendHash].owner = recipient
  /\ BalanceOf(KeyOf[p]) = 0
  /\ lastHash' = CalculateHash([owner |-> KeyOf[p], prev |-> NoHash,
                                prev2 |-> sendHash, sig |-> p], lastHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [owner |-> KeyOf[p],
                                             prev |-> NoHash,
                                             prev2 |-> sendHash, sig |-> p]]
  /\ \A m \in Node : received' = [received EXCEPT ![m] = @ \cup
                                   {[hash |-> lastHash', from |-> n]}]
  /\ UNCHANGED <<>>

\* A receive block credits this account and links to both its own predecessor
\* and the incoming send block.
CreateReceive(p, n, sendHash) ==
  /\ lastHash # NoHashVal
  /\ ledger[sendHash] # NoBlockVal
  /\ ledger[sendHash].owner = KeyOf[p]
  /\ BalanceOf(KeyOf[p]) >= 0
  /\ lastHash' = CalculateHash([owner |-> KeyOf[p], prev |-> lastHash,
                                prev2 |-> sendHash, sig |-> p], lastHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [owner |-> KeyOf[p],
                                             prev |-> lastHash,
                                             prev2 |-> sendHash, sig |-> p]]
  /\ \A m \in Node : received' = [received EXCEPT ![m] = @ \cup
                                   {[hash |-> lastHash', from |-> n]}]
  /\ UNCHANGED <<>>

\* A change-representative block re-signs the chain's head with no balance effect.
CreateChange(p, n) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHash([owner |-> KeyOf[p], prev |-> lastHash,
                                prev2 |-> NoHash, sig |-> p], lastHash)
  /\ ledger' = [ledger EXCEPT ![lastHash'] = [owner |-> KeyOf[p],
                                             prev |-> lastHash,
                                             prev2 |-> NoHash, sig |-> p]]
  /\ \A m \in Node : received' = [received EXCEPT ![m] = @ \cup
                                   {[hash |-> lastHash', from |-> n]}]
  /\ UNCHANGED <<>>

\* A node validates an inbound block against its local copy of the ledger.
Validate(n, h) ==
  /\ [hash |-> h, from |-> n] \in received[n]
  /\ ledger[h] # NoBlockVal
  /\ ledger[h].sig = CHOOSE p \in PrivateKey : KeyOf[p] = ledger[h].owner
  /\ received' = [received EXCEPT ![n] = @ \ {[hash |-> h, from |-> n]}]
  /\ UNCHANGED <<lastHash, ledger>>

Next ==
  \/ \E p \in PrivateKey, n \in Node : CreateGenesis(p, n)
  \/ \E p \in PrivateKey, n \in Node, rcpt \in PublicKey : CreateSend(p, n, rcpt)
  \/ \E p \in PrivateKey, n \in Node, h \in Hash : CreateOpen(p, n, h)
  \/ \E p \in PrivateKey, n \in Node, h \in Hash : CreateReceive(p, n, h)
  \/ \E p \in PrivateKey, n \in Node : CreateChange(p, n)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger has a signature matching the account that
\* owns the chain it belongs to.
SafetyInvariant ==
  \A h \in Hash : ledger[h] # NoBlockVal =>
    (ledger[h].sig = CHOOSE p \in PrivateKey : KeyOf[p] = ledger[h].owner)

====