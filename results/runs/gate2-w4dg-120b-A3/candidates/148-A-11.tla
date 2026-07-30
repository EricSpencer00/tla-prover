---- MODULE Nano ----
EXTENDS Naturals

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

\* A block carries the hash of the block that immediately precedes it in its own
\* account chain (PrevHash). The hash calculation is abstract and overridden in
\* the TLC configuration so it can be tuned (or made deterministic) for model
\* checking, which is what the cfg substitution mapping is for.

HashType == PUBLIC
BlockType == [prev : Hash \cup {NoHash}, from : PublicKey, to : PublicKey,
              amount : Nat, typ : {"genesis", "send", "open", "receive", "change"}, signer : PublicKey]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

BlankChain == NoHashVal

\* Balance is calculated recursively by walking the account chain from the head
\* hash backwards, summing, for send blocks, the funds that left the account.
RECURSIVE Balance(_)
Balance(h) ==
  \/ h = BlankChain
      /\ 0
  \/ LET b == ledger[h] IN
       IF b.from = b.to
         THEN Balance(b.prev)
       ELSE IF b.typ = "send"
         THEN Balance(b.prev) - b.amount
       ELSE IF b.typ \in {"open", "receive"}
         THEN Balance(b.prev) + b.amount
       ELSE Balance(b.prev)

RECURSIVE Claimed(_)
Claimed(h) ==
  \/ h = BlankChain
      /\ 0
  \/ LET b == ledger[h] IN
       IF b.typ \in {"genesis", "receive"}
         THEN Claimed(b.prev) + b.amount
       ELSE Claimed(b.prev) + IF b.typ = "send" THEN b.amount ELSE 0

RECURSIVE ChainSeen(_)
ChainSeen(h) ==
  \/ h = BlankChain
      /\ {}
  \/ LET b == ledger[h] IN
       ChainSeen(b.prev) \cup {b.from}

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Hash -> BlockType \cup {NoBlockVal}]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ received = [n \in Node |-> {}]

\* The genesis block is unique: it is the only block that may be created with
\* PrevHash = NoHash and the only block signed by the genesis account.
CreateGenesis(nk) ==
  /\ lastHash = NoHashVal
  /\ ledger' = [ledger EXCEPT ![CalculateHash(0, NoHash)] =
       [prev |-> NoHash, from |-> NoHash, to |-> NoHash, amount |-> GenesisBalance,
        typ |-> "genesis", signer |-> nk]]
  /\ \A m \in Node : received' = [received EXCEPT ![m] = @ \cup {CalculateHash(0, NoHash)}]
  /\ lastHash' = CalculateHash(0, NoHash)

\* A new hash based on the previous head hash in the same account chain.
CreateSend(nk, to, amt) ==
  /\ lastHash # NoHashVal
  /\ ledger[lastHash].signer = nk
  /\ Balance(lastHash) >= amt
  /\ ledger' = [ledger EXCEPT ![CalculateHash(amt, lastHash)] =
       [prev |-> lastHash, from |-> nk, to |-> to, amount |-> amt,
        typ |-> "send", signer |-> nk]]
  /\ \A m \in Node : received' = [received EXCEPT ![m] = @ \cup {CalculateHash(amt, lastHash)}]
  /\ lastHash' = CalculateHash(amt, lastHash)

\* The first block of an account (prev = NoHash) references a send block directed
\* to it that has not already been claimed by another open/receive block.
CreateOpen(nk, send) ==
  /\ lastHash # NoHashVal
  /\ ledger[send].typ = "send"
  /\ ledger[send].to = nk
  /\ ledger[send] \notin {ledger[h] : h \in ChainSeen(lastHash)}
  /\ ledger' = [ledger EXCEPT ![CalculateHash(0, lastHash)] =
       [prev |-> NoHash, from |-> nk, to |-> nk, amount |-> 0,
        typ |-> "open", signer |-> nk]]
  /\ \A m \in Node : received' = [received EXCEPT ![m] = @ \cup {CalculateHash(0, lastHash)}]
  /\ lastHash' = CalculateHash(0, lastHash)

CreateReceive(nk, send) ==
  /\ lastHash # NoHashVal
  /\ ledger[send].typ = "send"
  /\ ledger[send].to = nk
  /\ ledger[send] \notin {ledger[h] : h \in ChainSeen(lastHash)}
  /\ ledger' = [ledger EXCEPT ![CalculateHash(0, lastHash)] =
       [prev |-> lastHash, from |-> nk, to |-> nk, amount |-> 0,
        typ |-> "receive", signer |-> nk]]
  /\ \A m \in Node : received' = [received EXCEPT ![m] = @ \cup {CalculateHash(0, lastHash)}]
  /\ lastHash' = CalculateHash(0, lastHash)

CreateChangeRep(nk) ==
  /\ lastHash # NoHashVal
  /\ ledger[lastHash].signer = nk
  /\ ledger' = [ledger EXCEPT ![CalculateHash(0, lastHash)] =
       [prev |-> lastHash, from |-> nk, to |-> nk, amount |-> 0,
        typ |-> "change", signer |-> nk]]
  /\ \A m \in Node : received' = [received EXCEPT ![m] = @ \cup {CalculateHash(0, lastHash)}]
  /\ lastHash' = CalculateHash(0, lastHash)

ValidateReceive(n, h) ==
  /\ h \in received[n]
  /\ ledger[h] # NoBlockVal
  /\ hubcheck(n, h)
  /\ ledger' = [ledger EXCEPT ![h] = ledger[h]]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED lastHash

\* hubcheck: local validation of the block's signature and chain references.
hubcheck(n, h) ==
  /\ ledger[h].signer \in ChainSeen(n)
  /\ ledger[h].prev = NoHash \/ ledger[ledger[h].prev] # NoBlockVal
  /\ CASE ledger[h].typ = "send" -> ledger[h].amount <= Balance(n) /\ ledger[h].from = n
        [] ledger[h].typ = "open" -> ledger[h].to = n
        [] ledger[h].typ = "receive" -> ledger[h].to = n
        [] OTHER -> TRUE

ValidateSend(n, h) ==
  /\ h \in received[n]
  /\ ledger[h] # NoBlockVal
  /\ hubcheck(n, h)
  /\ ledger' = [ledger EXCEPT ![h] = ledger[h]]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E nk \in PrivateKey : CreateGenesis(nk) \/ CreateChangeRep(nk)
  \/ \E nk \in PrivateKey, to \in PublicKey, amt \in 1..GenesisBalance : CreateSend(nk, to, amt)
  \/ \E nk \in PrivateKey, send \in Hash : CreateOpen(nk, send) \/ CreateReceive(nk, send)
  \/ \E n \in Node, h \in Hash : ValidateSend(n, h) \/ ValidateReceive(n, h)

Spec == Init /\ [][Next]_vars

\* TypeInvariant: the three state variables retain their declared types.
TypeInvariant == TypeOK

\* SafetyInvariant: every block in every node's ledger carries a signature that
\* matches the public key of the account it belongs to.
SafetyInvariant == \A h \in Hash : ledger[h] # NoBlockVal => ledger[h].signer = ledger[h].from

====