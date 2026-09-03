---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Hash, NoHashVal,
  PrivateKey, PublicKey,
  Node, GenesisBalance,
  NoBlockVal, NoHash, NoBlock,
  CalculateHash

\* The block-lattice: each account (identified by a public key) has its own
\* chain, and the chain order is part of the block's identity. We track a
\* naive ledger replicated per node plus a per-node set of received blocks
\* awaiting confirmation.

Block == [kind: {"send", "receive", "open", "changeRep", "genesis"},
           creator: PrivateKey,
           pubkey: PublicKey,
           prevHash: Hash \ {NoHash},
           refHash: Hash \ {NoHash},
           amount: 0..GenesisBalance]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlock}]]
  /\ received \in [Node -> SUBSET (Hash \X Block)]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> {}]

\* Balance is computed by walking the account chain backwards from the last
\* block in that account's chain.
SumAmounts(S) == LET f[T \in SUBSET Block] ==
                     IF T = {} THEN 0
                     ELSE LET x == CHOOSE y \in T : \A z \in T : y.pubkey = z.pubkey
                          IN x.amount + f[T \ {x}]
                 IN f[S]

BalanceAt(account, n) == LET chain == {h \in Hash : ledger[n][h] # NoBlock
                                         /\ ledger[n][h].pubkey = account}
                         IN SumAmounts(chain)

Insert(n, h, blk) == [n \in Node |-> [ledger[n] EXCEPT ![h] = blk]]

CreateGenesis ==
  /\ lastHash = NoHash
  /\ \E pk \in PrivateKey :
       LET h == CalculateHash([kind |-> "genesis", creator |-> pk, pubkey |-> "genesis",
                               prevHash |-> NoHash, refHash |-> NoHash, amount |-> GenesisBalance])
       IN /\ lastHash' = h
          /\ ledger' = Insert(Node, h,
               [kind |-> "genesis", creator |-> pk, pubkey |-> "genesis",
                prevHash |-> NoHash, refHash |-> NoHash, amount |-> GenesisBalance])
          /\ received' = [n \in Node |-> received[n] \cup {<<h, [kind |-> "genesis", creator |-> pk,
               pubkey |-> "genesis", prevHash |-> NoHash, refHash |-> NoHash,
               amount |-> GenesisBalance]>>}]
  /\ UNCHANGED <<received>>

CreateSend(n, pk, amt, recPub) ==
  /\ lastHash # NoHash
  /\ ledger[n][lastHash] /= NoBlock
  /\ ledger[n][lastHash].pubkey = pk
  /\ BalanceAt(pk, n) >= amt
  /\ \E h \in Hash :
       /\ ledger[n][h] = NoBlock
       /\ h \notin {x.h : x \in received[n]}
       /\ LET blk == [kind |-> "send", creator |-> pk, pubkey |-> pk,
                      prevHash |-> lastHash, refHash |-> NoHash, amount |-> amt]
              nh == CalculateHash(blk)
          IN /\ nh = h
             /\ received' = [received EXCEPT ![n] = @ \cup {<<h, blk>>}]
  /\ UNCHANGED <<lastHash, ledger>>

CreateOpen(n, pk, amt, sendHash) ==
  /\ lastHash # NoHash
  /\ ledger[n][lastHash] /= NoBlock
  /\ \E h \in Hash :
       /\ ledger[n][h] = NoBlock
       /\ h \notin {x.h : x \in received[n]}
       /\ LET blk == [kind |-> "open", creator |-> pk, pubkey |-> pk,
                      prevHash |-> NoHash, refHash |-> sendHash, amount |-> amt]
              nh == CalculateHash(blk)
          IN /\ nh = h
             /\ received' = [received EXCEPT ![n] = @ \cup {<<h, blk>>}]
  /\ UNCHANGED <<lastHash, ledger>>

CreateReceive(n, pk, sendHash) ==
  /\ lastHash # NoHash
  /\ ledger[n][lastHash] /= NoBlock
  /\ \E h \in Hash :
       /\ ledger[n][h] = NoBlock
       /\ h \notin {x.h : x \in received[n]}
       /\ LET blk == [kind |-> "receive", creator |-> pk, pubkey |-> pk,
                      prevHash |-> lastHash, refHash |-> sendHash, amount |-> 0]
              nh == CalculateHash(blk)
          IN /\ nh = h
             /\ received' = [received EXCEPT ![n] = @ \cup {<<h, blk>>}]
  /\ UNCHANGED <<lastHash, ledger>>

CreateChangeRep(n, pk) ==
  /\ lastHash # NoHash
  /\ ledger[n][lastHash] /= NoBlock
  /\ ledger[n][lastHash].pubkey = pk
  /\ \E h \in Hash :
       /\ ledger[n][h] = NoBlock
       /\ h \notin {x.h : x \in received[n]}
       /\ LET blk == [kind |-> "changeRep", creator |-> pk, pubkey |-> pk,
                      prevHash |-> lastHash, refHash |-> NoHash, amount |-> 0]
              nh == CalculateHash(blk)
          IN /\ nh = h
             /\ received' = [received EXCEPT ![n] = @ \cup {<<h, blk>>}]
  /\ UNCHANGED <<lastHash, ledger>>

Validate(n) ==
  /\ received[n] # {}
  /\ \E x \in received[n] :
       /\ ledger[n][x[1]] = NoBlock
       /\ LET blk == x[2] IN
            /\ blk.creator = blk.pubkey
            /\ (\A r \in Node : ledger[r][x[1]] = NoBlock \/ ledger[r][x[1]] = blk)
            /\ (blk.kind \in {"send", "receive"} => ledger[n][blk.refHash] # NoBlock)
            /\ (blk.kind = "send" => BalanceAt(blk.pubkey, n) >= blk.amount)
            /\ (blk.kind = "open" => ledger[n][blk.refHash] # NoBlock /\ ledger[n][blk.refHash].kind = "send")
            /\ ledger' = [ledger EXCEPT ![n][x[1]] = blk]
            /\ lastHash' = IF ledger[n][x[1]] = NoBlock /\ x[1] # NoHashVal
                           THEN x[1] ELSE lastHash
       /\ received' = [received EXCEPT ![n] = @ \ {x}]
  /\ UNCHANGED <<lastHash>>

Next ==
  \/ CreateGenesis
  \/ \E n \in Node, pk \in PublicKey, amt \in 1..GenesisBalance :
        \E recPub \in PublicKey :
          CreateSend(n, pk, amt, recPub)
          \/ CreateOpen(n, pk, amt, NoHash)
  \/ \E n \in Node, pk \in PublicKey, sendHash \in Hash :
        CreateReceive(n, pk, sendHash)
        \/ CreateChangeRep(n, pk)
  \/ \E n \in Node : Validate(n)

Spec == Init /\ [][Next]_vars

\* Cryptographic sanity: every recorded block is signed by its own creator.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash :
    ledger[n][h] # NoBlock => ledger[n][h].creator = ledger[n][h].pubkey

\* Accounting sanity: the total of all account balances never exceeds the
\* genesis supply -- blocks only move value, never create or destroy it.
BalanceInvariant ==
  SumAmounts({h \in Hash : ledger[CHOOSE n \in Node : TRUE][h] /= NoBlock})
    <= GenesisBalance

====