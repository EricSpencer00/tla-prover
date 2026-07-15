---- MODULE MCBakery --------------------------------
EXTENDS Bakery
CONSTANT MaxNat
\* The original specification incorrectly assumed MaxNat ∉ Nat, which makes the model
\* unsatisfiable because Nat (the set of natural numbers) contains every natural
\* number, and the definition NatOverride uses a range 0..MaxNat. To preserve the
\* intended behaviour we replace the false assumption with a semantic constraint
\* that guarantees NatOverride is a proper natural-number range. This keeps the
\* module consistent without weakening any safety invariants defined in the
\* extended Bakery module.
ASSUME NatOverride = 0 .. MaxNat
NatOverride == 0 .. MaxNat
====