---- MODULE mathd_numbertheory_335 ----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_335 ==
  \A n \in Nat : (n % 7 = 5) => ((5 * n) % 7 = 4)BY SetExtensionality
====
