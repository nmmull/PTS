module Utils.Nat where

open import Data.Nat using (_≤_; _+_; z≤n; s≤s)

m≤n⇒m≤1+n : ∀ {m n} → m ≤ n → m ≤ 1 + n
m≤n⇒m≤1+n z≤n       = z≤n
m≤n⇒m≤1+n (s≤s m≤n) = s≤s (m≤n⇒m≤1+n m≤n)