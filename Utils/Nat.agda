module Utils.Nat where

open import Data.Nat using (ℕ; _<_; _≤_; _+_; z≤n; s≤s)
open import Data.Nat.Properties using (1+n≰n)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Empty using (⊥-elim)

m≤n⇒m≤1+n : ∀ {m n} → m ≤ n → m ≤ 1 + n
m≤n⇒m≤1+n z≤n       = z≤n
m≤n⇒m≤1+n (s≤s m≤n) = s≤s (m≤n⇒m≤1+n m≤n)

m<n⇒m≢n : {m n : ℕ} → m < n → m ≢ n
m<n⇒m≢n (s≤s i<j) refl = ⊥-elim (1+n≰n i<j)

1+n≤m⇒n≤m : {n m : ℕ} → 1 + n ≤ m → n ≤ m
1+n≤m⇒n≤m (s≤s prf) = m≤n⇒m≤1+n prf

m≡n∧m≤p⇒n≤p : {n m p : ℕ} → m ≡ n → m ≤ p → n ≤ p
m≡n∧m≤p⇒n≤p refl prf = prf