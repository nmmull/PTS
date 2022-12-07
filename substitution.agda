-------------------------------------------------------------------------------
-- Lemma about Lifting and Substitution
--
-------------------------------------------------------------------------------

module Substitution where

open import Tiered
open import Data.Nat using (ℕ; suc; pred; _≤?_)
open import Utils.Nat using (m≤n⇒m≤1+n)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.Definitions using (DecidableEquality)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; subst; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)


lift-drop-lemma : {x : ℕ} → {m : Term} →
  lift-map pred x (lift-map suc x m) ≡ m
lift-drop-lemma {x} {m} = go x m where
  l : ℕ → Term → Term
  l = lift-map suc
  d : ℕ → Term → Term
  d = lift-map pred
  go : (x : ℕ) → (m : Term) →
    d x (l x m) ≡ m
  go x (s i) = refl
  go x (y ♯ i) with x ≤? y
  go x (y ♯ i)    | yes p' with x ≤? suc y
  go x (y ♯ i)    | yes p'    | yes _ = refl
  go x (y ♯ i)    | yes p'    | no ¬p = ⊥-elim (¬p (m≤n⇒m≤1+n p'))
  go x (y ♯ i)    | no ¬p with x ≤? y
  go x (y ♯ i)    | no ¬p    | yes p = ⊥-elim (¬p p)
  go x (y ♯ i)    | no ¬p    | no _ = refl
  go x (λˢ i ∷ m ⇒ n) =
    begin
      d x (l x (λˢ i ∷ m ⇒ n))
    ≡⟨⟩
      d x (λˢ i ∷ (l x m) ⇒ (l (suc x) n))
    ≡⟨⟩
      λˢ i ∷ (d x (l x m)) ⇒ (d (suc x) (l (suc x) n))
    ≡⟨ cong (λ { m → λˢ i ∷ m ⇒ (d (suc x) (l (suc x) n)) }) (go x m) ⟩
      λˢ i ∷ m ⇒ (d (suc x) (l (suc x) n))
    ≡⟨ cong (λ { n → λˢ i ∷ m ⇒ n }) (go (suc x) n) ⟩
      λˢ i ∷ m ⇒ n
    ∎
  go x (Πˢ i ∷ m ⇒ n) =
    begin
      d x (l x (Πˢ i ∷ m ⇒ n))
    ≡⟨⟩
      Πˢ i ∷ (d x (l x m)) ⇒ (d (suc x) (l (suc x) n))
    ≡⟨ cong₂ (λ { m n → Πˢ i ∷ m ⇒ n }) (go x m) (go (suc x) n) ⟩
      Πˢ i ∷ m ⇒ n
    ∎
  go x (m § i § n) =
    begin
      d x (l x (m § i § n))
    ≡⟨ cong₂ (λ { m n → m § i § n }) (go x m) (go x n) ⟩
      m § i § n
    ∎

↓↑-id : {n : Term} →
  ↓ (↑ n) ≡ n
↓↑-id = lift-drop-lemma {x = 0}