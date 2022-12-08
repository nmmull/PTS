-------------------------------------------------------------------------------
-- Tiered Pure Type Systems
--
-------------------------------------------------------------------------------

module Tiered where

open import Data.Nat using (ℕ; suc; pred; _<_; _≤?_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Definitions using (DecidableEquality)

-------------------------------------------------------------------------------
-- Grammar (with DeBruijn Indices and explicit sort annotations)

data Term : Set where
  s : ℕ → Term
  _♯_ : ℕ → ℕ → Term
  λˢ_∷_⇒_ : ℕ → Term → Term → Term
  Πˢ_∷_⇒_ : ℕ → Term → Term → Term
  _§_§_ : Term → ℕ → Term → Term

data Variable : Set where
  _♯_ : ℕ → ℕ → Variable

_≟_ : DecidableEquality Variable
(x ♯ i) ≟ (y ♯ j) with x Data.Nat.≟ y with i Data.Nat.≟ j
...                  | yes refl          | yes refl = yes refl
...                  | no prf            | _        = no λ { refl → prf refl }
...                  | _                 | no prf   = no λ { refl → prf refl } 

data _∈_ : Variable → Term → Set where
  x∈x : {x i : ℕ} → (x ♯ i) ∈ (x ♯ i)
  x∈λ : {i : ℕ} → {x : Variable} → {a m : Term} → x ∈ a → x ∈ (λˢ i ∷ a ⇒ m) 

-------------------------------------------------------------------------------
-- Substitution and Lifting

lift-map : (ℕ → ℕ) → ℕ → Term → Term
lift-map f = go where
  go : ℕ → Term → Term
  go x (s i) = s i
  go x (y ♯ i) with x ≤? y
  ...             | yes _ = f y ♯ i
  ...             | no  _ = y ♯ i
  go x (λˢ i ∷ m ⇒ n) = λˢ i ∷ go x m ⇒ go (suc x) n
  go x (Πˢ i ∷ a ⇒ b) = Πˢ i ∷ go x a ⇒ go (suc x) b 
  go x (m § i § n) = go x m § i § go x n

↑ : Term → Term
↑ = lift-map suc 0

↓ : Term → Term
↓ = lift-map pred 0

_[_/_] : Term → Term → Variable → Term
s i [ n / y ♯ j ] = s i
(x ♯ i) [ n / y ♯ j ] with (x ♯ i) ≟ (y ♯ j) 
...                      | yes _  = n
...                      | _ = x ♯ i
(λˢ i ∷ a ⇒ m) [ n / y ♯ j ] = λˢ i ∷ (a [ n / y ♯ j ]) ⇒ (m [ ↑ n / (suc y) ♯ j ])
(Πˢ i ∷ a ⇒ b) [ n / y ♯ j ] = Πˢ i ∷ (a [ n / y ♯ j ]) ⇒ (b [ ↑ n / (suc y) ♯ j ])
(m₁ § i § m₂) [ n / y ♯ j ] = (m₁ [ n / y ♯ j ]) § i § (m₂ [ n / y ♯ j ])

_[_/_]′ : Term → Term → Variable → Term 
m [ n / x ]′ = ↓ (m [ ↑ n / x ])

-------------------------------------------------------------------------------
-- β-Reduction

data _⟶ᵇ_ : Term → Term → Set where
  β-rule : {i : ℕ} → {a m n : Term} →
    ((λˢ i ∷ a ⇒ m) § i § n) ⟶ᵇ (m [ n / 0 ♯ i ]′)
  comp-pi₁ : {i : ℕ} → {a b a' : Term} →
    a ⟶ᵇ a' →
    (Πˢ i ∷ a ⇒ b) ⟶ᵇ (Πˢ i ∷ a' ⇒ b)
  comp-pi₂ : {i : ℕ} → {a b b' : Term} →
    b ⟶ᵇ b' →
    (Πˢ i ∷ a ⇒ b) ⟶ᵇ (Πˢ i ∷ a ⇒ b')
  comp-lam₁ : {i : ℕ} → {a b a' : Term} →
    a ⟶ᵇ a' →
    (λˢ i ∷ a ⇒ b) ⟶ᵇ (λˢ i ∷ a' ⇒ b)
  comp-lam₂ : {i : ℕ} → {a b b' : Term} →
    b ⟶ᵇ b' →
    (λˢ i ∷ a ⇒ b) ⟶ᵇ (λˢ i ∷ a ⇒ b')
  comp-app₁ : {i : ℕ} → {a b a' : Term} →
    a ⟶ᵇ a' →
    (a § i § b) ⟶ᵇ (a' § i § b)
  comp-app₂ : {i : ℕ} → {a b b' : Term} →
    b ⟶ᵇ b'
    → (a § i § b) ⟶ᵇ (a § i § b')

data _↠ᵇ_ : Term → Term → Set where
  β-refl : {i : ℕ} → {m : Term} → m ↠ᵇ m
  β-step : {i : ℕ} → {m n n' : Term} → m ⟶ᵇ n → n ↠ᵇ n' → m ↠ᵇ n'

↠ᵇ-trans : {m n p : Term} →
  m ↠ᵇ n →
  n ↠ᵇ p →
  m ↠ᵇ p
↠ᵇ-trans β-refl np = np
↠ᵇ-trans (β-step {i} mn nn') np = β-step {i} mn (↠ᵇ-trans nn' np)

-------------------------------------------------------------------------------
-- Typing Inference

data Context : Set where
  ∅ : Context
  _,_∷_ : Context → Variable → Term → Context

data _∉_ : Variable → Context → Set where
  ∉∅ : {x : Variable} → x ∉ ∅
  ∉Γ : {x y : Variable} → {Γ : Context} → {a : Term} →
    x ∉ Γ →
    x ≡ y →
    x ∉ (Γ , y ∷ a)

postulate top-sort : ℕ
postulate rule : ℕ → ℕ → Set

sₜ : Term
sₜ = s top-sort

data _⊢_∷_ : Context → Term → Term → Set where

  axiom : {i : ℕ} →
    i < top-sort →
    -----------------------------------
    ∅ ⊢ s i ∷ s (suc i)

  var-intro : {x i : ℕ} → {Γ : Context} → {a : Term} →
    (x ♯ i) ∉ Γ →
    Γ ⊢ a ∷ s i →
    -----------------------------------
    (Γ , x ♯ i ∷ a) ⊢ x ♯ i ∷ a

  weaken : {x i : ℕ} → {Γ : Context} → {m a b : Term} →
    (x ♯ i) ∉ Γ →
    Γ ⊢ m ∷ a →
    Γ ⊢ b ∷ s i →
    -----------------------------------
    (Γ , x ♯ i ∷ b) ⊢ m ∷ a

  pi-intro : {x i j : ℕ} → {Γ : Context} → {a b : Term} →
    rule i j →
    Γ ⊢ a ∷ s i →
    (Γ , x ♯ i ∷ a) ⊢ b [ x ♯ i / 0 ♯ i ]′ ∷ s j →
    -----------------------------------
    Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j

  abstr : {x i j : ℕ} → {Γ : Context} → {m a b : Term} →
    (Γ , x ♯ i ∷ a) ⊢ m [ x ♯ i / 0 ♯ i ]′ ∷ (b [ x ♯ i / 0 ♯ i ]′) →
    Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j →
    -----------------------------------
    Γ ⊢ (λˢ i ∷ a ⇒ m) ∷ (Πˢ i ∷ a ⇒ b)

  app : {i : ℕ} → {Γ : Context} → {m n a b c : Term} →
    Γ ⊢ m ∷ (Πˢ i ∷ a ⇒ b) →
    Γ ⊢ n ∷ a →
    c ≡ b [ n / 0 ♯ i ]′ →
    -----------------------------------
    Γ ⊢ (m § i § n) ∷ c

  conv : {i : ℕ} → {Γ : Context} → {m a b : Term} →
    Γ ⊢ m ∷ a →
    Γ ⊢ b ∷ s i →
    b ↠ᵇ a →
    -----------------------------------
    Γ ⊢ m ∷ b

_⊬_∷_ : Context → Term → Term → Set
Γ ⊬ m ∷ a = ¬ (Γ ⊢ m ∷ a)

-------------------------------------------------------------------------------
-- Well-formed Contexts

data WFC : Context → Set where
  ∅-wf : WFC ∅
  ext-wf : {x i : ℕ} → {Γ : Context} → {a : Term} →
    (x ♯ i) ∉ Γ →
    Γ ⊢ a ∷ s i →
    WFC Γ →
    WFC (Γ , x ♯ i ∷ a)

Γ-wf : {Γ : Context} → {m a : Term} →
  Γ ⊢ m ∷ a →
  WFC Γ
Γ-wf = go where
  go : {Γ : Context} → {m a : Term} → Γ ⊢ m ∷ a → WFC Γ
  go (axiom x) = ∅-wf
  go (var-intro fresh deriv) = ext-wf fresh deriv (go (deriv))
  go (weaken fresh _ deriv) = ext-wf fresh deriv (go (deriv))
  go (pi-intro _ deriv _) = go deriv
  go (abstr _ deriv) = go deriv
  go (app deriv _ _) = go deriv
  go (conv deriv _ _) = go deriv