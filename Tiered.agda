-------------------------------------------------------------------------------
-- Tiered Pure Type Systems
--
-------------------------------------------------------------------------------

module Tiered where

open import Data.Nat using (ℕ; suc; pred; _<_; _≤?_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.String using (String)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Definitions using (DecidableEquality)

-------------------------------------------------------------------------------
-- Grammar (with DeBruijn Indices and explicit sort annotations)

data 𝕋 : Set where
  s : ℕ → 𝕋 -- make prefix?
  f⟨_♯_⟩ : ℕ → ℕ → 𝕋
  b⟨_♯_⟩ : ℕ → ℕ → 𝕋
  λˢ_∷_⇒_ : ℕ → 𝕋 → 𝕋 → 𝕋
  Πˢ_∷_⇒_ : ℕ → 𝕋 → 𝕋 → 𝕋
  _§_§_ : 𝕋 → ℕ → 𝕋 → 𝕋

data 𝕍 : Set where
  _♯_ : ℕ → ℕ → 𝕍

_≟_ : DecidableEquality 𝕍
(x ♯ i) ≟ (y ♯ j) with x Data.Nat.≟ y with i Data.Nat.≟ j
...                  | yes refl          | yes refl = yes refl
...                  | no prf            | _        = no λ { refl → prf refl }
...                  | _                 | no prf   = no λ { refl → prf refl } 

-------------------------------------------------------------------------------
-- Substitution and Lifting

lift-map : (ℕ → ℕ) → ℕ → 𝕋 → 𝕋
lift-map f = go where
  go : ℕ → 𝕋 → 𝕋
  go x (s i) = s i
  go x b⟨ y ♯ i ⟩ = b⟨ y ♯ i ⟩
  go x f⟨ y ♯ i ⟩ with x ≤? y
  ...             | yes _ = f⟨ f y ♯ i ⟩
  ...             | no  _ = f⟨ y ♯ i ⟩
  go x (λˢ i ∷ m ⇒ n) = λˢ i ∷ go x m ⇒ go (suc x) n
  go x (Πˢ i ∷ a ⇒ b) = Πˢ i ∷ go x a ⇒ go (suc x) b 
  go x (m § i § n) = go x m § i § go x n

↑ : 𝕋 → 𝕋
↑ = lift-map suc 0

↓ : 𝕋 → 𝕋
↓ = lift-map pred 0

_[_/_] : 𝕋 → 𝕋 → 𝕍 → 𝕋
s i [ n / y ♯ j ] = s i
b⟨ x ♯ i ⟩ [ n / y ♯ j ] = b⟨ x ♯ i ⟩
f⟨ x ♯ i ⟩ [ n / y ♯ j ] with (x ♯ i) ≟ (y ♯ j) 
...                      | yes _  = n
...                      | _ = f⟨ x ♯ i ⟩
(λˢ i ∷ a ⇒ m) [ n / y ♯ j ] = λˢ i ∷ (a [ n / y ♯ j ]) ⇒ (m [ ↑ n / (suc y) ♯ j ])
(Πˢ i ∷ a ⇒ b) [ n / y ♯ j ] = Πˢ i ∷ (a [ n / y ♯ j ]) ⇒ (b [ ↑ n / (suc y) ♯ j ])
(m₁ § i § m₂) [ n / y ♯ j ] = (m₁ [ n / y ♯ j ]) § i § (m₂ [ n / y ♯ j ])

_[_/_]ᵇ : 𝕋 → 𝕋 → 𝕍 → 𝕋 
s j [ n / x ♯ i ]ᵇ = s j
f⟨ y ♯ j ⟩ [ n / x ♯ i ]ᵇ = f⟨ y ♯ j ⟩
b⟨ y ♯ j ⟩ [ n / x ♯ i ]ᵇ with (y ♯ j) ≟ (x ♯ i)
...                          | yes _ = n
...                          | no _ = b⟨ y ♯ j ⟩
(λˢ j ∷ a ⇒ m) [ n / x ♯ i ]ᵇ = λˢ j ∷ (a [ n / x ♯ i ]ᵇ) ⇒ (m [ ↑ n / (suc x) ♯ i ]ᵇ)
(Πˢ j ∷ a ⇒ b) [ n / x ♯ i ]ᵇ = Πˢ j ∷ (a [ n / x ♯ i ]ᵇ) ⇒ (b [ ↑ n / (suc x) ♯ i ]ᵇ)
(m₁ § j § m₂) [ n / x ♯ i ]ᵇ = (m₁ [ n / x ♯ i ]ᵇ) § j § (m₂ [ n / x ♯ i ]ᵇ)

_[_/0♯_] : 𝕋 → 𝕋 → ℕ → 𝕋
m [ n /0♯ i ] = ↓ (m [ ↑ n / 0 ♯ i ]ᵇ)

-------------------------------------------------------------------------------
-- β-Reduction

data _⟶ᵇ_ : 𝕋 → 𝕋 → Set where
  β-rule : {i : ℕ} → {a m n : 𝕋} →
    ((λˢ i ∷ a ⇒ m) § i § n) ⟶ᵇ (m [ n /0♯ i ])
  comp-pi₁ : {i : ℕ} → {a b a' : 𝕋} →
    a ⟶ᵇ a' →
    (Πˢ i ∷ a ⇒ b) ⟶ᵇ (Πˢ i ∷ a' ⇒ b)
  comp-pi₂ : {i : ℕ} → {a b b' : 𝕋} →
    b ⟶ᵇ b' →
    (Πˢ i ∷ a ⇒ b) ⟶ᵇ (Πˢ i ∷ a ⇒ b')
  comp-lam₁ : {i : ℕ} → {a b a' : 𝕋} →
    a ⟶ᵇ a' →
    (λˢ i ∷ a ⇒ b) ⟶ᵇ (λˢ i ∷ a' ⇒ b)
  comp-lam₂ : {i : ℕ} → {a b b' : 𝕋} →
    b ⟶ᵇ b' →
    (λˢ i ∷ a ⇒ b) ⟶ᵇ (λˢ i ∷ a ⇒ b')
  comp-app₁ : {i : ℕ} → {a b a' : 𝕋} →
    a ⟶ᵇ a' →
    (a § i § b) ⟶ᵇ (a' § i § b)
  comp-app₂ : {i : ℕ} → {a b b' : 𝕋} →
    b ⟶ᵇ b'
    → (a § i § b) ⟶ᵇ (a § i § b')

data _↠ᵇ_ : 𝕋 → 𝕋 → Set where
  β-refl : {i : ℕ} → {m : 𝕋} → m ↠ᵇ m
  β-step : {i : ℕ} → {m n n' : 𝕋} → m ⟶ᵇ n → n ↠ᵇ n' → m ↠ᵇ n'

↠ᵇ-trans : {m n p : 𝕋} →
  m ↠ᵇ n →
  n ↠ᵇ p →
  m ↠ᵇ p
↠ᵇ-trans β-refl np = np
↠ᵇ-trans (β-step {i} mn nn') np = β-step {i} mn (↠ᵇ-trans nn' np)

-------------------------------------------------------------------------------
-- Typing Inference

data Context : Set where
  ∅ : Context
  _,_∷_ : Context → 𝕍 → 𝕋 → Context

data _∉_ : 𝕍 → Context → Set where
  ∉∅ : {x : 𝕍} → x ∉ ∅
  ∉Γ : {x y : 𝕍} → {Γ : Context} → {a : 𝕋} →
    x ∉ Γ →
    x ≡ y →
    x ∉ (Γ , y ∷ a)

postulate t : ℕ -- for top sort
sₜ : 𝕋
sₜ = s t

postulate rule : ℕ → ℕ → Set

data _⊢_∷_ : Context → 𝕋 → 𝕋 → Set where

  axiom : {i : ℕ} →
    i < t →
    -----------------------------------
    ∅ ⊢ s i ∷ s (suc i)

  var-intro : {x i : ℕ} → {Γ : Context} → {a : 𝕋} →
    (x ♯ i) ∉ Γ →
    Γ ⊢ a ∷ s i →
    -----------------------------------
    (Γ , x ♯ i ∷ a) ⊢ f⟨ x ♯ i ⟩ ∷ a

  weaken : {x i : ℕ} → {Γ : Context} → {m a b : 𝕋} →
    (x ♯ i) ∉ Γ →
    Γ ⊢ m ∷ a →
    Γ ⊢ b ∷ s i →
    -----------------------------------
    (Γ , x ♯ i ∷ b) ⊢ m ∷ a

  pi-intro : {x i j : ℕ} → {Γ : Context} → {a b : 𝕋} →
    rule i j →
    Γ ⊢ a ∷ s i →
    (Γ , x ♯ i ∷ a) ⊢ b [ f⟨ x ♯ i ⟩ /0♯ i ] ∷ s j →
    -----------------------------------
    Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j

  abstr : {x i j : ℕ} → {Γ : Context} → {m a b : 𝕋} →
    (Γ , x ♯ i ∷ a) ⊢ m [ f⟨ x ♯ i ⟩ /0♯ i ] ∷ (b [ f⟨ x ♯ i ⟩ /0♯ i ]) →
    Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j →
    -----------------------------------
    Γ ⊢ (λˢ i ∷ a ⇒ m) ∷ (Πˢ i ∷ a ⇒ b)

  app : {i : ℕ} → {Γ : Context} → {m n a b c : 𝕋} →
    Γ ⊢ m ∷ (Πˢ i ∷ a ⇒ b) →
    Γ ⊢ n ∷ a →
    c ≡ b [ n /0♯ i ] →
    -----------------------------------
    Γ ⊢ (m § i § n) ∷ c

  conv : {i : ℕ} → {Γ : Context} → {m a b : 𝕋} →
    Γ ⊢ m ∷ a →
    Γ ⊢ b ∷ s i →
    b ↠ᵇ a →
    -----------------------------------
    Γ ⊢ m ∷ b

_⊬_∷_ : Context → 𝕋 → 𝕋 → Set
Γ ⊬ m ∷ a = ¬ (Γ ⊢ m ∷ a)

-------------------------------------------------------------------------------
-- Well-formed Contexts

data WFC : Context → Set where
  ∅-wf : WFC ∅
  ext-wf : {x i : ℕ} → {Γ : Context} → {a : 𝕋} →
    (x ♯ i) ∉ Γ →
    Γ ⊢ a ∷ s i →
    WFC Γ →
    WFC (Γ , x ♯ i ∷ a)

Γ-wf : {Γ : Context} → {m a : 𝕋} →
  Γ ⊢ m ∷ a →
  WFC Γ
Γ-wf = go where
  go : {Γ : Context} → {m a : 𝕋} → Γ ⊢ m ∷ a → WFC Γ
  go (axiom x) = ∅-wf
  go (var-intro fresh deriv) = ext-wf fresh deriv (go (deriv))
  go (weaken fresh _ deriv) = ext-wf fresh deriv (go (deriv))
  go (pi-intro _ deriv _) = go deriv
  go (abstr _ deriv) = go deriv
  go (app deriv _ _) = go deriv
  go (conv deriv _ _) = go deriv
