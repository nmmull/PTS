-------------------------------------------------------------------------------
-- Tiered Pure Type Systems
--
-------------------------------------------------------------------------------

module Tiered where

open import Data.Nat using (ℕ; suc; pred; _<_; _≤?_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.String using (String)
open import Data.Sum using (_⊎_)
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
s i [ n / y ] = s i
b⟨ x ♯ i ⟩ [ n / y ] = b⟨ x ♯ i ⟩
f⟨ x ♯ i ⟩ [ n / y ♯ j ] with (x ♯ i) ≟ (y ♯ j) 
...                      | yes _  = n
...                      | _ = f⟨ x ♯ i ⟩
(λˢ i ∷ a ⇒ m) [ n / y ♯ j ] = λˢ i ∷ (a [ n / y ♯ j ]) ⇒ (m [ ↑ n / (suc y) ♯ j ])
(Πˢ i ∷ a ⇒ b) [ n / y ♯ j ] = Πˢ i ∷ (a [ n / y ♯ j ]) ⇒ (b [ ↑ n / (suc y) ♯ j ])
(m₁ § i § m₂) [ n / y ] = (m₁ [ n / y ]) § i § (m₂ [ n / y ])

_[_/_]ᵇ : 𝕋 → 𝕋 → 𝕍 → 𝕋 
s j [ n / x ]ᵇ = s j
f⟨ y ♯ j ⟩ [ n / x ]ᵇ = f⟨ y ♯ j ⟩
b⟨ y ♯ j ⟩ [ n / x ♯ i ]ᵇ with (y ♯ j) ≟ (x ♯ i)
...                          | yes _ = n
...                          | no _ = b⟨ y ♯ j ⟩
(λˢ j ∷ a ⇒ m) [ n / x ♯ i ]ᵇ = λˢ j ∷ (a [ n / x ♯ i ]ᵇ) ⇒ (m [ ↑ n / (suc x) ♯ i ]ᵇ)
(Πˢ j ∷ a ⇒ b) [ n / x ♯ i ]ᵇ = Πˢ j ∷ (a [ n / x ♯ i ]ᵇ) ⇒ (b [ ↑ n / (suc x) ♯ i ]ᵇ)
(m₁ § j § m₂) [ n / x ]ᵇ = (m₁ [ n / x ]ᵇ) § j § (m₂ [ n / x ]ᵇ)

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

data ℂ : Set where
  ∅ : ℂ
  _,_∷_ : ℂ → 𝕍 → 𝕋 → ℂ

data _∉_ : 𝕍 → ℂ → Set where
  ∉∅ : {x : 𝕍} → x ∉ ∅
  ∉Γ : {x y : 𝕍} → {Γ : ℂ} → {a : 𝕋} →
    x ∉ Γ →
    x ≡ y →
    x ∉ (Γ , y ∷ a)

_[_/_]ᶜ : ℂ → 𝕋 → 𝕍 → ℂ
∅ [ _ / _ ]ᶜ = ∅
(Γ , x ∷ a) [ n / y ]ᶜ = (Γ [ n / y ]ᶜ) , x ∷ (a [ n / y ])

_∘_ : ℂ → ℂ → ℂ
Γ ∘ ∅ = Γ
Γ ∘ (Δ , x ∷ a) = (Γ ∘ Δ) , x ∷ a

record Spec : Set₁ where
  field
    t : ℕ
    rule : ℕ → ℕ → Set

data _∥_⊢_∷_ : Spec → ℂ → 𝕋 → 𝕋 → Set₁ where

  axiom : {𝕊 : Spec} {i : ℕ} →
    i < Spec.t 𝕊 →
    -----------------------------------
    𝕊 ∥ ∅ ⊢ s i ∷ s (suc i)

  var-intro : {𝕊 : Spec} → {x i : ℕ} → {Γ : ℂ} → {a : 𝕋} →
    (x ♯ i) ∉ Γ →
    𝕊 ∥ Γ ⊢ a ∷ s i →
    -----------------------------------
    𝕊 ∥ (Γ , x ♯ i ∷ a) ⊢ f⟨ x ♯ i ⟩ ∷ a

  sort-weaken : {𝕊 : Spec} → {x i j : ℕ} → {Γ : ℂ} → {b : 𝕋} →
    (x ♯ i) ∉ Γ →
    𝕊 ∥ Γ ⊢ s j ∷ s (suc j) →
    𝕊 ∥ Γ ⊢ b ∷ s i →
    -----------------------------------
    𝕊 ∥ (Γ , x ♯ i ∷ b) ⊢ s j ∷ s (suc j)

  var-weaken : {𝕊 : Spec} → {x i y j : ℕ} → {Γ : ℂ} → {a b : 𝕋} →
    (y ♯ j) ∉ Γ →
    𝕊 ∥ Γ ⊢ f⟨ x ♯ i ⟩ ∷ a →
    𝕊 ∥ Γ ⊢ b ∷ s j →
    -----------------------------------
    𝕊 ∥ (Γ , y ♯ j ∷ b) ⊢ f⟨ x ♯ i ⟩ ∷ a

  pi-intro : {𝕊 : Spec} → {x i j : ℕ} → {Γ : ℂ} → {a b : 𝕋} →
    Spec.rule 𝕊 i j →
    𝕊 ∥ Γ ⊢ a ∷ s i →
    𝕊 ∥ (Γ , x ♯ i ∷ a) ⊢ b [ f⟨ x ♯ i ⟩ /0♯ i ] ∷ s j →
    -----------------------------------
    𝕊 ∥ Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j

  abstr : {𝕊 : Spec} → {x i j : ℕ} → {Γ : ℂ} → {m a b : 𝕋} →
    𝕊 ∥ (Γ , x ♯ i ∷ a) ⊢ m [ f⟨ x ♯ i ⟩ /0♯ i ] ∷ (b [ f⟨ x ♯ i ⟩ /0♯ i ]) →
    𝕊 ∥ Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j →
    -----------------------------------
    𝕊 ∥ Γ ⊢ (λˢ i ∷ a ⇒ m) ∷ (Πˢ i ∷ a ⇒ b)

  app : {𝕊 : Spec} → {i : ℕ} → {Γ : ℂ} → {m n a b c : 𝕋} →
    𝕊 ∥ Γ ⊢ m ∷ (Πˢ i ∷ a ⇒ b) →
    𝕊 ∥ Γ ⊢ n ∷ a →
    c ≡ b [ n /0♯ i ] →
    -----------------------------------
    𝕊 ∥ Γ ⊢ (m § i § n) ∷ c

  conv-red : {𝕊 : Spec} → {i : ℕ} → {Γ : ℂ} → {m a b : 𝕋} →
    𝕊 ∥ Γ ⊢ m ∷ a →
    𝕊 ∥ Γ ⊢ b ∷ s i →
    a ↠ᵇ b →
    -----------------------------------
    𝕊 ∥ Γ ⊢ m ∷ b
  
  conv-exp : {𝕊 : Spec} → {i : ℕ} → {Γ : ℂ} → {m a b : 𝕋} →
    𝕊 ∥ Γ ⊢ m ∷ a →
    𝕊 ∥ Γ ⊢ b ∷ s i →
    b ↠ᵇ a →
    -----------------------------------
    𝕊 ∥ Γ ⊢ m ∷ b


_∥_⊬_∷_ : (𝕊 : Spec) → ℂ → 𝕋 → 𝕋 → Set₁
𝕊 ∥ Γ ⊬ m ∷ a = ¬ (𝕊 ∥ Γ ⊢ m ∷ a)

-------------------------------------------------------------------------------
-- Well-formed Context

data WFC : (𝕊 : Spec) → ℂ → Set₁ where
  ∅-wf : {𝕊 : Spec} → WFC 𝕊 ∅
  ext-wf : {𝕊 : Spec} → {x i : ℕ} → {Γ : ℂ} → {a : 𝕋} →
    (x ♯ i) ∉ Γ →
    𝕊 ∥ Γ ⊢ a ∷ s i →
    WFC 𝕊 Γ →
    WFC 𝕊 (Γ , x ♯ i ∷ a)


 
