-------------------------------------------------------------------------------
-- Pure Type Systems
--
-------------------------------------------------------------------------------

open import Specification

module PTS (𝕊 : Spec) where

open import Data.Nat using (ℕ; suc; pred; _≤?_; _≟_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

-------------------------------------------------------------------------------
-- Grammar (with explicit sort annotations)

infix 30 s_
infix 22 ƛ_·_
infix 22 Π_·_
infix 22 _§_
data 𝕋 : Set where
  s_ : Spec.Sort 𝕊 → 𝕋
  f⟨_♯_⟩ : ℕ → Spec.Sort 𝕊 → 𝕋
  b⟨_⟩ : ℕ → 𝕋
  ƛ_·_ : 𝕋 → 𝕋 → 𝕋
  Π_·_ : 𝕋 → 𝕋 → 𝕋
  _§_ : 𝕋 → 𝕋 → 𝕋

-------------------------------------------------------------------------------
-- Substitution and Lifting

infix 25 _[_/_]
_[_/_] : 𝕋 → 𝕋 → ℕ → 𝕋
s i [ n / y ] = s i
f⟨ x ♯ i ⟩ [ n / y ] with x ≟ y
...                  | yes _ = n
...                  | no _ =  f⟨ x ♯ i ⟩
b⟨ x ⟩ [ n / y ] = b⟨ x ⟩
(ƛ a · m) [ n / y ] = ƛ a [ n / y ] · m [ n / y ]
(Π a · b) [ n / y ] = Π a [ n / y ] · b [ n / y ]
(m₁ § m₂) [ n / y ] = m₁ [ n / y ] § m₂ [ n / y ]


infix 25 _[_]⁰
_[_]⁰ : 𝕋 → 𝕋 → 𝕋
m [ n ]⁰ = m [ n / 0 ]ᵇ where
  _[_/_]ᵇ : 𝕋 → 𝕋 → ℕ → 𝕋
  s i [ n / y ]ᵇ = s i
  f⟨ x ♯ i ⟩ [ n / y ]ᵇ = f⟨ x ♯ i ⟩
  b⟨ x ⟩ [ n / y ]ᵇ with x ≟ y
  ...               | yes _ = n
  ...               | no _ = b⟨ x ⟩
  (ƛ a · m) [ n / y ]ᵇ = ƛ a [ n / y ]ᵇ · (m [ n / suc y ]ᵇ)
  (Π a · b) [ n / y ]ᵇ = Π a [ n / y ]ᵇ · (b [ n / suc y ]ᵇ)
  (m₁ § m₂) [ n / y ]ᵇ = (m₁ [ n / y ]ᵇ) § (m₂ [ n / y ]ᵇ)

-------------------------------------------------------------------------------
-- β-Reduction

infix 15 _⟶ᵇ_
data _⟶ᵇ_ : 𝕋 → 𝕋 → Set where
  β-rule : ∀ {a m n} →
    (ƛ a · m) § n ⟶ᵇ m [ n ]⁰
  comp-pi₁ : ∀ {a b a'} →
    a ⟶ᵇ a' →
    Π a · b ⟶ᵇ Π a · b
  comp-pi₂ : ∀ {a b b'} →
    b ⟶ᵇ b' →
    Π a · b ⟶ᵇ Π a · b'
  comp-lam₁ : ∀ {a b a'} →
    a ⟶ᵇ a' →
    ƛ a · b ⟶ᵇ ƛ a' · b
  comp-lam₂ : ∀ {a b b'} →
    b ⟶ᵇ b' →
    ƛ a · b ⟶ᵇ ƛ a · b'
  comp-app₁ : ∀ {a b a'} →
    a ⟶ᵇ a' →
    a § b ⟶ᵇ a' § b
  comp-app₂ : ∀ {a b b'} →
    b ⟶ᵇ b' →
    a § b ⟶ᵇ a § b'

data _↠ᵇ_ : 𝕋 → 𝕋 → Set where
  β-refl : ∀ {m} → m ↠ᵇ m
  β-step : ∀ {m n n'} → m ⟶ᵇ n → n ↠ᵇ n' → m ↠ᵇ n'

↠ᵇ-trans : ∀ {m n p} →
  m ↠ᵇ n →
  n ↠ᵇ p →
  m ↠ᵇ p
↠ᵇ-trans β-refl np = np
↠ᵇ-trans (β-step mn nn') np = β-step mn (↠ᵇ-trans nn' np)

data _=ᵇ_ : 𝕋 → 𝕋 → Set where
  =ᵇ-refl : ∀ {m n} → m ↠ᵇ n → m =ᵇ n
  =ᵇ-sym : ∀ {m n} → m =ᵇ n → n =ᵇ m
  =ᵇ-trans : ∀ {m n p} → m =ᵇ n → n =ᵇ p → m =ᵇ p

-------------------------------------------------------------------------------
-- Contexts

infix 22 _,_∷_
data ℂ : Set where
  ∅ : ℂ
  _,_∷_ : ℂ → ℕ → 𝕋 → ℂ

data _∉_ : ℕ → ℂ → Set where
  ∉∅ : ∀ {x} → x ∉ ∅
  ∉Γ : ∀ {x y Γ a} →
    x ∉ Γ →
    x ≢ y →
    x ∉ (Γ , y ∷ a)

infix 25 _[_/_]ᶜ
_[_/_]ᶜ : ℂ → 𝕋 → ℕ → ℂ
∅ [ _ / _ ]ᶜ = ∅
(Γ , x ∷ a) [ n / y ]ᶜ = Γ [ n / y ]ᶜ , x ∷ a [ n / y ]


infix 25 _∘_
_∘_ : ℂ → ℂ → ℂ
Γ ∘ ∅ = Γ
Γ ∘ (Δ , x ∷ a) = Γ ∘ Δ , x ∷ a

-------------------------------------------------------------------------------
-- Typing Inference

data _⊢_∷_ : ℂ → 𝕋 → 𝕋 → Set₁ where
  axiom : ∀ {i j} → Spec.axiom 𝕊 i j →
    -----------------------------------
    ∅ ⊢ s i ∷ s j

  var-intro : ∀ {x i Γ a} → x ∉ Γ →
    Γ ⊢ a ∷ s i →
    -----------------------------------
    Γ , x ∷ a ⊢ f⟨ x ♯ i ⟩ ∷ a

  sort-weaken : ∀ {x i j k Γ b} → Spec.axiom 𝕊 j k → x ∉ Γ →
    Γ ⊢ b ∷ s i →
    Γ ⊢ s j ∷ s k →
    -----------------------------------
    Γ , x ∷ b ⊢ s j ∷ s k

  var-weaken : ∀ {x y i j Γ a b} →
    y ∉ Γ →
    Γ ⊢ b ∷ s j →
    Γ ⊢ f⟨ x ♯ i ⟩ ∷ a →
    -----------------------------------
    Γ , y ∷ b ⊢ f⟨ x ♯ i ⟩ ∷ a

  pi-intro : ∀ {a i j k Γ b x} → Spec.rule 𝕊 i j k →
    Γ ⊢ a ∷ s i →
    Γ , x ∷ a ⊢ b ∷ s j →
    -----------------------------------
    Γ ⊢ Π a · (b [ b⟨ 0 ⟩ / x ]) ∷ s k

  abstr : ∀ {a i j k Γ m b x} →
    Γ ⊢ a ∷ s i →
    Γ , x ∷ a ⊢ b ∷ s j →
    Spec.rule 𝕊 i j k →
    Γ , x ∷ a ⊢ m ∷ b →
    -----------------------------------
    Γ ⊢ ƛ a · (m [ b⟨ 0 ⟩ / x ]) ∷ Π a · b [ b⟨ 0 ⟩ / x ]

  app : ∀ {Γ m n x a b j} →
    Γ , x ∷ a ⊢ b ∷ s j →
    Γ ⊢ m ∷ Π a · b [ b⟨ 0 ⟩ / x ] →
    Γ ⊢ n ∷ a →
    -----------------------------------
    Γ ⊢ m § n ∷ b [ n / x ]

  conv-red : ∀ {i Γ m a b} →
    Γ ⊢ m ∷ a →
    Γ ⊢ b ∷ s i →
    a ↠ᵇ b →
    ----------------------------------- 
    Γ ⊢ m ∷ b
  
  conv-exp : ∀ {i Γ m a b} →
    Γ ⊢ m ∷ a →
    Γ ⊢ b ∷ s i →
    b ↠ᵇ a →
    -----------------------------------
    Γ ⊢ m ∷ b

_⊬_∷_ : ℂ → 𝕋 → 𝕋 → Set₁
Γ ⊬ m ∷ a = ¬ (Γ ⊢ m ∷ a)

-------------------------------------------------------------------------------
-- Well-formed Context

data WFC : ℂ → Set₁ where
  ∅-wf : WFC ∅
  ext-wf : ∀ {x i Γ a} →
    x ∉ Γ →
    Γ ⊢ a ∷ s i →
    WFC Γ →
    WFC (Γ , x ∷ a)
