-------------------------------------------------------------------------------
-- Pure Type Systems
--
-------------------------------------------------------------------------------

open import Specification

module PTS (𝕊 : Spec) where

open import Data.Nat using (ℕ; suc; pred; _≤?_)
open import Data.String using (String)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

-------------------------------------------------------------------------------
-- Grammar (with DeBruijn Indices and explicit sort annotations)

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

lift-map : (ℕ → ℕ) → ℕ → 𝕋 → 𝕋
lift-map f = go where
  go : ℕ → 𝕋 → 𝕋
  go x (s i) = s i
  go x ⟨ y ♯ i ⟩ with x ≤? y
  ...            | yes _ = ⟨ y ♯ i ⟩
  ...            | no _ = ⟨ y ♯ i ⟩
  go x (ƛ a · m) = ƛ go x a · go (suc x) m
  go x (Π a · b) = Π go x a · go (suc x) b 
  go x (m § n) = go x m § go x n

↑ : 𝕋 → 𝕋
↑ = lift-map suc 0

↓ : 𝕋 → 𝕋
↓ = lift-map pred 0

infix 25 _[_/_]
_[_/_] : 𝕋 → 𝕋 → ℕ → 𝕋
s i [ n / y ] = s i
⟨ x ♯ i ⟩ [ n / y ] with x Data.Nat.≟ y
...                     | yes _ = n
...                     | no _ =  ⟨ x ♯ i ⟩
(ƛ a · m) [ n / y ] = ƛ a [ n / y ] · m [ ↑ n / suc y ]
(Π a · b) [ n / y ] = Π a [ n / y ] · b [ ↑ n / suc y ]
(m₁ § m₂) [ n / y ] = m₁ [ n / y ] § m₂ [ n / y ]


infix 25 _[_]⁰
_[_]⁰ : 𝕋 → 𝕋 → 𝕋
m [ n ]⁰ = ↓ (m [ ↑ n / 0 ])

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

  var-intro : ∀ {x i Γ a} →
    x ∉ Γ →
    Γ ⊢ a ∷ s i →
    -----------------------------------
    Γ , x ∷ a ⊢ ⟨ x ♯ i ⟩ ∷ a

  sort-weaken : ∀ {x i j k Γ b} →
    Spec.axiom 𝕊 j k →
    x ∉ Γ →
    Γ ⊢ b ∷ s i →
    Γ ⊢ s j ∷ s k →
    -----------------------------------
    Γ , x ∷ b ⊢ s j ∷ s k

  var-weaken : ∀ {x y i j Γ a b} →
    y ∉ Γ →
    Γ ⊢ b ∷ s j →
    Γ ⊢ ⟨ x ♯ i ⟩ ∷ a →
    -----------------------------------
    Γ , y ∷ b ⊢ ⟨ x ♯ i ⟩ ∷ a

  pi-intro : ∀ {a i j k Γ b} →
    Spec.rule 𝕊 i j k →
    Γ ⊢ a ∷ s i →
    (∀ {x} → x ∉ Γ →
      Γ , x ∷ a ⊢ b [ ⟨ x ♯ i ⟩ ]⁰ ∷ s j) →
    -----------------------------------
    Γ ⊢ Π a · b ∷ s k

  abstr : ∀ {a i j Γ m b} →
    Γ ⊢ Π a · b ∷ s j →
    (∀ {x} → x ∉ Γ →
      Γ , x ∷ a ⊢ m [ ⟨ x ♯ i ⟩ ]⁰ ∷ b [ ⟨ x ♯ i ⟩ ]⁰) →
    -----------------------------------
    Γ ⊢ ƛ a · m ∷ Π a · b

  app : ∀ {Γ m n a b c} →
    Γ ⊢ m ∷ Π a · b →
    Γ ⊢ n ∷ a →
    c ≡ b [ n ]⁰ →
    -----------------------------------
    Γ ⊢ m § n ∷ c

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
