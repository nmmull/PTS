-------------------------------------------------------------------------------
-- Pure Type Systems
--
-------------------------------------------------------------------------------

open import Specification

module PTS (𝕊 : Spec) where

open import Data.Nat using (ℕ; suc; pred; _≤?_; _≟_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; ≢-sym)
open import Data.Product using (_×_; _,_)

-------------------------------------------------------------------------------
-- Grammar (with explicit sort annotations)

infix 30 s_
infix 22 ƛ_·_
infix 22 Π_·_
infix 22 _§_
data 𝕋 : Set where
  s_ : Spec.Sort 𝕊 → 𝕋
  f⟨_⟩ : ℕ → 𝕋
  b⟨_⟩ : ℕ → 𝕋
  ƛ_·_ : 𝕋 → 𝕋 → 𝕋
  Π_·_ : 𝕋 → 𝕋 → 𝕋
  _§_ : 𝕋 → 𝕋 → 𝕋

-------------------------------------------------------------------------------
-- Substitution and Lifting

infix 25 _[_/_]
_[_/_] : 𝕋 → 𝕋 → ℕ → 𝕋
s i [ n / y ] = s i
f⟨ x ⟩ [ n / y ] with x ≟ y
...                  | yes _ = n
...                  | no _ =  f⟨ x ⟩
b⟨ x ⟩ [ n / y ] = b⟨ x ⟩
(ƛ a · m) [ n / y ] = ƛ a [ n / y ] · m [ n / y ]
(Π a · b) [ n / y ] = Π a [ n / y ] · b [ n / y ]
(m₁ § m₂) [ n / y ] = m₁ [ n / y ] § m₂ [ n / y ]


infix 25 _[_]⁰
_[_]⁰ : 𝕋 → 𝕋 → 𝕋
m [ n ]⁰ = m [ n / 0 ]ᵇ where
  _[_/_]ᵇ : 𝕋 → 𝕋 → ℕ → 𝕋
  s i [ n / y ]ᵇ = s i
  f⟨ x ⟩ [ n / y ]ᵇ = f⟨ x ⟩
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

infix 25 _[_/_]ᶜ
_[_/_]ᶜ : ℂ → 𝕋 → ℕ → ℂ
∅ [ _ / _ ]ᶜ = ∅
(Γ , x ∷ a) [ n / y ]ᶜ = Γ [ n / y ]ᶜ , x ∷ a [ n / y ]


infix 25 _∘_
_∘_ : ℂ → ℂ → ℂ
Γ ∘ ∅ = Γ
Γ ∘ (Δ , x ∷ a) = Γ ∘ Δ , x ∷ a

∘-id-l : ∀ {Γ} → Γ ≡ ∅ ∘ Γ
∘-id-l {∅} = refl
∘-id-l {Γ , x ∷ a} = cong (λ Δ → Δ , x ∷ a) ∘-id-l

data _∈_ : (ℕ × 𝕋) → ℂ → Set where
  ∈-base : ∀ {Γ x a} →
    (x , a) ∈ (Γ , x ∷ a)
  ∈-ext : ∀ {Γ x a y b} →
    (x , a) ∈ Γ → (x , a) ∈ (Γ , y ∷ b)

data _∉_ : ℕ → ℂ → Set where
  ∉∅ : ∀ {x} → x ∉ ∅
  ∉Γ : ∀ {x y Γ a} →
    x ∉ Γ →
    x ≢ y →
    x ∉ (Γ , y ∷ a)

∉-thinning : ∀ {Γ Δ x z a b} →
  z ∉ Γ ∘ Δ , x ∷ a →
  x ∉ Γ ∘ Δ →
  x ∉ (Γ , z ∷ b) ∘ Δ
∉-thinning {Δ = ∅} (∉Γ z∉Γx z≢x) x∉Γ = ∉Γ x∉Γ (≢-sym z≢x)
∉-thinning {Δ = Δ , y ∷ c} {a = a} (∉Γ (∉Γ z∉ΓΔ _) z≢x) (∉Γ x∉ΓΔ x≢y) =
  ∉Γ (∉-thinning {a = a} (∉Γ z∉ΓΔ z≢x) x∉ΓΔ) x≢y

∉-weaken : ∀ {Γ x z a b} →
  z ∉ Γ , x ∷ a →
  x ∉ Γ →
  x ∉ Γ , z ∷ b
∉-weaken z∉Γx x∉Γ = ∉-thinning {Δ = ∅} z∉Γx x∉Γ

∉-strengthen-gen : ∀ {Γ Δ x z a} →
  z ∉ (Γ , x ∷ a) ∘ Δ →
  z ∉ Γ ∘ Δ
∉-strengthen-gen {Δ = ∅} (∉Γ z∉Γ _) = z∉Γ
∉-strengthen-gen {Δ = Δ , _ ∷ _} (∉Γ z∉ΓxΔ z≢x) = ∉Γ (∉-strengthen-gen z∉ΓxΔ) z≢x

∉-strengthen : ∀ {Γ z x a} →
  z ∉ Γ , x ∷ a →
  z ∉ Γ
∉-strengthen (∉Γ z∉Γ _) = z∉Γ

∉-to-≢ : ∀ {Γ Δ x y a} →
  x ∉ (Γ , y ∷ a) ∘ Δ →
  x ≢ y
∉-to-≢ {Δ = ∅} (∉Γ _ x≢y) = x≢y
∉-to-≢ {Δ = Δ , z ∷ c} (∉Γ x∉ΓyΔ _) = ∉-to-≢ x∉ΓyΔ

-------------------------------------------------------------------------------
-- Typing Rules

data _⊢_∷_ : ℂ → 𝕋 → 𝕋 → Set₁ where
  axiom : ∀ {i j} → Spec.axiom 𝕊 i j →
    -----------------------------------
    ∅ ⊢ s i ∷ s j

  var-intro : ∀ {x i Γ a} → x ∉ Γ →
    Γ ⊢ a ∷ s i →
    -----------------------------------
    Γ , x ∷ a ⊢ f⟨ x ⟩ ∷ a

  sort-weaken : ∀ {x i j k Γ b} → Spec.axiom 𝕊 j k → x ∉ Γ →
    Γ ⊢ b ∷ s i →
    Γ ⊢ s j ∷ s k →
    -----------------------------------
    Γ , x ∷ b ⊢ s j ∷ s k

  var-weaken : ∀ {x y j Γ a b} →
    y ∉ Γ →
    Γ ⊢ b ∷ s j →
    Γ ⊢ f⟨ x ⟩ ∷ a →
    -----------------------------------
    Γ , y ∷ b ⊢ f⟨ x ⟩ ∷ a

  pi-intro : ∀ {a i j k Γ b} → Spec.rule 𝕊 i j k →
    Γ ⊢ a ∷ s i →
    (∀ {x} → x ∉ Γ → Γ , x ∷ a ⊢ b [ f⟨ x ⟩ ]⁰ ∷ s j) →
    -----------------------------------
    Γ ⊢ Π a · b ∷ s k

  abstr : ∀ {a i j k Γ m b} → Spec.rule 𝕊 i j k →
    Γ ⊢ a ∷ s i →
    (∀ {x} → x ∉ Γ → Γ , x ∷ a ⊢ b [ f⟨ x ⟩ ]⁰ ∷ s j) →
    (∀ {x} → x ∉ Γ → Γ , x ∷ a ⊢ m [ f⟨ x ⟩ ]⁰ ∷ s j) →
    -----------------------------------
    Γ ⊢ ƛ a · m ∷ Π a · b

  app : ∀ {Γ m n a b} →
    Γ ⊢ m ∷ Π a · b →
    Γ ⊢ n ∷ a →
    -----------------------------------
    Γ ⊢ m § n ∷ b [ n ]⁰

  conv-red : ∀ {i Γ m a b} →
    Γ ⊢ m ∷ a →
    Γ ⊢ b ∷ s i →
    a ⟶ᵇ b →
    -----------------------------------
    Γ ⊢ m ∷ b

  conv-exp : ∀ {i Γ m a b} →
    Γ ⊢ m ∷ a →
    Γ ⊢ b ∷ s i →
    b ⟶ᵇ a →
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

-------------------------------------------------------------------------------
-- Start

start-sort : ∀ {Γ i j} →
  Spec.axiom 𝕊 i j →
  WFC Γ →
  Γ ⊢ s i ∷ s j
start-sort ax ∅-wf = axiom ax
start-sort ax (ext-wf x∉Γ Γ⊢as Γ-wf) = sort-weaken ax x∉Γ Γ⊢as (start-sort ax Γ-wf)

start-var : ∀ {Γ x a} →
  WFC Γ →
  (x , a) ∈ Γ →
  Γ ⊢ f⟨ x ⟩ ∷ a
start-var (ext-wf {i = i} x∉Γ Γ⊢a Γ-wf) ∈-base = var-intro x∉Γ Γ⊢a
start-var {x = x} {a = a} (ext-wf {Γ = Γ} y∉Γ  Γ⊢b Γ-wf) (∈-ext x∈Γ) = var-weaken y∉Γ Γ⊢b (start-var Γ-wf x∈Γ)

-------------------------------------------------------------------------------
-- Thinning

thinning : ∀ {Γ Δ m a b x i} →
  x ∉ Γ ∘ Δ →
  Γ ⊢ b ∷ s i →
  Γ ∘ Δ ⊢ m ∷ a →
  (Γ , x ∷ b) ∘ Δ ⊢ m ∷ a
thinning {Δ = ∅} x∉ΓΔ Γ⊢b (axiom ax) = sort-weaken ax ∉∅ Γ⊢b (axiom ax)
thinning {Δ = ∅} x∉Γ Γx⊢b (var-intro y∉Γ Γ⊢a) = var-weaken x∉Γ Γx⊢b (var-intro y∉Γ Γ⊢a)
thinning {Δ = ∅} x∉ΓΔ Γ⊢b (sort-weaken {b = c} ax x∉Γ Γ⊢c Γ⊢s) = sort-weaken ax x∉ΓΔ Γ⊢b (sort-weaken ax x∉Γ Γ⊢c Γ⊢s)
thinning {Δ = ∅} x∉Γy Γy⊢b (var-weaken {b = c} y∉Γ Γ⊢c Γ⊢xa) = var-weaken x∉Γy Γy⊢b (var-weaken y∉Γ Γ⊢c Γ⊢xa)
thinning {Γ = Γ} {Δ = ∅} {x = x} x∉Γ Γ⊢b (pi-intro {a = c} {b = d} rule Γ⊢c Γy⊢d) =
  pi-intro rule
    (thinning x∉Γ Γ⊢b Γ⊢c)
    λ z∉Γx → thinning (∉-weaken z∉Γx x∉Γ) Γ⊢b (Γy⊢d (∉-strengthen z∉Γx))
thinning {Δ = ∅} x∉Γ Γ⊢b (abstr {b = c} rule Γ⊢a Γy⊢c Γy⊢m) =
  abstr rule (thinning x∉Γ Γ⊢b Γ⊢a)
    (λ {z} z∉Γx → thinning (∉-weaken z∉Γx x∉Γ) Γ⊢b (Γy⊢c (∉-strengthen z∉Γx)))
    (λ {z} z∉Γx → thinning (∉-weaken z∉Γx x∉Γ) Γ⊢b (Γy⊢m (∉-strengthen z∉Γx)))
thinning {Δ = ∅} x∉Γ Γ⊢b (app Γ⊢m Γ⊢n) =
  app
    (thinning x∉Γ Γ⊢b Γ⊢m)
    (thinning x∉Γ Γ⊢b Γ⊢n)
thinning {Δ = ∅} x∉Γ Γ⊢b (conv-red Γ⊢m Γ⊢c red) =
  conv-red
    (thinning x∉Γ Γ⊢b Γ⊢m)
    (thinning x∉Γ Γ⊢b Γ⊢c)
    red
thinning {Δ = ∅} x∉Γ Γ⊢b (conv-exp Γ⊢m Γ⊢c exp) =
  conv-exp
    (thinning x∉Γ Γ⊢b Γ⊢m)
    (thinning x∉Γ Γ⊢b Γ⊢c)
    exp
thinning {Δ = Δ , y ∷ b} x∉ΓΔy Γ⊢b (var-intro y∉ΓΔ ΓΔ⊢c) =
  var-intro
    (∉-thinning x∉ΓΔy y∉ΓΔ)
    (thinning (∉-strengthen x∉ΓΔy) Γ⊢b ΓΔ⊢c)
thinning {Δ = Δ , y ∷ b} x∉ΓΔy Γ⊢b (sort-weaken ax y∉ΓΔ ΓΔ⊢c ΓΔ⊢s) =
  sort-weaken ax
    (∉-thinning x∉ΓΔy y∉ΓΔ)
    (thinning (∉-strengthen x∉ΓΔy) Γ⊢b ΓΔ⊢c)
    (thinning (∉-strengthen x∉ΓΔy) Γ⊢b ΓΔ⊢s)
thinning {Δ = Δ , y ∷ b} x∉ΓΔy Γ⊢b (var-weaken y∉ΓΔ ΓΔ⊢c ΓΔ⊢x) =
  var-weaken
    (∉-thinning x∉ΓΔy y∉ΓΔ)
    (thinning (∉-strengthen x∉ΓΔy) Γ⊢b ΓΔ⊢c)
    (thinning (∉-strengthen x∉ΓΔy) Γ⊢b ΓΔ⊢x)
thinning {Γ} {Δ = Δ , y ∷ b} {b = c} x∉ΓΔy Γ⊢b (pi-intro rule ΓΔ⊢a ΓΔyx⊢b) =
  pi-intro rule
    (thinning x∉ΓΔy Γ⊢b ΓΔ⊢a)
    λ {z} z∉ΓxΔy → (thinning
      (∉Γ x∉ΓΔy (≢-sym (∉-to-≢ {Γ = Γ} {Δ = Δ , y ∷ b} {a = c} z∉ΓxΔy)))
      Γ⊢b
      (ΓΔyx⊢b (∉-strengthen-gen {Γ = Γ} z∉ΓxΔy)))
thinning {Γ} {Δ = Δ , y ∷ b} x∉ΓΔy Γ⊢b (abstr rule ⊢a ⊢b ⊢m) =
  abstr
    rule
    (thinning x∉ΓΔy Γ⊢b ⊢a)
    (λ {z} z∉ → thinning
      (∉Γ x∉ΓΔy (≢-sym (∉-to-≢ {Γ = Γ} {Δ = Δ , y ∷ b} z∉)))
      Γ⊢b
      (⊢b {z} (∉-strengthen-gen {Γ = Γ} z∉)))
    λ {z} z∉ → thinning
      (∉Γ x∉ΓΔy (≢-sym (∉-to-≢ {Δ = Δ , y ∷ b} z∉)))
      Γ⊢b
      (⊢m {z} (∉-strengthen-gen {Γ = Γ} z∉))
thinning {Δ = Δ , y ∷ b} x∉ΓΔ Γ⊢b (app ΓΔ⊢m ΓΔ⊢n) =
  app
    (thinning x∉ΓΔ Γ⊢b ΓΔ⊢m)
    (thinning x∉ΓΔ Γ⊢b ΓΔ⊢n)
thinning {Δ = Δ , y ∷ b} x∉ΓΔ Γ⊢b (conv-red ΓΔ⊢m ΓΔ⊢a red) =
  conv-red
    (thinning x∉ΓΔ Γ⊢b ΓΔ⊢m)
    (thinning x∉ΓΔ Γ⊢b ΓΔ⊢a)
    red
thinning {Δ = Δ , y ∷ b} x∉ΓΔ Γ⊢b (conv-exp ΓΔ⊢m ΓΔ⊢a exp) =
  conv-exp
    (thinning x∉ΓΔ Γ⊢b ΓΔ⊢m)
    (thinning x∉ΓΔ Γ⊢b ΓΔ⊢a)
    exp

weakening : ∀ {Γ m a b x i} →
  x ∉ Γ →
  Γ ⊢ b ∷ s i →
  Γ ⊢ m ∷ a →
  Γ , x ∷ b ⊢ m ∷ a
weakening = thinning

-------------------------------------------------------------------------------
-- Substitution

substitution : ∀ {Γ Δ m n a b x} →
  (Γ , x ∷ a) ∘ Δ ⊢ m ∷ b →
  Γ ⊢ n ∷ a →
  Γ ∘ (Δ [ n / x ]ᶜ) ⊢ m [ n / x ] ∷ b [ n / x ]
substitution {Δ = ∅} {x = x} (var-intro {x = y} ∉ ⊢a) ⊢n with x ≟ y
... | yes _ = {!!}
... | no _ = {!!}
substitution {Δ = ∅} (sort-weaken _ _ _ ⊢s) _ = ⊢s
substitution {Δ = ∅} (var-weaken x ⊢m ⊢m₁) ⊢n = {!!}
substitution {Δ = ∅} (pi-intro x ⊢m x₁) ⊢n = {!!}
substitution {Δ = ∅} (abstr x ⊢m x₁ x₂) ⊢n = {!!}
substitution {Δ = ∅} (app ⊢m ⊢m₁) ⊢n = {!!}
substitution {Δ = ∅} (conv-red ⊢m ⊢m₁ x) ⊢n = {!!}
substitution {Δ = ∅} (conv-exp ⊢m ⊢m₁ x) ⊢n = {!!}
substitution {Δ = Δ , x ∷ x₁} ⊢m ⊢n = {!!}
