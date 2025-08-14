-------------------------------------------------------------------------------
-- Pure Type Systems
--
-------------------------------------------------------------------------------

open import Specification

module PTS (𝒮 : Spec) where

open import Data.Nat using (ℕ; suc; _≟_; _+_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; ≢-sym)
open import Data.Product using (_×_; proj₁; proj₂; _,_; ∃; ∃-syntax; map₂; Σ; Σ-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map)

-------------------------------------------------------------------------------
-- Grammar

infix 30 s_
infix 22 ƛ_·_
infix 22 Π_·_
infix 22 _§_
data 𝕋 : Set where
  s_ : Spec.Sort 𝒮 → 𝕋
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


infix 25 _[_/_]ᵇ
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
    (ƛ a · m) § n ⟶ᵇ m [ n / 0 ]ᵇ
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

-- infix 22 _,_∷_
-- data ℂ : Set where
--   ∅ : ℂ
--   _,_∷_ : ℂ → ℕ → 𝕋 → ℂ

-- infix 25 _[_/_]ᶜ
-- _[_/_]ᶜ : ℂ → 𝕋 → ℕ → ℂ
-- ∅ [ _ / _ ]ᶜ = ∅
-- (Γ , x ∷ a) [ n / y ]ᶜ = Γ [ n / y ]ᶜ , x ∷ a [ n / y ]


-- infix 25 _∘_
-- _∘_ : ℂ → ℂ → ℂ
-- Γ ∘ ∅ = Γ
-- Γ ∘ (Δ , x ∷ a) = Γ ∘ Δ , x ∷ a

-- ∘-id-l : ∀ {Γ} → Γ ≡ ∅ ∘ Γ
-- ∘-id-l {∅} = refl
-- ∘-id-l {Γ , x ∷ a} = cong (λ Δ → Δ , x ∷ a) ∘-id-l

-- data _∈_ : (ℕ × 𝕋) → ℂ → Set where
--   ∈-base : ∀ {Γ x a} →
--     (x , a) ∈ (Γ , x ∷ a)
--   ∈-ext : ∀ {Γ x a y b} →
--     (x , a) ∈ Γ → (x , a) ∈ (Γ , y ∷ b)

infix 4 _∉_
data _∉_ : ℕ → List (ℕ × 𝕋) → Set where
  ∉∅ : ∀ {x} → x ∉ []
  ∉Γ : ∀ {x y Γ a} →
    x ∉ Γ →
    x ≢ y →
    x ∉ (y , a) ∷ Γ

-- ∉-thinning : ∀ {Γ Δ x z a b} →
--   z ∉ Γ ∘ Δ , x ∷ a →
--   x ∉ Γ ∘ Δ →
--   x ∉ (Γ , z ∷ b) ∘ Δ
-- ∉-thinning {Δ = ∅} (∉Γ z∉Γx z≢x) x∉Γ = ∉Γ x∉Γ (≢-sym z≢x)
-- ∉-thinning {Δ = Δ , y ∷ c} {a = a} (∉Γ (∉Γ z∉ΓΔ _) z≢x) (∉Γ x∉ΓΔ x≢y) =
--   ∉Γ (∉-thinning {a = a} (∉Γ z∉ΓΔ z≢x) x∉ΓΔ) x≢y

-- ∉-weaken : ∀ {Γ x z a b} →
--   z ∉ Γ , x ∷ a →
--   x ∉ Γ →
--   x ∉ Γ , z ∷ b
-- ∉-weaken z∉Γx x∉Γ = ∉-thinning {Δ = ∅} z∉Γx x∉Γ

-- ∉-strengthen-gen : ∀ {Γ Δ x z a} →
--   z ∉ (Γ , x ∷ a) ∘ Δ →
--   z ∉ Γ ∘ Δ
-- ∉-strengthen-gen {Δ = ∅} (∉Γ z∉Γ _) = z∉Γ
-- ∉-strengthen-gen {Δ = Δ , _ ∷ _} (∉Γ z∉ΓxΔ z≢x) = ∉Γ (∉-strengthen-gen z∉ΓxΔ) z≢x

-- ∉-strengthen : ∀ {Γ z x a} →
--   z ∉ Γ , x ∷ a →
--   z ∉ Γ
-- ∉-strengthen (∉Γ z∉Γ _) = z∉Γ

-- ∉-to-≢ : ∀ {Γ Δ x y a} →
--   x ∉ (Γ , y ∷ a) ∘ Δ →
--   x ≢ y
-- ∉-to-≢ {Δ = ∅} (∉Γ _ x≢y) = x≢y
-- ∉-to-≢ {Δ = Δ , z ∷ c} (∉Γ x∉ΓyΔ _) = ∉-to-≢ x∉ΓyΔ

-- -- fresh : ℂ → ℕ
-- -- fresh ∅ = 1
-- -- fresh (Γ , x ∷ _) = x + fresh Γ

-- -- fresh-is-fresh : ∀ {Γ} → fresh Γ ∉ Γ
-- -- fresh-is-fresh {∅} = ∉∅
-- -- fresh-is-fresh {Γ , x ∷ _} = {!!}

-- fresh : ∀ Γ → ∃[ x ] x ∉ Γ
-- fresh = {!!}

-- -------------------------------------------------------------------------------
-- -- Typing Rules

infix 3 _⊢_
data _⊢_ : (List 𝕋 × List (ℕ × 𝕋)) → 𝕋 × 𝕋 → Set₁ where
  axiom : ∀ {i j} → Spec.axiom 𝒮 i j →
    [] , [] ⊢ s i , s j

  fvar-intro : ∀ {x i Γ a} → x ∉ Γ →
    [] , Γ ⊢ a , s i →
    [] , (x , a) ∷ Γ ⊢ f⟨ x ⟩ , a

  bvar-intro : ∀ {i Γ₁ Γ₂ a} →
    Γ₁ , Γ₂ ⊢ a , s i →
    a ∷ Γ₁ , Γ₂ ⊢ b⟨ 0 ⟩ , a

  sort-weaken : ∀ {x i j k Γ₁ Γ₂ b} → Spec.axiom 𝒮 j k → x ∉ Γ₂ →
    Γ₁ , Γ₂ ⊢ b , s i →
    Γ₁ , Γ₂ ⊢ s j , s k →
    Γ₁ , (x , b) ∷ Γ₂ ⊢ s j , s k

  var-weaken : ∀ {x y j Γ₁ Γ₂ a b} → y ∉ Γ₂ →
    Γ₁ , Γ₂ ⊢ b , s j →
    Γ₁ , Γ₂ ⊢ f⟨ x ⟩ , a →
    Γ₁ , (y , b) ∷ Γ₂ ⊢ f⟨ x ⟩ , a

  pi-intro : ∀ {a i j k Γ₁ Γ₂ b} → Spec.rule 𝒮 i j k →
    Γ₁ , Γ₂ ⊢ a , s i →
    a ∷ Γ₁ , Γ₂ ⊢ b , s j →
    Γ₁ , Γ₂ ⊢ Π a · b , s k

  abstr : ∀ {a i j k Γ₁ Γ₂ m b} → Spec.rule 𝒮 i j k →
    Γ₁ , Γ₂ ⊢ a , s i →
    a ∷ Γ₁ , Γ₂ ⊢ b , s j →
    a ∷ Γ₁ , Γ₂ ⊢ m , b →
    Γ₁ , Γ₂ ⊢ ƛ a · m , Π a · b

  app : ∀ {Γ m n a b} →
    Γ ⊢ m , Π a · b →
    Γ ⊢ n , a →
    Γ ⊢ m § n , b [ n / 0 ]ᵇ

  conv-exp : ∀ {i Γ m a b} →
    Γ ⊢ m , a →
    Γ ⊢ b , s i →
    a ⟶ᵇ b →
    Γ ⊢ m , b

  conv-red : ∀ {i Γ m a b} →
    Γ ⊢ m , a →
    Γ ⊢ b , s i →
    b ⟶ᵇ a →
    Γ ⊢ m , b

subst-noop : ∀ {Γ₁ Γ₂ m a x n} →
  Γ₁ , Γ₂ ⊢ m , a →
  x ∉ Γ₂ →
  m [ n / x ] ≡ m
subst-noop (axiom _) _ = refl
subst-noop {x = y} (fvar-intro {x = x} _ ⊢) x∉Γy with x ≟ y
subst-noop {x = y} (fvar-intro _ _) (∉Γ _ y≢x) | yes x≡y = ⊥-elim (y≢x (sym (x≡y)))
... | no _ = refl
subst-noop (sort-weaken _ _ _ _) _ = refl
subst-noop {x = y} (var-weaken {x = x} {y = z} z∉Γ Γ⊢b Γ⊢x) (∉Γ y∉Γ _) = subst-noop Γ⊢x y∉Γ
subst-noop {n = n} (pi-intro _ Γ⊢a Γa⊢b) x∉Γ
  rewrite subst-noop {n = n} Γ⊢a x∉Γ
  rewrite subst-noop {n = n} Γa⊢b x∉Γ = refl
subst-noop {n = n} (abstr _ Γ⊢a _ Γa⊢m) x∉Γ
  rewrite subst-noop {n = n} Γ⊢a x∉Γ
  rewrite subst-noop {n = n} Γa⊢m x∉Γ = refl
subst-noop {n = n} (app Γ⊢m Γ⊢n) x∉Γ
  rewrite subst-noop {n = n} Γ⊢m x∉Γ
  rewrite subst-noop {n = n} Γ⊢n x∉Γ = refl
subst-noop (conv-exp Γ⊢m _ _) x∉Γ = subst-noop Γ⊢m x∉Γ
subst-noop (conv-red Γ⊢m _ _) x∉Γ = subst-noop Γ⊢m x∉Γ

substitution : ∀ {Γ Δ₁ Δ₂ m n a b x} →
  Γ , Δ₂ ++ (x , a) ∷ Δ₁ ⊢ m , b →
  Γ , Δ₁ ⊢ n , a →
  Γ , (map (λ (x , t) → (x , t [ n / x ])) Δ₂) ++ Δ₁ ⊢ m [ n / x ] , b [ n / x ]
substitution {Δ₂ = []} {n = n} {x = x} (fvar-intro {x = y} y∉Δ₁ ⊢a) ⊢n with x ≟ y
... | yes _ rewrite subst-noop {n = n} ⊢a y∉Δ₁ = ⊢n
... | no x≢x = ⊥-elim (x≢x refl)
substitution {Δ₂ = []} (sort-weaken _ _ _ ⊢s) _ = ⊢s
substitution {Δ₂ = []} {x = x} (var-weaken {x = y} x∉Δ₁ ⊢a ⊢y) ⊢n with y ≟ x
... | yes _ = {!!} -- contradiction
... | no _ = {!!} -- typing
substitution {Δ₂ = []} (pi-intro x ⊢m ⊢m₁) ⊢n = {!!}
substitution {Δ₂ = []} (abstr x ⊢m ⊢m₁ ⊢m₂) ⊢n = {!!}
substitution {Δ₂ = []} (app ⊢m ⊢m₁) ⊢n = {!!}
substitution {Δ₂ = []} (conv-exp ⊢m ⊢m₁ x) ⊢n = {!!}
substitution {Δ₂ = []} (conv-red ⊢m ⊢m₁ x) ⊢n = {!!}
substitution {Δ₂ = _ ∷ _} ⊢m ⊢n = {!!}

-- data _⊢_∷_ : ℂ → 𝕋 → 𝕋 → Set₁ where
--   axiom : ∀ {i j} → Spec.axiom 𝒮 i j →
--     -----------------------------------
--     ∅ ⊢ s i ∷ s j

--   var-intro : ∀ {x i Γ a} → x ∉ Γ →
--     Γ ⊢ a ∷ s i →
--     -----------------------------------
--     Γ , x ∷ a ⊢ f⟨ x ⟩ ∷ a

--   sort-weaken : ∀ {x i j k Γ b} → Spec.axiom 𝒮 j k → x ∉ Γ →
--     Γ ⊢ b ∷ s i →
--     Γ ⊢ s j ∷ s k →
--     -----------------------------------
--     Γ , x ∷ b ⊢ s j ∷ s k

--   var-weaken : ∀ {x y j Γ a b} →
--     y ∉ Γ →
--     Γ ⊢ b ∷ s j →
--     Γ ⊢ f⟨ x ⟩ ∷ a →
--     -----------------------------------
--     Γ , y ∷ b ⊢ f⟨ x ⟩ ∷ a

--   pi-intro : ∀ {a i j k Γ b} → Spec.rule 𝒮 i j k →
--     Γ ⊢ a ∷ s i →
--     (∀ {x} → x ∉ Γ → Γ , x ∷ a ⊢ b [ f⟨ x ⟩ ]⁰ ∷ s j) →
--     -----------------------------------
--     Γ ⊢ Π a · b ∷ s k

--   abstr : ∀ {a i j k Γ m b} → Spec.rule 𝒮 i j k →
--     Γ ⊢ a ∷ s i →
--     (∀ {x} → x ∉ Γ → Γ , x ∷ a ⊢ b [ f⟨ x ⟩ ]⁰ ∷ s j) →
--     (∀ {x} → x ∉ Γ → Γ , x ∷ a ⊢ m [ f⟨ x ⟩ ]⁰ ∷ b [ f⟨ x ⟩ ]⁰) →
--     -----------------------------------
--     Γ ⊢ ƛ a · m ∷ Π a · b

--   app : ∀ {Γ m n a b} →
--     Γ ⊢ m ∷ Π a · b →
--     Γ ⊢ n ∷ a →
--     -----------------------------------
--     Γ ⊢ m § n ∷ b [ n ]⁰

--   conv-red : ∀ {i Γ m a b} →
--     Γ ⊢ m ∷ a →
--     Γ ⊢ b ∷ s i →
--     a ⟶ᵇ b →
--     -----------------------------------
--     Γ ⊢ m ∷ b

--   conv-exp : ∀ {i Γ m a b} →
--     Γ ⊢ m ∷ a →
--     Γ ⊢ b ∷ s i →
--     b ⟶ᵇ a →
--     -----------------------------------
--     Γ ⊢ m ∷ b

-- _⊬_∷_ : ℂ → 𝕋 → 𝕋 → Set₁
-- Γ ⊬ m ∷ a = ¬ (Γ ⊢ m ∷ a)

-- -------------------------------------------------------------------------------
-- -- Well-formed Context

-- data WFC : ℂ → Set₁ where
--   ∅-wf : WFC ∅
--   ext-wf : ∀ {x i Γ a} →
--     x ∉ Γ →
--     Γ ⊢ a ∷ s i →
--     WFC Γ →
--     WFC (Γ , x ∷ a)

-- -------------------------------------------------------------------------------
-- -- Start

-- start-sort : ∀ {Γ i j} →
--   Spec.axiom 𝒮 i j →
--   WFC Γ →
--   Γ ⊢ s i ∷ s j
-- start-sort ax ∅-wf = axiom ax
-- start-sort ax (ext-wf x∉Γ Γ⊢as Γ-wf) = sort-weaken ax x∉Γ Γ⊢as (start-sort ax Γ-wf)

-- start-var : ∀ {Γ x a} →
--   WFC Γ →
--   (x , a) ∈ Γ →
--   Γ ⊢ f⟨ x ⟩ ∷ a
-- start-var (ext-wf {i = i} x∉Γ Γ⊢a Γ-wf) ∈-base = var-intro x∉Γ Γ⊢a
-- start-var {x = x} {a = a} (ext-wf {Γ = Γ} y∉Γ  Γ⊢b Γ-wf) (∈-ext x∈Γ) = var-weaken y∉Γ Γ⊢b (start-var Γ-wf x∈Γ)

-- -------------------------------------------------------------------------------
-- -- Thinning

-- thinning : ∀ {Γ Δ m a b x i} →
--   x ∉ Γ ∘ Δ →
--   Γ ⊢ b ∷ s i →
--   Γ ∘ Δ ⊢ m ∷ a →
--   (Γ , x ∷ b) ∘ Δ ⊢ m ∷ a
-- thinning {Δ = ∅} x∉ΓΔ Γ⊢b (axiom ax) = sort-weaken ax ∉∅ Γ⊢b (axiom ax)
-- thinning {Δ = ∅} x∉Γ Γx⊢b (var-intro y∉Γ Γ⊢a) = var-weaken x∉Γ Γx⊢b (var-intro y∉Γ Γ⊢a)
-- thinning {Δ = ∅} x∉ΓΔ Γ⊢b (sort-weaken {b = c} ax x∉Γ Γ⊢c Γ⊢s) = sort-weaken ax x∉ΓΔ Γ⊢b (sort-weaken ax x∉Γ Γ⊢c Γ⊢s)
-- thinning {Δ = ∅} x∉Γy Γy⊢b (var-weaken {b = c} y∉Γ Γ⊢c Γ⊢xa) = var-weaken x∉Γy Γy⊢b (var-weaken y∉Γ Γ⊢c Γ⊢xa)
-- thinning {Γ = Γ} {Δ = ∅} {x = x} x∉Γ Γ⊢b (pi-intro {a = c} {b = d} rule Γ⊢c Γy⊢d) =
--   pi-intro rule
--     (thinning x∉Γ Γ⊢b Γ⊢c)
--     λ z∉Γx → thinning (∉-weaken z∉Γx x∉Γ) Γ⊢b (Γy⊢d (∉-strengthen z∉Γx))
-- thinning {Δ = ∅} x∉Γ Γ⊢b (abstr {b = c} rule Γ⊢a Γy⊢c Γy⊢m) =
--   abstr rule (thinning x∉Γ Γ⊢b Γ⊢a)
--     (λ {z} z∉Γx → thinning (∉-weaken z∉Γx x∉Γ) Γ⊢b (Γy⊢c (∉-strengthen z∉Γx)))
--     (λ {z} z∉Γx → thinning (∉-weaken z∉Γx x∉Γ) Γ⊢b (Γy⊢m (∉-strengthen z∉Γx)))
-- thinning {Δ = ∅} x∉Γ Γ⊢b (app Γ⊢m Γ⊢n) =
--   app
--     (thinning x∉Γ Γ⊢b Γ⊢m)
--     (thinning x∉Γ Γ⊢b Γ⊢n)
-- thinning {Δ = ∅} x∉Γ Γ⊢b (conv-red Γ⊢m Γ⊢c red) =
--   conv-red
--     (thinning x∉Γ Γ⊢b Γ⊢m)
--     (thinning x∉Γ Γ⊢b Γ⊢c)
--     red
-- thinning {Δ = ∅} x∉Γ Γ⊢b (conv-exp Γ⊢m Γ⊢c exp) =
--   conv-exp
--     (thinning x∉Γ Γ⊢b Γ⊢m)
--     (thinning x∉Γ Γ⊢b Γ⊢c)
--     exp
-- thinning {Δ = Δ , y ∷ b} x∉ΓΔy Γ⊢b (var-intro y∉ΓΔ ΓΔ⊢c) =
--   var-intro
--     (∉-thinning x∉ΓΔy y∉ΓΔ)
--     (thinning (∉-strengthen x∉ΓΔy) Γ⊢b ΓΔ⊢c)
-- thinning {Δ = Δ , y ∷ b} x∉ΓΔy Γ⊢b (sort-weaken ax y∉ΓΔ ΓΔ⊢c ΓΔ⊢s) =
--   sort-weaken ax
--     (∉-thinning x∉ΓΔy y∉ΓΔ)
--     (thinning (∉-strengthen x∉ΓΔy) Γ⊢b ΓΔ⊢c)
--     (thinning (∉-strengthen x∉ΓΔy) Γ⊢b ΓΔ⊢s)
-- thinning {Δ = Δ , y ∷ b} x∉ΓΔy Γ⊢b (var-weaken y∉ΓΔ ΓΔ⊢c ΓΔ⊢x) =
--   var-weaken
--     (∉-thinning x∉ΓΔy y∉ΓΔ)
--     (thinning (∉-strengthen x∉ΓΔy) Γ⊢b ΓΔ⊢c)
--     (thinning (∉-strengthen x∉ΓΔy) Γ⊢b ΓΔ⊢x)
-- thinning {Γ} {Δ = Δ , y ∷ b} {b = c} x∉ΓΔy Γ⊢b (pi-intro rule ΓΔ⊢a ΓΔyx⊢b) =
--   pi-intro rule
--     (thinning x∉ΓΔy Γ⊢b ΓΔ⊢a)
--     λ {z} z∉ΓxΔy → (thinning
--       (∉Γ x∉ΓΔy (≢-sym (∉-to-≢ {Γ = Γ} {Δ = Δ , y ∷ b} {a = c} z∉ΓxΔy)))
--       Γ⊢b
--       (ΓΔyx⊢b (∉-strengthen-gen {Γ = Γ} z∉ΓxΔy)))
-- thinning {Γ} {Δ = Δ , y ∷ b} x∉ΓΔy Γ⊢b (abstr rule ⊢a ⊢b ⊢m) =
--   abstr
--     rule
--     (thinning x∉ΓΔy Γ⊢b ⊢a)
--     (λ {z} z∉ → thinning
--       (∉Γ x∉ΓΔy (≢-sym (∉-to-≢ {Γ = Γ} {Δ = Δ , y ∷ b} z∉)))
--       Γ⊢b
--       (⊢b {z} (∉-strengthen-gen {Γ = Γ} z∉)))
--     λ {z} z∉ → thinning
--       (∉Γ x∉ΓΔy (≢-sym (∉-to-≢ {Δ = Δ , y ∷ b} z∉)))
--       Γ⊢b
--       (⊢m {z} (∉-strengthen-gen {Γ = Γ} z∉))
-- thinning {Δ = Δ , y ∷ b} x∉ΓΔ Γ⊢b (app ΓΔ⊢m ΓΔ⊢n) =
--   app
--     (thinning x∉ΓΔ Γ⊢b ΓΔ⊢m)
--     (thinning x∉ΓΔ Γ⊢b ΓΔ⊢n)
-- thinning {Δ = Δ , y ∷ b} x∉ΓΔ Γ⊢b (conv-red ΓΔ⊢m ΓΔ⊢a red) =
--   conv-red
--     (thinning x∉ΓΔ Γ⊢b ΓΔ⊢m)
--     (thinning x∉ΓΔ Γ⊢b ΓΔ⊢a)
--     red
-- thinning {Δ = Δ , y ∷ b} x∉ΓΔ Γ⊢b (conv-exp ΓΔ⊢m ΓΔ⊢a exp) =
--   conv-exp
--     (thinning x∉ΓΔ Γ⊢b ΓΔ⊢m)
--     (thinning x∉ΓΔ Γ⊢b ΓΔ⊢a)
--     exp

-- weakening : ∀ {Γ m a b x i} →
--   x ∉ Γ →
--   Γ ⊢ b ∷ s i →
--   Γ ⊢ m ∷ a →
--   Γ , x ∷ b ⊢ m ∷ a
-- weakening = thinning

-- -------------------------------------------------------------------------------
-- -- Substitution

-- helper : ∀ {Γ m a x n} →
--   Γ ⊢ m ∷ a →
--   x ∉ Γ →
--   m [ n / x ] ≡ m
-- helper (axiom _) _ = refl
-- helper {x = y} (var-intro {x = x} _ ⊢) x∉Γy with x ≟ y
-- helper {x = y} (var-intro _ _) (∉Γ _ y≢x) | yes x≡y = ⊥-elim (y≢x (sym (x≡y)))
-- ... | no _ = refl
-- helper (sort-weaken _ _ _ _) _ = refl
-- helper {x = y} (var-weaken {x = x} {y = z} z∉Γ Γ⊢b Γ⊢x) (∉Γ y∉Γ _) = helper Γ⊢x y∉Γ
-- helper {Γ = Γ} {x = y} {n = n} (pi-intro x Γ⊢a Γz⊢b) y∉Γ with fresh Γ
-- helper (pi-intro _ _ Γz⊢b) _ | z , z∉Γ with Γz⊢b z∉Γ
-- helper (pi-intro _ _ _)    _ | z , z∉Γ | _ = {!!}
-- helper (abstr x ⊢ x₁ x₂) ∉ = {!!}
-- helper {n = n} (app Γ⊢m Γ⊢n) x∉Γ
--   rewrite helper {n = n} Γ⊢m x∉Γ
--   rewrite helper {n = n} Γ⊢n x∉Γ = refl
-- helper (conv-red Γ⊢m _ _) x∉Γ = helper Γ⊢m x∉Γ
-- helper (conv-exp Γ⊢m _ _) x∉Γ = helper Γ⊢m x∉Γ

-- substitution : ∀ {Γ Δ m n a b x} →
--   (Γ , x ∷ a) ∘ Δ ⊢ m ∷ b →
--   Γ ⊢ n ∷ a →
--   Γ ∘ (Δ [ n / x ]ᶜ) ⊢ m [ n / x ] ∷ b [ n / x ]
-- substitution {Δ = ∅} {n = n} {x = x} (var-intro {x = y} ∉ ⊢a) ⊢n with x ≟ y
-- ... | yes _ rewrite helper {n = n} ⊢a ∉ = ⊢n
-- ... | no x≢x = ⊥-elim (x≢x refl)
-- substitution {Δ = ∅} (sort-weaken _ _ _ ⊢s) _ = ⊢s
-- substitution {Δ = ∅} (var-weaken x ⊢m ⊢m₁) ⊢n = {!!}
-- substitution {Δ = ∅} (pi-intro x ⊢m x₁) ⊢n = {!!}
-- substitution {Δ = ∅} (abstr x ⊢m x₁ x₂) ⊢n = {!!}
-- substitution {Δ = ∅} (app ⊢m ⊢m₁) ⊢n = {!!}
-- substitution {Δ = ∅} (conv-red ⊢m ⊢m₁ x) ⊢n = {!!}
-- substitution {Δ = ∅} (conv-exp ⊢m ⊢m₁ x) ⊢n = {!!}
-- substitution {Δ = Δ , x ∷ x₁} ⊢m ⊢n = {!!}
