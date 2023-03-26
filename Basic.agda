
-------------------------------------------------------------------------------
-- Basic Meta-Theoretic Lemmas
--
-------------------------------------------------------------------------------

-- open import Data.Nat using (ℕ; suc; pred; _≤?_; _<_; _≤_)
-- open import Data.Nat.Properties using (≤∧≢⇒<)
-- open import Utils.Nat using (m≤n⇒m≤1+n; m<n⇒m≢n; 1+n≤m⇒n≤m; m≡n∧m≤p⇒n≤p)
-- open import Relation.Nullary using (yes; no)
-- open import Data.Empty using (⊥; ⊥-elim)
-- open import Relation.Binary.Definitions using (DecidableEquality)
-- open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; _≢_; refl; cong; cong₂; subst; sym; trans; ≢-sym)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
-- open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂; _,_; ∃-syntax; ∃)
-- open import Data.Fin using (Fin)
-- open import Data.String

open import Specification

module Basic (𝕊 : Spec) where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; proj₁; proj₂; _,_; ∃; ∃-syntax; map₂; Σ; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; subst; sym; trans; ≢-sym)
open import Data.Empty using (⊥; ⊥-elim)

open import PTS 𝕊

-------------------------------------------------------------------------------
-- Helpers

Π-not-sort : ∀{a b i} →
  Π a · b ≢ s i
Π-not-sort ()

-------------------------------------------------------------------------------
-- Contexts

∉-thinning : ∀ {Δ x y a Γ} →
  x ∉ (Γ ∘ Δ) →
  x ≢ y →
  x ∉ ((Γ , y ∷ a) ∘ Δ)
∉-thinning {∅} = ∉Γ 
∉-thinning {_ , _ ∷ _} (∉Γ x∉Γ∘Δ x≢z) x≢y = ∉Γ (∉-thinning x∉Γ∘Δ x≢y) x≢z 

∉-strengthen : ∀ {Δ x Γ y a} →
  x ∉ ((Γ , y ∷ a) ∘ Δ) →
  x ∉ (Γ ∘ Δ)
∉-strengthen {∅} (∉Γ x∉Γ _) = x∉Γ
∉-strengthen {Δ , z ∷ b} (∉Γ x∉Γ,y,Δ x≢z) = ∉Γ (∉-strengthen x∉Γ,y,Δ) x≢z 

∉-to-≢ : ∀ {Δ x Γ y a} →
  x ∉ ((Γ , y ∷ a) ∘ Δ) →
  x ≢ y
∉-to-≢ {∅} (∉Γ _ x≢y) = x≢y
∉-to-≢ {Δ , z ∷ b} (∉Γ x∉Γ,y,Δ _) = ∉-to-≢ x∉Γ,y,Δ

{-
data _∉ᵗ_ : ℕ → 𝕋 → Set where
  ∉-s : ∀ {x i} → x ∉ᵗ s i
  ∉-v : ∀ {x y i} → x ≢ y → x ∉ᵗ f⟨ y ♯ i ⟩
  ∉-λ : ∀ {x a m} → x ∉ᵗ a → (suc x) ∉ᵗ m → x ∉ᵗ ƛ a · m
  ∉-Π : ∀ {x a b} → x ∉ᵗ a → (suc x) ∉ᵗ b → x ∉ᵗ Π a · b
  ∉-§ : ∀ {x m n} → x ∉ᵗ m → x ∉ᵗ n → x ∉ᵗ m § n

∉-to-∉ᵗ : ∀ {Γ m a x} →
  Γ ⊢ m ∷ a →
  x ∉ Γ →
  x ∉ᵗ m
∉-to-∉ᵗ (axiom _) _ = ∉-s
∉-to-∉ᵗ (var-intro _ _) x∉Γy = ∉-v (∉-to-≢ {Δ = ∅} x∉Γy)
∉-to-∉ᵗ (sort-weaken _ _ _ _) _ = ∉-s
∉-to-∉ᵗ (var-weaken y∉Γ Γ⊢z _) x∉Γy = ∉-v {!!}
∉-to-∉ᵗ (pi-intro rl Γ⊢a Γy⊢b) x∉Γ = ∉-Π (∉-to-∉ᵗ Γ⊢a x∉Γ) {!!}
∉-to-∉ᵗ (abstr Γ⊢m x) x∉Γ = {!!}
∉-to-∉ᵗ (app Γ⊢m Γ⊢n _) x∉Γ = ∉-§ (∉-to-∉ᵗ Γ⊢m x∉Γ) (∉-to-∉ᵗ Γ⊢n x∉Γ)
∉-to-∉ᵗ (conv-red Γ⊢m _ _) = ∉-to-∉ᵗ Γ⊢m
∉-to-∉ᵗ (conv-exp Γ⊢m _ _) = ∉-to-∉ᵗ Γ⊢m
-}

-------------------------------------------------------------------------------
-- Contexts in Judgments are Well-formed

Γ-wf : ∀ {Γ m a} →
  Γ ⊢ m ∷ a →
  WFC Γ
Γ-wf = {!!}

-------------------------------------------------------------------------------
-- Start Lemma

start : ∀ {Γ i j} →
  Spec.axiom 𝕊 i j →
  WFC Γ →
  Γ ⊢ s i ∷ s j
start i<t ∅-wf = axiom i<t
start i<t (ext-wf fresh a-deriv Γ-wf) = {!!}

-------------------------------------------------------------------------------
-- Thinning
{-
thinning : ∀ {Δ b Γ x a j m} →
  x ∉ (Γ ∘ Δ) →
  Γ ⊢ b ∷ s j →
  (Γ ∘ Δ) ⊢ m ∷ a →
  ((Γ , x ∷ b) ∘ Δ) ⊢ m ∷ a
thinning {∅} x∉ΓΔ Γ⊢b (axiom ax-ij) = sort-weaken ax-ij x∉ΓΔ Γ⊢b (axiom ax-ij)
thinning {∅} x∉ΓΔ Γ⊢b (var-intro y∉ΓΔ ΓΔ⊢c) = var-weaken x∉ΓΔ Γ⊢b (var-intro y∉ΓΔ ΓΔ⊢c) 
thinning {∅} x∉ΓΔ Γ⊢b (sort-weaken ax-ij y∉ΓΔ ΓΔ⊢s ΓΔ⊢c) =
  sort-weaken ax-ij x∉ΓΔ Γ⊢b (sort-weaken ax-ij y∉ΓΔ ΓΔ⊢s ΓΔ⊢c)
thinning {∅} x∉ΓΔ Γ⊢b (var-weaken fr md cd) = var-weaken x∉ΓΔ Γ⊢b (var-weaken fr md cd)
thinning {∅} x∉ΓΔ Γ⊢b (pi-intro {a} rl sd td) = {!!}
--pi-intro rl (thinning x∉ΓΔ Γ⊢b sd)
--  λ { {y} (∉Γ not-in not-eq) → thinning (∉Γ x∉ΓΔ (≢-sym not-eq)) Γ⊢b (td not-in) }
thinning {∅} x∉ΓΔ Γ⊢b m = {!!}
--abstr (thinning x∉ΓΔ Γ⊢b pid)
--  λ { {y} (∉Γ not-in not-eq) → thinning {∅ , y ∷ a} ((∉Γ x∉ΓΔ (≢-sym not-eq))) Γ⊢b (md not-in) }
thinning {∅} x∉ΓΔ Γ⊢b a = ?
thinning {∅} x∉ΓΔ Γ⊢b (conv-red md bd red) =
  conv-red (thinning x∉ΓΔ Γ⊢b md) (thinning x∉ΓΔ Γ⊢b bd) red
thinning {∅} x∉ΓΔ Γ⊢b (conv-exp md bd exp) =
  conv-exp (thinning x∉ΓΔ Γ⊢b md) (thinning x∉ΓΔ Γ⊢b bd) exp
thinning {Δ , y ∷ c} (∉Γ not-in not-eq) Γ⊢b (var-intro fr ad) =
  var-intro (∉-thinning fr (≢-sym not-eq)) (thinning not-in Γ⊢b ad)
thinning {Δ , y ∷ c} (∉Γ x∉ΓΔ x≢y) Γ⊢b (sort-weaken ax-ij y∉ΓΔ ΓΔ⊢c ΓΔ⊢s) = 
  sort-weaken ax-ij
    (∉-thinning y∉ΓΔ (≢-sym x≢y))
    (thinning x∉ΓΔ Γ⊢b ΓΔ⊢c)
    (thinning x∉ΓΔ Γ⊢b ΓΔ⊢s)
thinning {Δ , y ∷ c} (∉Γ x∉ΓΔ x≢y) Γ⊢b (var-weaken y∉ΓΔ ΓΔ⊢c ΓΔ⊢z) = 
  var-weaken
    (∉-thinning y∉ΓΔ (≢-sym x≢y))
    (thinning x∉ΓΔ Γ⊢b ΓΔ⊢c)
    (thinning x∉ΓΔ Γ⊢b ΓΔ⊢z)
thinning {Δ , y ∷ c} x∉ΓΔy Γ⊢b (pi-intro rl ΓΔy⊢a ΓΔyx⊢b) =
  pi-intro rl
    (thinning x∉ΓΔy Γ⊢b ΓΔy⊢a)
    {!!}
    {- λ { {z} (∉Γ z∉ΓxΔ z≢y) →
      thinning
        (∉Γ x∉ΓΔy (≢-sym (∉-to-≢ z∉ΓxΔ)))
        Γ⊢b
        (ΓΔyx⊢b {z} (∉Γ (∉-strengthen z∉ΓxΔ) z≢y)) } -}
thinning {Δ , y ∷ c} x∉ΓΔy Γ⊢b (abstr ΓΔy⊢Π ΓΔyz⊢m) = 
  abstr
    (thinning x∉ΓΔy Γ⊢b ΓΔy⊢Π)
    {!!}
    {-λ { {z} (∉Γ z∉ΓxΔ z≢y) →
      thinning
        (∉Γ x∉ΓΔy ((≢-sym (∉-to-≢ z∉ΓxΔ))))
        Γ⊢b
        (ΓΔyz⊢m {z} (∉Γ (∉-strengthen z∉ΓxΔ) z≢y)) }-}
thinning {Δ , y ∷ c} x∉ΓΔy Γ⊢b (app ΓΔy⊢m ΓΔy⊢n) = 
  app
    (thinning x∉ΓΔy Γ⊢b ΓΔy⊢m)
    (thinning x∉ΓΔy Γ⊢b ΓΔy⊢n)
thinning {Δ , y ∷ c} x∉ΓΔy Γ⊢b (conv-red ΓΔy⊢m ΓΔy⊢b b↠a) = 
  conv-red
    (thinning x∉ΓΔy Γ⊢b ΓΔy⊢m)
    (thinning x∉ΓΔy Γ⊢b ΓΔy⊢b)
    b↠a
thinning {Δ , y ∷ c} x∉ΓΔy Γ⊢b (conv-exp ΓΔy⊢m ΓΔy⊢b a↠b) = 
  conv-exp
    (thinning x∉ΓΔy Γ⊢b ΓΔy⊢m)
    (thinning x∉ΓΔy Γ⊢b ΓΔy⊢b)
    a↠b

weaken : ∀ {Γ x a b m j} →
  x ∉ Γ →
  Γ ⊢ b ∷ s j →
  Γ ⊢ m ∷ a →
  Γ , x ∷ b ⊢ m ∷ a
weaken = thinning
-}
-------------------------------------------------------------------------------
-- Substitution

lemma : ∀ {Γ m n a x} →
  Γ ⊢ m ∷ a →
  x ∉ Γ →
  m [ n / x ] ≡ m
lemma = {!!}

substitution : ∀ {Δ Γ x a m n b} →
  Γ ⊢ n ∷ a →
  (Γ , x ∷ a) ∘ Δ ⊢ m ∷ b →
  Γ ∘ (Δ [ n / x ]ᶜ)  ⊢ m [ n / x ] ∷ b [ n / x ]
substitution (axiom x) = {!!}
substitution (var-intro x Γ⊢n) = {!!}
substitution (sort-weaken x x₁ Γ⊢n Γ⊢n₁) = {!!}
substitution (var-weaken x Γ⊢n Γ⊢n₁) = {!!}
substitution (pi-intro x Γ⊢n x₁) = {!!}
substitution (abstr Γ⊢n x) = {!!}
substitution (app Γ⊢n Γ⊢n₁) = {!!}
substitution (conv-red Γ⊢n Γ⊢n₁ x) = {!!}
substitution (conv-exp Γ⊢n Γ⊢n₁ x) = {!!}
{- substitution {∅} {x = x} Γ⊢n (var-intro x∉Γ Γ⊢a) with x Data.String.≟ x
... | yes _ = ?
... | no _ = ?
substitution {∅} Γ⊢n (sort-weaken x x₁ Γx⊢m Γx⊢m₁) = {!!}
substitution {∅} Γ⊢n (var-weaken x Γx⊢m Γx⊢m₁) = {!!}
substitution {∅} Γ⊢n (pi-intro x Γx⊢m x₁) = {!!}
substitution {∅} Γ⊢n (abstr Γx⊢m x) = {!!}
substitution {∅} Γ⊢n (app Γx⊢m Γx⊢m₁ x) = {!!}
substitution {∅} Γ⊢n (conv-red Γx⊢m Γx⊢m₁ x) = {!!}
substitution {∅} Γ⊢n (conv-exp Γx⊢m Γx⊢m₁ x) = {!!}
substitution {Δ , y ∷ c} Γ⊢n ΓxΔ⊢m = {!!}
-}
{-
substitution {Δ = ∅} {x = x} {n = n} Γ⊢n (var-intro {a = a} x∉Γ Γ⊢a)
  rewrite (noop-sub {m = a} {n = n} Γ⊢a x∉Γ)
  with x Data.String.≟ x
...  | yes _ = Γ⊢n
...  | no x≢x = ⊥-elim (x≢x refl)
substitution {∅} Γ⊢n (sort-weaken _ _ Γ⊢s) = Γ⊢s
substitution {∅} {x = x} {n = n} {b = b} Γ⊢n (var-weaken {y} {a = b} {b = c} x∉Γ Γ⊢c Γ⊢y)
  rewrite (noop-sub {m = b} {n = n} (var-type-correctness Γ⊢y) x∉Γ)
  with y Data.String.≟ x
...  | yes _ = {!!}
...  | no _ = Γ⊢y
substitution {∅} Γ⊢n (pi-intro rl Γ,x⊢a Γ,x,y⊢b) = 
  pi-intro rl
    (substitution Γ⊢n Γ,x⊢a)
    λ {y} → λ y∉Γ → {!
      substitution Γ⊢n (Γ,x,y⊢b {y} (∉Γ y∉Γ ?))  !} 
substitution {∅} Γ⊢n (abstr md x) = {!!}
substitution {∅} Γ⊢n (app md md₁ x) = {!!}
substitution {∅} Γ⊢n (conv-red md md₁ x) = {!!}
substitution {∅} Γ⊢n (conv-exp md md₁ x) = {!!}
substitution {Δ , z ∷ d} Γ⊢n md = {!!}
-}

-------------------------------------------------------------------------------
-- Generation Lemma (Π-Types)
{-
Π-gen₁ : ∀ {Γ a b c} →
  Γ ⊢ Π a · b ∷ c →
  ∃[ i ] ∃[ j ] ∃[ k ] Spec.rule 𝕊 i j k
Π-gen₁ (pi-intro {i = i} {j = j} {k = k} rl _ _) = (i , (j , (k , rl)))
Π-gen₁ (conv-red Γ⊢Π _ _) = Π-gen₁ Γ⊢Π
Π-gen₁ (conv-exp Γ⊢Π _ _) = Π-gen₁ Γ⊢Π

Π-gen₂ : ∀ {Γ a b c} →
  Γ ⊢ Π a · b ∷ c →
  ∃[ k ] (c =ᵇ s k)
Π-gen₂ (pi-intro {k = k} rl Γ⊢Π Γx⊢b) = (k , =ᵇ-refl β-refl) 
Π-gen₂ (conv-red Γ⊢Π _ d↠c) = map₂ (=ᵇ-trans (=ᵇ-sym (=ᵇ-refl d↠c))) (Π-gen₂ Γ⊢Π)
Π-gen₂ (conv-exp Γ⊢Π Γ⊢Π₁ c↠d) = map₂ (=ᵇ-trans (=ᵇ-refl c↠d)) (Π-gen₂ Γ⊢Π) 

Π-gen₃ : ∀ {Γ a b c} →
  Γ ⊢ Π a · b ∷ c →
  ∃[ i ] Γ ⊢ a ∷ s i
Π-gen₃ (pi-intro {i = i} _ Γ⊢a _) = (i , Γ⊢a)
Π-gen₃ (conv-red Γ⊢Π _ _) = Π-gen₃ Γ⊢Π
Π-gen₃ (conv-exp Γ⊢Π _ _) = Π-gen₃ Γ⊢Π

Π-gen₄ : ∀ {Γ a b c x} →
  Γ ⊢ Π a · b ∷ c →
  x ∉ Γ →
  ∃[ i ] ∃[ j ] Γ , x ∷ a ⊢ b [ f⟨ x ♯ i ⟩ ]⁰ ∷ s j
Π-gen₄ (pi-intro {i = i} {j = j} _ _ Γx⊢b) x∉Γ = (i , (j , Γx⊢b x∉Γ))
Π-gen₄ (conv-red Γ⊢Π _ _) = Π-gen₄ Γ⊢Π
Π-gen₄ (conv-exp Γ⊢Π _ _) = Π-gen₄ Γ⊢Π

fresh : ∀ {Γ} → Σ[ x ∈ ℕ ] x ∉ Γ
fresh {Γ = ∅} = (0 , ∉∅)
fresh {Γ = (Γ' , x ∷ a)} = (proj₁ (fresh {Γ = Γ'}) + x , ∉Γ {!!} {!!}) 
-}
Π-gen₅ : ∀ {Γ a b c n j x i} →
  Γ ⊢ Π a · b ∷ c →
  Γ , x ∷ a ⊢ b [ f⟨ x ♯ i ⟩ ]⁰ ∷ s j →
  Γ ⊢ n ∷ a →
  Γ ⊢ b [ n ]⁰ ∷ s j
Π-gen₅ Γ⊢Π Γx⊢b Γ⊢n = {!!}
-------------------------------------------------------------------------------
-- Type Correctness

type-correctness : ∀ {Γ m a} →
  Γ ⊢ m ∷ a →
  (∃[ i ] Γ ⊢ a ∷ s i) ⊎ (∃[ i ] a ≡ s i)
type-correctness (axiom {j = j} _) = inj₂ (j , refl)
type-correctness (var-intro {i = i} x∉Γ Γ⊢a) = inj₁ (i , weaken x∉Γ Γ⊢a Γ⊢a )
type-correctness (sort-weaken {k = k} ax x∉Γ Γ⊢b Γ⊢s) = inj₂ (k , refl)
type-correctness (var-weaken y∉Γ Γ⊢b Γ⊢x) =
  [ (λ prf → inj₁ ((proj₁ prf , weaken y∉Γ Γ⊢b (proj₂ prf)))) , inj₂ ] (type-correctness Γ⊢x)
type-correctness (pi-intro {k = k} _ _ _) = inj₂ (k , refl)
type-correctness (abstr {j = j} Γ⊢Π Γx⊢m) = inj₁ (j , Γ⊢Π)
type-correctness (app Γ⊢m Γ⊢n) =
  [ (λ prf → {!!})
  ,  (λ prf → ⊥-elim (Π-not-sort (proj₂ prf)))
  ] (type-correctness Γ⊢m)
type-correctness (conv-red {i = i} _ Γ⊢a _) = inj₁ (i , Γ⊢a)
type-correctness (conv-exp {i = i} _ Γ⊢a _) = inj₁ (i , Γ⊢a)
{-
{-
-------------------------------------------------------------------------------
-- Generation Lemma (Sorts)

s-gen₁ : {i : ℕ} {Γ : ℂ} {a : 𝕋} →
  𝕊 ∥ Γ ⊢ s i ∷ a →
  a ↠ᵇ s (suc i)
s-gen₁ {i = i} (axiom x) = β-refl {i}
s-gen₁ (sort-weaken _ deriv _) = s-gen₁ deriv
s-gen₁ {i = i} {a = b} (conv-red {a = a} m-deriv b-deriv a↠b) =
  subst (λ { k → b ↠ᵇ k })
    (sort-nf (proj₁ (proj₂ lem₂)))
    (proj₂ (proj₂ lem₂)) where
      lem₁ : a ↠ᵇ s (suc i)
      lem₁ = s-gen₁ m-deriv
      lem₂ : Σ[ p ∈ 𝕋 ] (s (suc i) ↠ᵇ p) × (b ↠ᵇ p)
      lem₂ = church-rosser lem₁ a↠b
s-gen₁ (conv-exp m-deriv b-deriv b↠a) = ↠ᵇ-trans b↠a (s-gen₁ m-deriv)

s-gen₂ : {i j : ℕ} {Γ : ℂ} →
  𝕊 ∥ Γ ⊢ s i ∷ s j →
  j ≡ suc i
s-gen₂ deriv = sᵢ≡sⱼ→i≡j (sym (sort-nf (s-gen₁ deriv)))

s-gen₃ : {i j : ℕ} {Γ : ℂ} →
  𝕊 ∥ Γ ⊢ s i ∷ s j →
  𝕊 ∥ Γ ⊢ s i ∷ s (suc i)
s-gen₃ deriv = subst (λ { j → _ ∥ _ ⊢ _ ∷ s j }) (s-gen₂ deriv) deriv

s-strengthen : {i x j : ℕ} {Γ : ℂ} {a b : 𝕋} →
  𝕊 ∥ (Γ , x ♯ j ∷ a) ⊢ s i ∷ b →
  𝕊 ∥ Γ ⊢ s i ∷ b
s-strengthen (sort-weaken _ deriv _) = deriv
s-strengthen (conv-red m-deriv a-deriv a↠b) = {!   !} -- NON-TRIVIAL
s-strengthen (conv-exp m-deriv a-deriv b↠a) = {!!}

-------------------------------------------------------------------------------
-- Generation Lemma (Π-Types)

Π-gen₁ : {i j x : ℕ} {Γ : ℂ} {a b : 𝕋} →
  𝕊 ∥ Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j →
  (x ♯ i) ∉ Γ →
  𝕊 ∥ (Γ , x ♯ i ∷ a) ⊢ b [ f⟨ x ♯ i ⟩ /0♯ i ] ∷ s j
Π-gen₁ = {!   !}

Π-gen₂ : {i j : ℕ} {Γ : ℂ} {a b n : 𝕋} →
  𝕊 ∥ Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j →
  𝕊 ∥ Γ ⊢ n ∷ a →
  𝕊 ∥ Γ ⊢ b [ n /0♯ i ] ∷ s j
Π-gen₂ (pi-intro x pi-deriv pi-deriv₁) n-deriv = {!   !}
Π-gen₂ (conv-red pi-deriv pi-deriv₁ x) n-deriv = {!   !}
Π-gen₂ (conv-exp pi-deriv pi-deriv₁ x) n-deriv = {!   !}

-------------------------------------------------------------------------------
-- Top Sort Lemma

sₜ-not-typable : {Γ : ℂ} {m a : 𝕋} →
  𝕊 ∥ Γ ⊢ m ∷ a →
  m ≢ s (Spec.t 𝕊)
sₜ-not-typable (axiom prf) = i≢j⇒sᵢ≢sⱼ (m<n⇒m≢n prf)
sₜ-not-typable (var-intro x deriv) ()
sₜ-not-typable (sort-weaken _ deriv _) = sₜ-not-typable deriv
sₜ-not-typable (var-weaken _ deriv _) = sₜ-not-typable deriv
sₜ-not-typable (pi-intro _ _ _) ()
sₜ-not-typable (abstr _ _) ()
sₜ-not-typable (app _ _ _) ()
sₜ-not-typable (conv-red deriv _ _) = sₜ-not-typable deriv
sₜ-not-typable (conv-exp deriv _ _) = sₜ-not-typable deriv

Γ⊬sₜ∷a : {Γ : ℂ} {a : 𝕋} →
  𝕊 ∥ Γ ⊬ s (Spec.t 𝕊) ∷ a
Γ⊬sₜ∷a deriv = sₜ-not-typable deriv refl

no-var-sₜ : {x i : ℕ} {Γ : ℂ} {a : 𝕋} →
  𝕊 ∥ Γ ⊢ f⟨ x ♯ i ⟩ ∷ a →
  a ≢ s (Spec.t 𝕊)
no-var-sₜ (var-intro _ deriv) = sₜ-not-typable deriv
no-var-sₜ (var-weaken _ deriv _) = no-var-sₜ deriv
no-var-sₜ (conv-red _ deriv _) = sₜ-not-typable deriv
no-var-sₜ (conv-exp _ deriv _) = sₜ-not-typable deriv

Γ⊬x∷sₜ : {x i : ℕ} {Γ : ℂ} →
  𝕊 ∥ Γ ⊬ f⟨ x ♯ i ⟩ ∷ s (Spec.t 𝕊)
Γ⊬x∷sₜ deriv = no-var-sₜ deriv refl

no-λ-sₜ : {i : ℕ} {Γ : ℂ} {a m b : 𝕋} →
  𝕊 ∥ Γ ⊢ λˢ i ∷ a ⇒ m ∷ b →
  b ≢ s (Spec.t 𝕊)
no-λ-sₜ (abstr deriv deriv₁) ()
no-λ-sₜ (conv-red _ deriv _) = sₜ-not-typable deriv
no-λ-sₜ (conv-exp _ deriv _) = sₜ-not-typable deriv

Γ⊬λ∷sₜ : {i : ℕ} {Γ : ℂ} {a m : 𝕋} →
  𝕊 ∥ Γ ⊬ λˢ i ∷ a ⇒ m ∷ s (Spec.t 𝕊)
Γ⊬λ∷sₜ deriv = no-λ-sₜ deriv refl

no-app-sₜ : {i : ℕ} {Γ : ℂ} {m n a : 𝕋} →
  𝕊 ∥ Γ ⊢ m § i § n ∷ a →
  a ≢ s (Spec.t 𝕊)
no-app-sₜ 
  {𝕊 = 𝕊} {i = i} {Γ = Γ} {n = n}
  (app {a = a} {b = b} m-deriv n-deriv c≡sub) c≡sₜ =
    [ b≢sₜ , n≢sₜ ] sₜ-form where
      sₜ≡sub : s (Spec.t 𝕊) ≡ b [ n /0♯ i ]
      sₜ≡sub = trans (sym c≡sₜ) c≡sub
      sₜ-form : b ≡ s (Spec.t 𝕊) ⊎ n ≡ s (Spec.t 𝕊)
      sₜ-form = sort-sub sₜ≡sub
      tc : Σ[ j ∈ ℕ ] 𝕊 ∥ Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j 
      tc = type-correctness m-deriv (λ { () })
      k : ℕ
      k = proj₁ tc
      b≢sₜ : b ≢ s (Spec.t 𝕊)
      b≢sₜ b≡sₜ =
        Γ⊬sₜ∷a (subst (λ { m → _ ∥ Γ ⊢ m ∷ s k })
          (sym sₜ≡sub) (Π-gen₂ (proj₂ tc) n-deriv))
      n≢sₜ : n ≢ s (Spec.t 𝕊)
      n≢sₜ = sₜ-not-typable n-deriv 
no-app-sₜ (conv-red _ deriv _) = sₜ-not-typable deriv
no-app-sₜ (conv-exp _ deriv _) = sₜ-not-typable deriv

Γ⊬mn∷sₜ : {i : ℕ} → {Γ : ℂ} → {m n : 𝕋} →
  𝕊 ∥ Γ ⊬ m § i § n ∷ s (Spec.t 𝕊)
Γ⊬mn∷sₜ deriv = no-app-sₜ deriv refl
-}
-}
