
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

open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; proj₁; proj₂; _,_; ∃; ∃-syntax; map₂)
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

data _∉ᵗ_ : ℕ → 𝕋 → Set where
  ∉-s : ∀ {x i} → x ∉ᵗ s i
  ∉-v : ∀ {x y i} → x ≢ y → x ∉ᵗ ⟨ y ♯ i ⟩
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

-------------------------------------------------------------------------------
-- Thinning

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
thinning {∅} x∉ΓΔ Γ⊢b (pi-intro {a} rl sd td) = pi-intro rl (thinning x∉ΓΔ Γ⊢b sd)
  λ { {y} (∉Γ not-in not-eq) → thinning (∉Γ x∉ΓΔ (≢-sym not-eq)) Γ⊢b (td not-in) }
thinning {∅} x∉ΓΔ Γ⊢b (abstr {a} pid md) = abstr (thinning x∉ΓΔ Γ⊢b pid)
  λ { {y} (∉Γ not-in not-eq) → thinning {∅ , y ∷ a} ((∉Γ x∉ΓΔ (≢-sym not-eq))) Γ⊢b (md not-in) }
thinning {∅} x∉ΓΔ Γ⊢b (app md nd ty-eq) =
  app (thinning x∉ΓΔ Γ⊢b md) (thinning x∉ΓΔ Γ⊢b nd) ty-eq
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
    λ { {z} (∉Γ z∉ΓxΔ z≢y) →
      thinning
        (∉Γ x∉ΓΔy (≢-sym (∉-to-≢ z∉ΓxΔ)))
        Γ⊢b
        (ΓΔyx⊢b {z} (∉Γ (∉-strengthen z∉ΓxΔ) z≢y)) }
thinning {Δ , y ∷ c} x∉ΓΔy Γ⊢b (abstr ΓΔy⊢Π ΓΔyz⊢m) = 
  abstr
    (thinning x∉ΓΔy Γ⊢b ΓΔy⊢Π)
    λ { {z} (∉Γ z∉ΓxΔ z≢y) →
      thinning
        (∉Γ x∉ΓΔy ((≢-sym (∉-to-≢ z∉ΓxΔ))))
        Γ⊢b
        (ΓΔyz⊢m {z} (∉Γ (∉-strengthen z∉ΓxΔ) z≢y)) }
thinning {Δ , y ∷ c} x∉ΓΔy Γ⊢b (app ΓΔy⊢m ΓΔy⊢n a≡b[n]) = 
  app
    (thinning x∉ΓΔy Γ⊢b ΓΔy⊢m)
    (thinning x∉ΓΔy Γ⊢b ΓΔy⊢n)
    a≡b[n]
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


-------------------------------------------------------------------------------
-- Substitution

sub-comm₁ : ∀ {m n x i} →
  m [ n ]⁰ ≡ m [ ⟨ x ♯ i ⟩ ]⁰ [ n / x ]
sub-comm₁ = {!!}

substitution : ∀ {Δ Γ x a m n b} →
  Γ ⊢ n ∷ a →
  (Γ , x ∷ a) ∘ Δ ⊢ m ∷ b →
  Γ ∘ (Δ [ n / x ]ᶜ)  ⊢ m [ n / x ] ∷ b [ n / x ]
substitution = {!!}
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
  ∃[ i ] ∃[ j ] Γ , x ∷ a ⊢ b [ ⟨ x ♯ i ⟩ ]⁰ ∷ s j
Π-gen₄ (pi-intro {i = i} {j = j} _ _ Γx⊢b) x∉Γ = (i , (j , Γx⊢b x∉Γ))
Π-gen₄ (conv-red Γ⊢Π _ _) = Π-gen₄ Γ⊢Π
Π-gen₄ (conv-exp Γ⊢Π _ _) = Π-gen₄ Γ⊢Π

Π-gen₅ : ∀ {Γ x a b c n} →
  Γ ⊢ Π a · b ∷ c →
  Γ ⊢ n ∷ a →
  x ∉ Γ →
  ∃[ j ] Γ ⊢ b [ n ]⁰ ∷ s j
Π-gen₅ {b = s i} (pi-intro {j = j} x Γ⊢Π x₁) Γ⊢n x∉Γ = (j , {!!})
Π-gen₅ {b = ⟨ x₂ ♯ x₃ ⟩} (pi-intro {j = j} x Γ⊢Π x₁) Γ⊢n x∉Γ = (j , {!!})
Π-gen₅ {b = ƛ b · b₁} (pi-intro {j = j} x Γ⊢Π x₁) Γ⊢n x∉Γ = (j , {!!})
Π-gen₅ {b = Π b · b₁} (pi-intro {j = j} x Γ⊢Π x₁) Γ⊢n x∉Γ = (j , {!!})
Π-gen₅ {b = b § b₁} (pi-intro {j = j} x Γ⊢Π x₁) Γ⊢n x∉Γ = (j , {!!})
Π-gen₅ {b = b} (conv-red Γ⊢Π Γ⊢Π₁ x) Γ⊢n x∉Γ = {!!}
Π-gen₅ {b = b} (conv-exp Γ⊢Π Γ⊢Π₁ x) Γ⊢n x∉Γ = {!!}

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
type-correctness (app Γ⊢m Γ⊢n c≡bn) =
  [ (λ prf → inj₁ {!!})
  ,  (λ prf → ⊥-elim (Π-not-sort (proj₂ prf)))
  ] (type-correctness Γ⊢m)
type-correctness (conv-red {i = i} _ Γ⊢a _) = inj₁ (i , Γ⊢a)
type-correctness (conv-exp {i = i} _ Γ⊢a _) = inj₁ (i , Γ⊢a)

{-
{-
-------------------------------------------------------------------------------
-- Helpers

{-
i≢j⇒sᵢ≢sⱼ : {i j : ℕ} → i ≢ j → s i ≢ s j
i≢j⇒sᵢ≢sⱼ neq refl = neq refl

sᵢ≢sⱼ⇒i≢j : {i j : ℕ} → s i ≢ s j → i ≢ j
sᵢ≢sⱼ⇒i≢j neq refl = neq refl

sᵢ≡sⱼ→i≡j : {i j : ℕ} → s i ≡ s j → i ≡ j
sᵢ≡sⱼ→i≡j refl = refl

∉Γ-strengthen : {x y : 𝕍} {Γ : ℂ} {a : 𝕋} →
  x ∉ (Γ , y ∷ a) →
  x ≢ y →
  x ∉ Γ
∉Γ-strengthen (∉Γ x∉Γ x≡y) x≢y = ⊥-elim (x≢y x≡y)

lift-drop-lemma : {x : ℕ} {m : 𝕋} →
  lift-map pred x (lift-map suc x m) ≡ m
lift-drop-lemma {x} {m} = go x m where
  l : ℕ → 𝕋 → 𝕋
  l = lift-map suc
  d : ℕ → 𝕋 → 𝕋
  d = lift-map pred
  go : (x : ℕ) → (m : 𝕋) →
    d x (l x m) ≡ m
  go x (s _) = refl
  go x b⟨ _ ♯ _ ⟩ = refl
  go x f⟨ y ♯ _ ⟩ with x ≤? y
  go x f⟨ y ♯ _ ⟩    | yes p' with x ≤? suc y
  go x f⟨ y ♯ _ ⟩    | yes p'    | yes _ = refl
  go x f⟨ y ♯ _ ⟩    | yes p'    | no ¬p = ⊥-elim (¬p (m≤n⇒m≤1+n p'))
  go x f⟨ y ♯ _ ⟩    | no ¬p with x ≤? y
  go x f⟨ y ♯ _ ⟩    | no ¬p    | yes p = ⊥-elim (¬p p)
  go x f⟨ y ♯ _ ⟩    | no ¬p    | no _ = refl
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

↓↑-id : {n : 𝕋} →
  ↓ (↑ n) ≡ n
↓↑-id = lift-drop-lemma {x = 0}

sort-sub : {i j : ℕ} {m n : 𝕋} →
  s i ≡ m [ n /0♯ j ] →
  m ≡ s i ⊎ n ≡ s i
sort-sub {m = s k} eq = inj₁ (sym eq)
sort-sub {j = j} {m = b⟨ y ♯ k ⟩} eq with (y ♯ k) ≟ (0 ♯ j)
...                                     | yes _ = inj₂ (sym (trans eq ↓↑-id))
...                                     | no _ = ⊥-elim (s-not-var eq) where
  s-not-var : {i x j : ℕ} → s i ≢ b⟨ x ♯ j ⟩
  s-not-var ()
sort-sub {j = j} {m = f⟨ x ♯ k ⟩} eq = ⊥-elim (s-not-var eq) where
  s-not-var : {i x j : ℕ} → s i ≢ f⟨ x ♯ j ⟩
  s-not-var ()

sort-nf : {i : ℕ} → {a : 𝕋} →
  s i ↠ᵇ a →
  a ≡ s i
sort-nf β-refl = refl

-------------------------------------------------------------------------------
-- Church-Rosser

church-rosser : {m n₁ n₂ : 𝕋} →
  m ↠ᵇ n₁ →
  m ↠ᵇ n₂ →
  Σ[ p ∈ 𝕋 ] (n₁ ↠ᵇ p) × (n₂ ↠ᵇ p)
church-rosser = {!   !}

-------------------------------------------------------------------------------
-- Assume a Specification

variable
  𝕊 : Spec

-------------------------------------------------------------------------------
-- Inversion

inversion : {x i y j : ℕ} {Γ Δ : ℂ} {a b m c : 𝕋} →
  (x ♯ i) ∉ (Γ , y ♯ j ∷ a) →
  𝕊 ∥ (((Γ , x ♯ i ∷ b) , y ♯ j ∷ a) ∘ Δ) ⊢ m ∷ c →
  𝕊 ∥ (((Γ , y ♯ j ∷ a) , x ♯ i ∷ a) ∘ Δ) ⊢ m ∷ c
inversion = {!   !}
-}

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

-------------------------------------------------------------------------------
-- Thinning

thinning : ∀ {Δ b Γ x a j m} →
  x ∉ (Γ ∘ Δ) →
  Γ ⊢ b ∷ s j →
  (Γ ∘ Δ) ⊢ m ∷ a →
  ((Γ , x ∷ b) ∘ Δ) ⊢ m ∷ a
thinning {∅} x∉ΓΔ Γ⊢b (axiom i<n) = sort-weaken x∉ΓΔ Γ⊢b (axiom i<n)
thinning {∅} x∉ΓΔ Γ⊢b (var-intro y∉ΓΔ ΓΔ⊢c) = var-weaken x∉ΓΔ Γ⊢b (var-intro y∉ΓΔ ΓΔ⊢c) 
thinning {∅} x∉ΓΔ Γ⊢b (sort-weaken y∉ΓΔ ΓΔ⊢s ΓΔ⊢c) = sort-weaken x∉ΓΔ Γ⊢b (sort-weaken y∉ΓΔ ΓΔ⊢s ΓΔ⊢c)
thinning {∅} x∉ΓΔ Γ⊢b (var-weaken fr md cd) = var-weaken x∉ΓΔ Γ⊢b (var-weaken fr md cd)
thinning {∅} x∉ΓΔ Γ⊢b (pi-intro {a} rl sd td) = pi-intro rl (thinning x∉ΓΔ Γ⊢b sd)
  λ { {y} (∉Γ not-in not-eq) → thinning (∉Γ x∉ΓΔ (≢-sym not-eq)) Γ⊢b (td not-in) }
thinning {∅} x∉ΓΔ Γ⊢b (abstr {a} pid md) = abstr (thinning x∉ΓΔ Γ⊢b pid)
  λ { {y} (∉Γ not-in not-eq) → thinning {∅ , y ∷ a} ((∉Γ x∉ΓΔ (≢-sym not-eq))) Γ⊢b (md not-in) }
thinning {∅} x∉ΓΔ Γ⊢b (app md nd ty-eq) =
  app (thinning x∉ΓΔ Γ⊢b md) (thinning x∉ΓΔ Γ⊢b nd) ty-eq
thinning {∅} x∉ΓΔ Γ⊢b (conv-red md bd red) =
  conv-red (thinning x∉ΓΔ Γ⊢b md) (thinning x∉ΓΔ Γ⊢b bd) red
thinning {∅} x∉ΓΔ Γ⊢b (conv-exp md bd exp) =
  conv-exp (thinning x∉ΓΔ Γ⊢b md) (thinning x∉ΓΔ Γ⊢b bd) exp
thinning {Δ , y ∷ c} (∉Γ not-in not-eq) Γ⊢b (var-intro fr ad) =
  var-intro (∉-thinning fr (≢-sym not-eq)) (thinning not-in Γ⊢b ad)
thinning {Δ , y ∷ c} (∉Γ x∉ΓΔ x≢y) Γ⊢b (sort-weaken y∉ΓΔ ΓΔ⊢c ΓΔ⊢s) = 
  sort-weaken
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
    λ { {z} (∉Γ z∉ΓxΔ z≢y) →
      thinning
        (∉Γ x∉ΓΔy (≢-sym (∉-to-≢ z∉ΓxΔ)))
        Γ⊢b
        (ΓΔyx⊢b {z} (∉Γ (∉-strengthen z∉ΓxΔ) z≢y)) }
thinning {Δ , y ∷ c} x∉ΓΔy Γ⊢b (abstr ΓΔy⊢Π ΓΔyz⊢m) = 
  abstr
    (thinning x∉ΓΔy Γ⊢b ΓΔy⊢Π)
    λ { {z} (∉Γ z∉ΓxΔ z≢y) →
      thinning
        (∉Γ x∉ΓΔy ((≢-sym (∉-to-≢ z∉ΓxΔ))))
        Γ⊢b
        (ΓΔyz⊢m {z} (∉Γ (∉-strengthen z∉ΓxΔ) z≢y)) }
thinning {Δ , y ∷ c} x∉ΓΔy Γ⊢b (app ΓΔy⊢m ΓΔy⊢n a≡b[n]) = 
  app
    (thinning x∉ΓΔy Γ⊢b ΓΔy⊢m)
    (thinning x∉ΓΔy Γ⊢b ΓΔy⊢n)
    a≡b[n]
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

-------------------------------------------------------------------------------
-- Substitution Lemma

noop-sub : ∀ {Γ m a x n} →
  Γ ⊢ m ∷ a →
  x ∉ Γ →
  m [ n / x ] ≡ m
noop-sub (axiom _) x∉Γ = refl
noop-sub (var-intro {x = y} y∉Γ Γ⊢a) x∉Γ,y = {!noop-sub !}
noop-sub (sort-weaken x Γ⊢m Γ⊢m₁) x∉Γ = {!!}
noop-sub (var-weaken x Γ⊢m Γ⊢m₁) x∉Γ = {!!}
noop-sub (pi-intro x Γ⊢m x₁) x∉Γ = {!!}
noop-sub (abstr Γ⊢m x) x∉Γ = {!!}
noop-sub (app Γ⊢m Γ⊢m₁ x) x∉Γ = {!!}
noop-sub (conv-red Γ⊢m Γ⊢m₁ x) x∉Γ = {!!}
noop-sub (conv-exp Γ⊢m Γ⊢m₁ x) x∉Γ = {!!}

var-type-correctness : ∀ {Γ x i a} →
  Γ ⊢ f⟨ x ♯ i ⟩ ∷ a →
  Γ ⊢ a ∷ s i
var-type-correctness = {!!}

substitution : ∀ {Δ Γ x a m n b} →
  Γ ⊢ n ∷ a →
  ((Γ , x ∷ a) ∘ Δ) ⊢ m ∷ b →
  (Γ ∘ (Δ [ n / x ]ᶜ))  ⊢ m [ n / x ] ∷ (b [ n / x ])
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

{-
-------------------------------------------------------------------------------
-- Contexts in Judgments are Well-formed

Γ-wf : {Γ : ℂ} {m a : 𝕋} →
  𝕊 ∥ Γ ⊢ m ∷ a →
  WFC 𝕊 Γ
Γ-wf = go where
  go : {Γ : ℂ} {m a : 𝕋} → 𝕊 ∥ Γ ⊢ m ∷ a → WFC 𝕊 Γ
  go (axiom x) = ∅-wf
  go (var-intro fresh deriv) = ext-wf fresh deriv (go (deriv))
  go (sort-weaken fresh _ deriv) = ext-wf fresh deriv (go (deriv))
  go (var-weaken fresh _ deriv) = ext-wf fresh deriv (go (deriv))
  go (pi-intro _ deriv _) = go deriv
  go (abstr _ deriv) = go deriv
  go (app deriv _ _) = go deriv
  go (conv-red deriv _ _) = go deriv
  go (conv-exp deriv _ _) = go deriv

-------------------------------------------------------------------------------
-- Start Lemma

start : {i : ℕ} {Γ : ℂ} →
  i < Spec.t 𝕊 →
  WFC 𝕊 Γ →
  𝕊 ∥ Γ ⊢ s i ∷ s (suc i)
start i<t ∅-wf = axiom i<t
start i<t (ext-wf fresh a-deriv Γ-wf) = sort-weaken fresh (start i<t Γ-wf) a-deriv
 

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
-- Type Correctness

type-correctness : {Γ : ℂ} {m a : 𝕋} →
  𝕊 ∥ Γ ⊢ m ∷ a →
  a ≢ s (Spec.t 𝕊) →
  Σ[ i ∈ ℕ ] 𝕊 ∥ Γ ⊢ a ∷ s i
type-correctness (axiom {i = i} i<t) prf = (suc (suc i) , axiom (≤∧≢⇒< i<t (sᵢ≢sⱼ⇒i≢j prf)))
type-correctness (var-intro {i = i} fresh deriv) _ = (i , weaken fresh deriv deriv)
type-correctness (sort-weaken fresh m-deriv b-deriv) prf =
  let (i , done) = type-correctness m-deriv prf in
    (i , weaken fresh done b-deriv)
type-correctness (var-weaken fresh m-deriv b-deriv) prf = 
  let (i , done) = type-correctness m-deriv prf in
    (i , weaken fresh done b-deriv)
type-correctness (pi-intro {j = j} _ a-deriv b-deriv) prf =
  (suc j , s-strengthen (s-gen₃ (proj₂ (type-correctness b-deriv prf))))
type-correctness (abstr {j = j} _ t-deriv) _ = (j , t-deriv)
type-correctness {Γ = Γ} (app {c = c} m-deriv n-deriv c≡sub) c≢sₜ = 
  let (j , Π-deriv) = type-correctness m-deriv (λ { () }) in
    (j , subst (λ { n → _ ∥ Γ ⊢ n ∷ s j }) (sym c≡sub) (Π-gen₂ Π-deriv n-deriv))
type-correctness (conv-red {i = i} _ a-deriv _) _ = (i , a-deriv)
type-correctness (conv-exp {i = i} _ a-deriv _) _ = (i , a-deriv)

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

-}
