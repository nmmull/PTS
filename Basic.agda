-------------------------------------------------------------------------------
-- Basic Meta-Theoretic Lemmas
--
-------------------------------------------------------------------------------

module Basic where

open import Tiered
open import Data.Nat using (ℕ; suc; pred; _≤?_; _<_; _≤_)
open import Data.Nat.Properties using (≤∧≢⇒<)
open import Utils.Nat using (m≤n⇒m≤1+n; m<n⇒m≢n; 1+n≤m⇒n≤m; m≡n∧m≤p⇒n≤p)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; subst; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂; _,_)

-------------------------------------------------------------------------------
-- Helpers

i≢j⇒sᵢ≢sⱼ : {i j : ℕ} → i ≢ j → s i ≢ s j
i≢j⇒sᵢ≢sⱼ neq refl = neq refl

sᵢ≢sⱼ⇒i≢j : {i j : ℕ} → s i ≢ s j → i ≢ j
sᵢ≢sⱼ⇒i≢j neq refl = neq refl

sᵢ≡sⱼ→i≡j : {i j : ℕ} → s i ≡ s j → i ≡ j
sᵢ≡sⱼ→i≡j refl = refl

∉Γ-strengthen : {x y : 𝕍} → {Γ : Context} → {a : 𝕋} →
  x ∉ (Γ , y ∷ a) →
  x ≢ y →
  x ∉ Γ
∉Γ-strengthen (∉Γ x∉Γ x≡y) x≢y = ⊥-elim (x≢y x≡y)

lift-drop-lemma : {x : ℕ} → {m : 𝕋} →
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

sort-sub : {i j : ℕ} → {m n : 𝕋} →
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

-------------------------------------------------------------------------------
-- Start Lemma

start : {i : ℕ} → {Γ : Context} →
  i < t →
  WFC Γ →
  Γ ⊢ s i ∷ s (suc i)
start i<t ∅-wf = axiom i<t
start {i} i<t (ext-wf fresh a-deriv Γ-wf) =
  weaken fresh (start i<t Γ-wf) a-deriv

-------------------------------------------------------------------------------
-- Substitution Lemma

sub-lemma : {x i : ℕ} → {Γ' Γ Δ : Context} → {m n a b : 𝕋} →
  Γ' ⊢ m ∷ b →
  Γ' ≡ ((Γ , x ♯ i ∷ a) ∘ Δ) →
  Γ ⊢ n ∷ a →
  (Γ ∘ (Δ [ n / x ♯ i ]ᶜ))  ⊢ m [ n / x ♯ i ] ∷ (b [ n / x ♯ i ])
sub-lemma = {!   !}

-------------------------------------------------------------------------------
-- Generation Lemma (Sorts)

s-gen₁ : {i : ℕ} → {Γ : Context} → {a : 𝕋} →
  Γ ⊢ s i ∷ a →
  a ↠ᵇ s (suc i)
s-gen₁ {i} (axiom x) = β-refl {i}
s-gen₁ (weaken _ deriv _) = s-gen₁ deriv
s-gen₁ (conv deriv deriv₁ b↠ᵇa) = ↠ᵇ-trans b↠ᵇa (s-gen₁ deriv)

sort-nf : {i : ℕ} → {a : 𝕋} →
  s i ↠ᵇ a →
  s i ≡ a
sort-nf β-refl = refl

s-gen₂ : {i j : ℕ} → {Γ : Context} →
  Γ ⊢ s i ∷ s j →
  j ≡ suc i
s-gen₂ deriv = sᵢ≡sⱼ→i≡j (sort-nf (s-gen₁ deriv))

s-gen₃ : {i j : ℕ} → {Γ : Context} →
  Γ ⊢ s i ∷ s j →
  Γ ⊢ s i ∷ s (suc i)
s-gen₃ deriv = subst (λ { j → _ ⊢ _ ∷ s j }) (s-gen₂ deriv) deriv

s-strengthen : {i x j : ℕ} → {Γ : Context} → {a : 𝕋} →
  (Γ , x ♯ j ∷ a) ⊢ s i ∷ s (suc i) →
  Γ ⊢ s i ∷ s (suc i)
s-strengthen (weaken _ deriv _) = deriv
s-strengthen (conv m-deriv a-deriv β-refl) = s-strengthen m-deriv

-------------------------------------------------------------------------------
-- Generation Lemma (Π-Types)

{-
Π-gen₁ : {i j x : ℕ} → {Γ : Context} → {a b : 𝕋} →
  Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j →
  (x ♯ i) ∉ Γ →
  (Γ , x ♯ i ∷ a) ⊢ b [ f⟨ x ♯ i ⟩ /0♯ i ] ∷ s j
Π-gen₁ = {!   !}
-}

Π-gen₂ : {i j : ℕ} → {Γ : Context} → {a b n : 𝕋} →
  Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j →
  Γ ⊢ n ∷ a →
  Γ ⊢ b [ n /0♯ i ] ∷ s j
Π-gen₂ (weaken x deriv deriv₁) n-deriv = {!   !}
Π-gen₂ (pi-intro x deriv deriv₁) n-deriv = {!   !}
Π-gen₂ (conv deriv deriv₁ x) n-deriv = {!   !} 

-------------------------------------------------------------------------------
-- Type Correctness

type-correctness : {Γ : Context} → {m a : 𝕋} →
  Γ ⊢ m ∷ a →
  a ≢ s t →
  Σ[ i ∈ ℕ ] Γ ⊢ a ∷ s i
type-correctness (axiom {i} i<t) prf = (suc (suc i) , axiom (≤∧≢⇒< i<t (sᵢ≢sⱼ⇒i≢j prf)))
type-correctness (var-intro {i = i} fresh deriv) _ = (i , weaken fresh deriv deriv)
type-correctness (weaken fresh m-deriv b-deriv) prf =
  let (i , done) = type-correctness m-deriv prf in
    (i , weaken fresh done b-deriv)
type-correctness (pi-intro {j = j} _ a-deriv b-deriv) prf =
  (suc j , s-strengthen (s-gen₃ (proj₂ (type-correctness b-deriv prf))))
type-correctness (abstr {j = j} _ t-deriv) _ = (j , t-deriv)
type-correctness {Γ = Γ} (app {c = c} m-deriv n-deriv c≡sub) c≢sₜ = 
  let (j , Π-deriv) = type-correctness m-deriv (λ { () }) in
    (j , subst (λ { n → Γ ⊢ n ∷ s j }) (sym c≡sub) (Π-gen₂ Π-deriv n-deriv))
type-correctness (conv {i = i} _ a-deriv _) _ = (i , a-deriv)

-------------------------------------------------------------------------------
-- Top Sort Lemma

sₜ-not-typable : {Γ : Context} → {m a : 𝕋} →
  Γ ⊢ m ∷ a →
  m ≢ sₜ
sₜ-not-typable (axiom prf) = i≢j⇒sᵢ≢sⱼ (m<n⇒m≢n prf)
sₜ-not-typable (var-intro x deriv) ()
sₜ-not-typable (weaken _ deriv _) = sₜ-not-typable deriv
sₜ-not-typable (pi-intro _ _ _) ()
sₜ-not-typable (abstr _ _) ()
sₜ-not-typable (app _ _ _) ()
sₜ-not-typable (conv deriv _ _) = sₜ-not-typable deriv

Γ⊬sₜ∷a : {Γ : Context} → {a : 𝕋} →
  Γ ⊬ sₜ ∷ a
Γ⊬sₜ∷a deriv = sₜ-not-typable deriv refl

no-var-sₜ : {x i : ℕ} → {Γ : Context} → {a : 𝕋} →
  Γ ⊢ f⟨ x ♯ i ⟩ ∷ a →
  a ≢ sₜ
no-var-sₜ (var-intro _ deriv) = sₜ-not-typable deriv
no-var-sₜ (weaken _ deriv _) = no-var-sₜ deriv
no-var-sₜ (conv _ deriv _) = sₜ-not-typable deriv

Γ⊬x∷sₜ : {x i : ℕ} → {Γ : Context} →
  Γ ⊬ f⟨ x ♯ i ⟩ ∷ sₜ
Γ⊬x∷sₜ deriv = no-var-sₜ deriv refl

no-λ-sₜ : {i : ℕ} → {Γ : Context} → {a m b : 𝕋} →
  Γ ⊢ λˢ i ∷ a ⇒ m ∷ b →
  b ≢ sₜ
no-λ-sₜ (weaken _ deriv _) = no-λ-sₜ deriv
no-λ-sₜ (abstr deriv deriv₁) ()
no-λ-sₜ (conv _ deriv _) = sₜ-not-typable deriv

Γ⊬λ∷sₜ : {i : ℕ} → {Γ : Context} → {a m : 𝕋} →
  Γ ⊬ λˢ i ∷ a ⇒ m ∷ sₜ
Γ⊬λ∷sₜ deriv = no-λ-sₜ deriv refl

no-app-sₜ : {i : ℕ} → {Γ : Context} → {m n a : 𝕋} →
  Γ ⊢ m § i § n ∷ a →
  a ≢ sₜ
no-app-sₜ (weaken _ deriv _) = no-app-sₜ deriv
no-app-sₜ 
  {i = i} {Γ = Γ} {n = n}
  (app {a = a} {b = b} m-deriv n-deriv c≡sub) c≡sₜ =
    [ b≢sₜ , n≢sₜ ] sₜ-form where
      sₜ≡sub : sₜ ≡ b [ n /0♯ i ]
      sₜ≡sub = trans (sym c≡sₜ) c≡sub
      sₜ-form : b ≡ sₜ ⊎ n ≡ sₜ
      sₜ-form = sort-sub sₜ≡sub
      tc : Σ[ j ∈ ℕ ] Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j 
      tc = type-correctness m-deriv (λ { () })
      k : ℕ
      k = proj₁ tc
      b≢sₜ : b ≢ sₜ
      b≢sₜ b≡sₜ =  Γ⊬sₜ∷a (subst (λ { m → Γ ⊢ m ∷ s k }) (sym sₜ≡sub) (Π-gen₂ (proj₂ tc) n-deriv))
      n≢sₜ : n ≢ sₜ
      n≢sₜ = sₜ-not-typable n-deriv 
no-app-sₜ (conv _ deriv _) = sₜ-not-typable deriv

Γ⊬mn∷sₜ : {i : ℕ} → {Γ : Context} → {m n : 𝕋} →
  Γ ⊬ m § i § n ∷ sₜ
Γ⊬mn∷sₜ deriv = no-app-sₜ deriv refl