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

-------------------------------------------------------------------------------
-- Lifting and Dropping

lift-drop-lemma : {x : ℕ} → {m : Term} →
  lift-map pred x (lift-map suc x m) ≡ m
lift-drop-lemma {x} {m} = go x m where
  l : ℕ → Term → Term
  l = lift-map suc
  d : ℕ → Term → Term
  d = lift-map pred
  go : (x : ℕ) → (m : Term) →
    d x (l x m) ≡ m
  go x (s i) = refl
  go x (y ♯ i) with x ≤? y
  go x (y ♯ i)    | yes p' with x ≤? suc y
  go x (y ♯ i)    | yes p'    | yes _ = refl
  go x (y ♯ i)    | yes p'    | no ¬p = ⊥-elim (¬p (m≤n⇒m≤1+n p'))
  go x (y ♯ i)    | no ¬p with x ≤? y
  go x (y ♯ i)    | no ¬p    | yes p = ⊥-elim (¬p p)
  go x (y ♯ i)    | no ¬p    | no _ = refl
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

↓↑-id : {n : Term} →
  ↓ (↑ n) ≡ n
↓↑-id = lift-drop-lemma {x = 0}


-------------------------------------------------------------------------------
-- Generation Lemma (Sorts)

s-gen₁ : {i : ℕ} → {Γ : Context} → {a : Term} →
  Γ ⊢ s i ∷ a →
  a ↠ᵇ s (suc i)
s-gen₁ {i} (axiom x) = β-refl {i}
s-gen₁ (weaken _ deriv _) = s-gen₁ deriv
s-gen₁ (conv deriv deriv₁ b↠ᵇa) = ↠ᵇ-trans b↠ᵇa (s-gen₁ deriv)

sort-nf : {i : ℕ} → {a : Term} →
  s i ↠ᵇ a →
  s i ≡ a
sort-nf β-refl = refl

s-gen₂ : {i j : ℕ} → {Γ : Context} →
  Γ ⊢ s i ∷ s j →
  j ≡ suc i
s-gen₂ deriv = sᵢ≡sⱼ→i≡j (sort-nf (s-gen₁ deriv))

-------------------------------------------------------------------------------
-- Generation Lemma (Π-Types)

Π-gen₁ : {i j x : ℕ} → {Γ : Context} → {a b : Term} →
  Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j →
  (x ♯ i) ∉ Γ →
  (Γ , x ♯ i ∷ a) ⊢ b [ x ♯ i / 0 ♯ i ]′ ∷ s j
Π-gen₁ = {!   !}

Π-gen₂ : {i j : ℕ} → {Γ : Context} → {a b n : Term} →
  Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j →
  Γ ⊢ n ∷ a →
  Γ ⊢ b [ n / 0 ♯ i ]′ ∷ s j
Π-gen₂ = {!   !}

-------------------------------------------------------------------------------
-- Start Lemma

start : {i : ℕ} → {Γ : Context} →
  i < top-sort →
  WFC Γ →
  Γ ⊢ s i ∷ s (suc i)
start i<t ∅-wf = axiom i<t
start {i} i<t (ext-wf fresh a-deriv Γ-wf) =
  weaken {i = i} fresh (start i<t Γ-wf) a-deriv

-------------------------------------------------------------------------------
-- sₜ is the largest sort

≤sₜ : {i : ℕ} → {Γ : Context} → {a : Term} →
  Γ ⊢ a ∷ s i →
  i ≤ top-sort
≤sₜ (axiom prf) = prf
≤sₜ (var-intro {i = j} _ deriv) =
  1+n≤m⇒n≤m
    (m≡n∧m≤p⇒n≤p
      (s-gen₂ deriv)
      (≤sₜ deriv))
≤sₜ (weaken _ deriv _) = ≤sₜ deriv
≤sₜ (pi-intro _ _ deriv) = ≤sₜ deriv
≤sₜ (app deriv deriv₁ x) = {!!}
≤sₜ (conv _ deriv _) =
  1+n≤m⇒n≤m
    (m≡n∧m≤p⇒n≤p
      (s-gen₂ deriv)
      (≤sₜ deriv))

-------------------------------------------------------------------------------
-- Type Correctness

type-correctness : {Γ : Context} → {m a : Term} →
  Γ ⊢ m ∷ a →
  a ≢ s top-sort →
  Σ[ i ∈ ℕ ] Γ ⊢ a ∷ s i
type-correctness (axiom {i} i<t) prf = (suc (suc i) , axiom (≤∧≢⇒< i<t (sᵢ≢sⱼ⇒i≢j prf)))
type-correctness (var-intro {i = i} fresh deriv) _ = (i , weaken {i = i} fresh deriv deriv)
type-correctness (weaken fresh m-deriv b-deriv) prf =
  let (i , done) = type-correctness m-deriv prf in
    (i , weaken {i = i} fresh done b-deriv)
type-correctness (pi-intro {j = j} x deriv deriv₁) prf =
  (suc j ,
    start
    (≤∧≢⇒< (≤sₜ deriv₁) (sᵢ≢sⱼ⇒i≢j prf))
    (Γ-wf deriv))
type-correctness (abstr {j = j} _ t-deriv) _ = (j , t-deriv)
type-correctness {Γ = Γ} (app {c = c} m-deriv n-deriv c≡sub) c≢sₜ = 
  let (j , Π-deriv) = type-correctness m-deriv (λ { () }) in
    (j , subst (λ { n → Γ ⊢ n ∷ s j }) (sym c≡sub) (Π-gen₂ Π-deriv n-deriv))
type-correctness (conv {i = i} _ a-deriv _) _ = (i , a-deriv)

-------------------------------------------------------------------------------
-- Top Sort Lemma

sₜ-not-typable : {Γ : Context} → {m a : Term} →
  Γ ⊢ m ∷ a →
  m ≢ sₜ
sₜ-not-typable (axiom prf) = i≢j⇒sᵢ≢sⱼ (m<n⇒m≢n prf)
sₜ-not-typable (var-intro x deriv) ()
sₜ-not-typable (weaken _ deriv _) = sₜ-not-typable deriv
sₜ-not-typable (pi-intro _ _ _) ()
sₜ-not-typable (abstr _ _) ()
sₜ-not-typable (app _ _ _) ()
sₜ-not-typable (conv deriv _ _) = sₜ-not-typable deriv

no-var-sₜ : {x i : ℕ} → {Γ : Context} → {a : Term} →
  Γ ⊢ x ♯ i ∷ a →
  a ≢ sₜ
no-var-sₜ (var-intro _ deriv) = sₜ-not-typable deriv
no-var-sₜ (weaken _ deriv _) = no-var-sₜ deriv
no-var-sₜ (conv _ deriv _) = sₜ-not-typable deriv

no-λ-sₜ : {i : ℕ} → {Γ : Context} → {a m b : Term} →
  Γ ⊢ λˢ i ∷ a ⇒ m ∷ b →
  b ≢ sₜ
no-λ-sₜ (weaken _ deriv _) = no-λ-sₜ deriv
no-λ-sₜ (abstr deriv deriv₁) ()
no-λ-sₜ (conv _ deriv _) = sₜ-not-typable deriv

sort-not-var : {i x j : ℕ} →
  s i ≢ x ♯ j
sort-not-var ()

sort-sub : {i j : ℕ} → {Γ : Context} → {m n : Term} →
  s i ≡ m [ n / 0 ♯ j ]′ →
  m ≡ s i ⊎ n ≡ s i
sort-sub {m = s k} eq = inj₁ (sym eq)
sort-sub {j = j} {m = x ♯ k} eq with (x ♯ k) ≟ (0 ♯ j)
...                        | yes p = inj₂ (sym (trans eq ↓↑-id))
...                        | no _  = inj₂ (⊥-elim (sort-not-var eq))

no-app-sₜ : {i : ℕ} → {Γ : Context} → {m n a : Term} →
  Γ ⊢ m § i § n ∷ a →
  a ≢ sₜ
no-app-sₜ (weaken _ deriv _) = no-app-sₜ deriv
no-app-sₜ 
  {i = i} {Γ = Γ} {n = n}
  (app {a = a} {b = b} m-deriv n-deriv c≡sub) c≡s =
    [ lem₃ , lem₄ ] lem₂ where
      lem : sₜ ≡ b [ n / 0 ♯ i ]′
      lem = trans (sym c≡s) c≡sub
      lem₂ : b ≡ sₜ ⊎ n ≡ sₜ
      lem₂ = sort-sub {Γ = Γ} lem
      lem₂₁ : Σ[ j ∈ ℕ ] Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j
      lem₂₁ = type-correctness m-deriv λ { () }
      lem₃ : b ≢ sₜ
      lem₃ = {!   !}
      lem₄ : n ≢ sₜ
      lem₄ = sₜ-not-typable n-deriv 
no-app-sₜ (conv _ deriv _) = sₜ-not-typable deriv

Γ⊬sₜ∷a : {Γ : Context} → {a : Term} →
  Γ ⊬ sₜ ∷ a
Γ⊬sₜ∷a deriv = sₜ-not-typable deriv refl

Γ⊬x∷sₜ : {x i : ℕ} → {Γ : Context} →
  Γ ⊬ x ♯ i ∷ sₜ
Γ⊬x∷sₜ deriv = no-var-sₜ deriv refl

Γ⊬λ∷sₜ : {i : ℕ} → {Γ : Context} → {a m : Term} →
  Γ ⊬ λˢ i ∷ a ⇒ m ∷ sₜ
Γ⊬λ∷sₜ deriv = no-λ-sₜ deriv refl

Γ⊬mn∷sₜ : {i : ℕ} → {Γ : Context} → {m n : Term} →
  Γ ⊬ m § i § n ∷ sₜ
Γ⊬mn∷sₜ deriv = no-app-sₜ deriv refl