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

-------------------------------------------------------------------------------
-- Weakening

weaken : {x j : ℕ} {Γ : ℂ} {m a b : 𝕋} →
  (x ♯ j) ∉ Γ →
  𝕊 ∥ Γ ⊢ m ∷ a →
  𝕊 ∥ Γ ⊢ b ∷ s j →
  𝕊 ∥ (Γ , x ♯ j ∷ b) ⊢ m ∷ a
weaken fresh (axiom i<t) b-deriv =
  sort-weaken fresh (axiom i<t) b-deriv
weaken fresh (var-intro fr m-deriv) b-deriv =
  var-weaken fresh (var-intro fr m-deriv) b-deriv
weaken fresh (sort-weaken fr m-deriv c-deriv) b-deriv =
  sort-weaken fresh (sort-weaken fr m-deriv c-deriv) b-deriv
weaken fresh (var-weaken fr m-deriv c-deriv) b-deriv =
  var-weaken fresh (var-weaken fr m-deriv c-deriv) b-deriv
weaken fresh (pi-intro r a-deriv c-deriv) b-deriv = {!   !}
weaken fresh (abstr m-deriv m-deriv₁) b-deriv = {!   !}
weaken fresh (app m-deriv n-deriv eq) b-deriv =
  app
    (weaken fresh m-deriv b-deriv)
    (weaken fresh n-deriv b-deriv)
    eq
weaken fresh (conv-red m-deriv a-deriv eq) b-deriv = 
  conv-red
    (weaken fresh m-deriv b-deriv)
    (weaken fresh a-deriv b-deriv)
    eq
weaken fresh (conv-exp m-deriv a-deriv eq) b-deriv =
  conv-exp
    (weaken fresh m-deriv b-deriv)
    (weaken fresh a-deriv b-deriv)
    eq

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
-- Substitution Lemma

sub-lemma : {x i : ℕ} {Γ' Γ Δ : ℂ} {m n a b : 𝕋} →
  𝕊 ∥ ((Γ , x ♯ i ∷ a) ∘ Δ) ⊢ m ∷ b →
  𝕊 ∥ Γ ⊢ n ∷ a →
  𝕊 ∥ (Γ ∘ (Δ [ n / x ♯ i ]ᶜ))  ⊢ m [ n / x ♯ i ] ∷ (b [ n / x ♯ i ])
sub-lemma = {!   !}

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