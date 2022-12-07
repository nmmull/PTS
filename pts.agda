module PTS where

open import Data.Nat using (ℕ; _≰_; _<_; _≤_; _≤?_; _+_; suc; zero; pred; z≤n; s≤s)
open import Data.Nat.Properties using (1+n≰n; ≤∧≢⇒<; m≤n⇒m≤1+n)
open import Data.String using (String)
open import Data.Bool using (Bool; T)
open import Data.Bool.Properties using (T?)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (map′)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.Definitions using (DecidableEquality)
open Eq using (_≡_; _≢_; refl; cong; cong₂; subst; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)

m≤n⇒m≤1+n : ∀ {m n} → m ≤ n → m ≤ suc n
m≤n⇒m≤1+n z≤n       = z≤n
m≤n⇒m≤1+n (s≤s m≤n) = s≤s (m≤n⇒m≤1+n m≤n)

data Term : Set where
  s : ℕ → Term
  _♯_ : ℕ → ℕ → Term
  λˢ_∷_⇒_ : ℕ → Term → Term → Term
  Πˢ_∷_⇒_ : ℕ → Term → Term → Term
  _§_§_ : Term → ℕ → Term → Term

lift-map : (ℕ → ℕ) → ℕ → Term → Term
lift-map f = go where
  go : ℕ → Term → Term
  go x (s i) = s i
  go x (y ♯ i) with x ≤? y
  ...             | yes _ = f y ♯ i
  ...             | no  _ = y ♯ i
  go x (λˢ i ∷ m ⇒ n) = λˢ i ∷ go x m ⇒ go (suc x) n
  go x (Πˢ i ∷ a ⇒ b) = Πˢ i ∷ go x a ⇒ go (suc x) b 
  go x (m § i § n) = go x m § i § go x n

↑ : Term → Term
↑ = lift-map suc 0

↓ : Term → Term
↓ = lift-map pred 0

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

data Variable : Set where
  _♯_ : ℕ → ℕ → Variable

_≟_ : DecidableEquality Variable
(x ♯ i) ≟ (y ♯ j) with x Data.Nat.≟ y with i Data.Nat.≟ j
...                  | yes refl          | yes refl = yes refl
...                  | no prf            | _        = no λ { refl → prf refl }
...                  | _                 | no prf   = no λ { refl → prf refl } 

_[_/_] : Term → Term → Variable → Term
s i [ n / y ♯ j ] = s i
(x ♯ i) [ n / y ♯ j ] with (x ♯ i) ≟ (y ♯ j) 
...                      | yes _  = n
...                      | _ = x ♯ i
(λˢ i ∷ a ⇒ m) [ n / y ♯ j ] = λˢ i ∷ (a [ n / y ♯ j ]) ⇒ (m [ ↑ n / (suc y) ♯ j ])
(Πˢ i ∷ a ⇒ b) [ n / y ♯ j ] = Πˢ i ∷ (a [ n / y ♯ j ]) ⇒ (b [ ↑ n / (suc y) ♯ j ])
(m₁ § i § m₂) [ n / y ♯ j ] = (m₁ [ n / y ♯ j ]) § i § (m₂ [ n / y ♯ j ])

_[_/_]′ : Term → Term → Variable → Term
m [ n / x ]′ = ↓ (m [ ↑ n / x ]) 


data _⟶ᵇ_ : Term → Term → Set where
  beta-rule : {i : ℕ} → {a m n : Term} → ((λˢ i ∷ a ⇒ m) § i § n) ⟶ᵇ (m [ n / 0 ♯ i ]′)
  comp-pi1 : {i : ℕ} → {a b a' : Term} → a ⟶ᵇ a' → (Πˢ i ∷ a ⇒ b) ⟶ᵇ (Πˢ i ∷ a' ⇒ b)
  comp-pi2 : {i : ℕ} → {a b b' : Term} → b ⟶ᵇ b' → (Πˢ i ∷ a ⇒ b) ⟶ᵇ (Πˢ i ∷ a ⇒ b')
  comp-lam1 : {i : ℕ} → {a b a' : Term} → a ⟶ᵇ a' → (λˢ i ∷ a ⇒ b) ⟶ᵇ (λˢ i ∷ a' ⇒ b)
  comp-lam2 : {i : ℕ} → {a b b' : Term} → b ⟶ᵇ b' → (λˢ i ∷ a ⇒ b) ⟶ᵇ (λˢ i ∷ a ⇒ b')
  comp-app1 : {i : ℕ} → {a b a' : Term} → a ⟶ᵇ a' → (a § i § b) ⟶ᵇ (a' § i § b)
  comp-app2 : {i : ℕ} → {a b b' : Term} → b ⟶ᵇ b' → (a § i § b) ⟶ᵇ (a § i § b')

data _↠ᵇ_ : Term → Term → Set where
  refl : {i : ℕ} → {m : Term} → m ↠ᵇ m
  step : {i : ℕ} → {m n n' : Term} → m ⟶ᵇ n → n ↠ᵇ n' → m ↠ᵇ n'

↠ᵇ-trans : {m n p : Term} →
  m ↠ᵇ n →
  n ↠ᵇ p →
  m ↠ᵇ p
↠ᵇ-trans refl np = np
↠ᵇ-trans (step mn mn₁) np = step mn (↠ᵇ-trans mn₁ np)

data Context : Set where
  ∅ : Context
  _,_∷_ : Context → Variable → Term → Context

_∉_ : Variable → Context → Set
(x ♯ i) ∉ ∅ = ⊤
(x ♯ i) ∉ (Γ , y ♯ j ∷ _) with (x ♯ i) ≟ (y ♯ j)
...                          | yes _ = (x ♯ i) ∉ Γ
...                          | no  _ = ⊥

postulate top-sort : ℕ
postulate rule : ℕ → ℕ → Set

data _⊢_∷_ : Context → Term → Term → Set where

  axiom : {i : ℕ} →
    i < top-sort →
    ∅ ⊢ s i ∷ s (suc i)

  var-intro : {x i : ℕ} → {Γ : Context} → {a : Term} →
    (x ♯ i) ∉ Γ →
    Γ ⊢ a ∷ s i →
    (Γ , x ♯ i ∷ a) ⊢ x ♯ i ∷ a

  weaken : {x i j : ℕ} → {Γ : Context} → {m a b : Term} →
    (x ♯ j) ∉ Γ →
    Γ ⊢ m ∷ a →
    Γ ⊢ b ∷ s j →
    (Γ , x ♯ j ∷ b) ⊢ m ∷ a

  pi-intro : {x i j : ℕ} → {Γ : Context} → {a b : Term} →
    rule i j →
    Γ ⊢ a ∷ s i →
    (Γ , x ♯ i ∷ a) ⊢ b [ x ♯ i / 0 ♯ i ]′ ∷ s j →
    Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j

  abstr : {x i j : ℕ} → {Γ : Context} → {m a b : Term} →
    (Γ , x ♯ i ∷ a) ⊢ m [ x ♯ i / 0 ♯ i ]′ ∷ (b [ x ♯ i / 0 ♯ i ]′) →
    Γ ⊢ Πˢ i ∷ a ⇒ b ∷ s j →
    Γ ⊢ (λˢ i ∷ a ⇒ m) ∷ (Πˢ i ∷ a ⇒ b)

  app : {i : ℕ} → {Γ : Context} → {m n a b c : Term} →
    Γ ⊢ m ∷ (Πˢ i ∷ a ⇒ b) →
    Γ ⊢ n ∷ a →
    c ≡ b [ n / 0 ♯ i ]′ →
    Γ ⊢ (m § i § n) ∷ c

  conv : {i : ℕ} → {Γ : Context} → {m a b : Term} →
    Γ ⊢ m ∷ a →
    Γ ⊢ b ∷ s i →
    b ↠ᵇ a →
    Γ ⊢ m ∷ b

deg : Term → ℕ
deg (s i) = suc (suc i)
deg (x ♯ i) = i
deg (λˢ _ ∷ _ ⇒ m) = deg m
deg (Πˢ _ ∷ _ ⇒ m) = deg m 
deg (m § _ § _) = deg m

sᵢ≡sⱼ→i≡j : {i j : ℕ} → s i ≡ s j → i ≡ j
sᵢ≡sⱼ→i≡j refl = refl

sᵢ≢sⱼ→i≢j : {i j : ℕ} → s i ≢ s j → i ≢ j
sᵢ≢sⱼ→i≢j neq refl = neq refl

i≢j⇒sᵢ≢sⱼ : {i j : ℕ} → i ≢ j → s i ≢ s j
i≢j⇒sᵢ≢sⱼ neq refl = neq refl

i<j⇒i≢j : {i j : ℕ} → i < j → i ≢ j
i<j⇒i≢j (s≤s i<j) refl = ⊥-elim (1+n≰n i<j)

top-sort-not-deriv : {Γ : Context} → {m a : Term} →
  Γ ⊢ m ∷ a →
  m ≢ s top-sort
top-sort-not-deriv (axiom prf) = i≢j⇒sᵢ≢sⱼ (i<j⇒i≢j prf)
top-sort-not-deriv (var-intro x deriv) ()
top-sort-not-deriv (weaken _ deriv _) = top-sort-not-deriv deriv
top-sort-not-deriv (pi-intro _ _ _) ()
top-sort-not-deriv (abstr _ _) ()
top-sort-not-deriv (app _ _ _) ()
top-sort-not-deriv (conv deriv _ _) = top-sort-not-deriv deriv

no-var-top-sort : {x i : ℕ} → {Γ : Context} → {a : Term} →
  Γ ⊢ x ♯ i ∷ a →
  a ≢ s top-sort
no-var-top-sort (var-intro _ deriv) = top-sort-not-deriv deriv
no-var-top-sort (weaken _ deriv _) = no-var-top-sort deriv
no-var-top-sort (conv _ deriv _) = top-sort-not-deriv deriv

no-lam-top-sort : {i : ℕ} → {Γ : Context} → {a m b : Term} →
  Γ ⊢ λˢ i ∷ a ⇒ m ∷ b →
  b ≢ s top-sort
no-lam-top-sort (weaken _ deriv _) = no-lam-top-sort deriv
no-lam-top-sort (abstr deriv deriv₁) ()
no-lam-top-sort (conv _ deriv _) = top-sort-not-deriv deriv

sort-not-var : {i x j : ℕ} →
  s i ≢ x ♯ j
sort-not-var ()

sort-sub : {i j : ℕ} → {Γ : Context} → {m n : Term} →
  s i ≡ ↓ (m [ ↑ n / 0 ♯ j ]) →
  (m ≡ s i) ⊎ n ≡ s i
sort-sub {m = s k} eq = inj₁ (sym eq)
sort-sub {j = j} {m = x ♯ k} eq with (x ♯ k) ≟ (0 ♯ j)
...                        | yes p = inj₂ (sym (trans eq ↓↑-id))
...                        | no _  = inj₂ (⊥-elim (sort-not-var eq))

no-app-top-sort : {i : ℕ} → {Γ : Context} → {m n a : Term} →
  Γ ⊢ m § i § n ∷ a →
  a ≢ s top-sort
no-app-top-sort (weaken _ deriv _) = no-app-top-sort deriv
no-app-top-sort (app m-deriv n-deriv a≡sub) a≡s = [
  (λ { b≡s → {!!}} )
  , ( λ { n≡s → (top-sort-not-deriv n-deriv) n≡s } ) ] (sort-sub (trans (sym a≡s) a≡sub))
no-app-top-sort (conv _ deriv _) = top-sort-not-deriv deriv

gen-sort₁ : {i : ℕ} → {Γ : Context} → {a : Term} →
  Γ ⊢ s i ∷ a →
  a ↠ᵇ s (suc i)
gen-sort₁ (axiom x) = refl
gen-sort₁ (weaken _ deriv _) = gen-sort₁ deriv
gen-sort₁ (conv deriv deriv₁ b↠ᵇa) = ↠ᵇ-trans b↠ᵇa (gen-sort₁ deriv)

sort-nf : {i : ℕ} → {a : Term} →
  s i ↠ᵇ a →
  s i ≡ a
sort-nf refl = refl

gen-sort₂ : {i j : ℕ} → {Γ : Context} →
  Γ ⊢ s i ∷ s j →
  j ≡ suc i
gen-sort₂ deriv = sᵢ≡sⱼ→i≡j (sort-nf (gen-sort₁ deriv))

data WFC : Context → Set where
  ∅-wf : WFC ∅
  ext-wf : {x i : ℕ} → {Γ : Context} → {a : Term} →
    (x ♯ i) ∉ Γ →
    Γ ⊢ a ∷ s i →
    WFC Γ →
    WFC (Γ , x ♯ i ∷ a)

deriv-context-wf : {Γ : Context} → {m a : Term} →
  Γ ⊢ m ∷ a →
  WFC Γ
deriv-context-wf = go where
  go : {Γ : Context} → {m a : Term} → Γ ⊢ m ∷ a → WFC Γ
  go (axiom x) = ∅-wf
  go (var-intro fresh deriv) = ext-wf fresh deriv (go (deriv))
  go (weaken fresh _ deriv) = ext-wf fresh deriv (go (deriv))
  go (pi-intro _ deriv _) = go deriv
  go (abstr _ deriv) = go deriv
  go (app deriv _ _) = go deriv
  go (conv deriv _ _) = go deriv

start : {i : ℕ} → {Γ : Context} →
  i < top-sort →
  WFC Γ →
  Γ ⊢ s i ∷ s (suc i)
start i<t ∅-wf = axiom i<t
start i<t (ext-wf fresh a-deriv Γ-wf) = weaken fresh (start i<t Γ-wf) a-deriv

1+n≤m⇒n≤m : {n m : ℕ} → suc n ≤ m → n ≤ m
1+n≤m⇒n≤m (s≤s prf) = m≤n⇒m≤1+n prf

m≡n∧m≤p→n≤p : {n m p : ℕ} → m ≡ n → m ≤ p → n ≤ p
m≡n∧m≤p→n≤p refl prf = prf

s-as-sub : {i : ℕ} → {b n : Term} →
  s i ≡ ↓ (b [ ↑ n / 0 ♯ (suc i) ]) →
  (n ≡ s i × b ≡ 0 ♯ (suc i)) ⊎ b ≡ s i
s-as-sub = {!!} {- Not sure -}

≤-top-sort : {i : ℕ} → {Γ : Context} → {a : Term} →
  Γ ⊢ a ∷ s i →
  i ≤ top-sort
≤-top-sort (axiom prf) = prf
≤-top-sort (var-intro {i = j} _ deriv) =
  1+n≤m⇒n≤m
    (m≡n∧m≤p→n≤p
      (gen-sort₂ deriv)
      (≤-top-sort deriv))
≤-top-sort (weaken _ deriv _) = ≤-top-sort deriv
≤-top-sort (pi-intro _ _ deriv) = ≤-top-sort deriv
≤-top-sort (app deriv deriv₁ x) = {!!}
≤-top-sort (conv _ deriv _) =
  1+n≤m⇒n≤m
    (m≡n∧m≤p→n≤p
      (gen-sort₂ deriv)
      (≤-top-sort deriv))

pi-not-sort : {i j : ℕ} → {a b : Term} → Πˢ i ∷ a ⇒ b ≢ s j
pi-not-sort ()

type-correctness : {Γ : Context} → {m a : Term} →
  Γ ⊢ m ∷ a →
  a ≢ s top-sort →
  Σ[ i ∈ ℕ ] Γ ⊢ a ∷ s i
type-correctness (axiom {i} i<t) prf = (suc (suc i) , axiom (≤∧≢⇒< i<t (sᵢ≢sⱼ→i≢j prf)))
type-correctness (var-intro {i = i} fresh deriv) _ = (i , weaken fresh deriv deriv)
type-correctness (weaken fresh m-deriv b-deriv) prf =
  let (i , done) = type-correctness m-deriv prf in
    (i , weaken fresh done b-deriv)
type-correctness (pi-intro {j = j} x deriv deriv₁) prf =
  (suc j ,
    start
    (≤∧≢⇒< (≤-top-sort deriv₁) (sᵢ≢sⱼ→i≢j prf))
    (deriv-context-wf deriv))
type-correctness (abstr {j = j} _ t-deriv) _ = (j , t-deriv)
type-correctness (app m-deriv deriv₁ x) prf =
  let (j , _) = type-correctness m-deriv pi-not-sort in
    (j , {!!})
type-correctness (conv {i = i} _ a-deriv _) _ = (i , a-deriv)

{-
bind-var : String → Term¹ → Term¹
bind-var = go 0 where
  go : ℕ → String → Term¹ → Term¹
  go i x (s¹ j) =  s¹ j
  go i x f⟪ x₁ ⟫¹ with x ≟ x₁
  ...                | yes _ = b⟪ i ⟫¹
  ...                | no _ = f⟪ x₁ ⟫¹
  go i x b⟪ x₁ ⟫¹ =  b⟪ x₁ ⟫¹
  go i x (λ¹ t ⇒ t₁) = λ¹ go i x t ⇒ go (suc i) x t
  go i x (Π¹ t ⇒ t₁) = Π¹ go i x t ⇒ go (suc i) x t
  go i x (t $¹ t₁) = go i x t $¹ go i x t₁

⦉_⦊ : Term⁰ → Term¹
⦉_⦊ = go where
  go : Term⁰ → Term¹
  go (s⁰ i) = s¹ i
  go ⟪ x ⟫⁰ = f⟪ x ⟫¹
  go (λ⁰ x ∷ t ⇒ t₁) = λ¹ go t ⇒ bind-var x (go t₁)
  go (Π⁰ x ∷ t ⇒ t₁) = Π¹ go t ⇒ bind-var x (go t₁)
  go (t $⁰ t₁) = go t $¹ go t₁

t : Term⁰
t = λ⁰ "x" ∷ s⁰ 0 ⇒ (⟪ "x" ⟫⁰ $⁰ ⟪ "z" ⟫⁰)

test : ⦉ t ⦊ ≡ λ¹ s¹ 0 ⇒ (b⟪ 0 ⟫¹ $¹ f⟪ "z" ⟫¹)
test = refl
-}
