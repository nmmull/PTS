open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; ≢-sym)
open import Data.Product using (_×_; proj₁; proj₂; _,_; ∃; ∃-syntax; map₂; Σ; Σ-syntax)

module Specification where

record Spec : Set₁ where
  field
    Sort : Set
    axiom : Sort → Sort → Set
    rule : Sort → Sort → Sort → Set

a-functional : Spec → Set
a-functional 𝒮 = ∀ {s₁ s₂ t₁ t₂} →
  Spec.axiom 𝒮 s₁ s₂ →
  Spec.axiom 𝒮 t₁ t₂ →
  s₁ ≡ t₁ →
  s₂ ≡ t₂

r-functional : Spec → Set
r-functional 𝒮 = ∀ {s₁ s₂ s₃ t₁ t₂ t₃} →
  Spec.rule 𝒮 s₁ s₂ s₃ →
  Spec.rule 𝒮 t₁ t₂ t₃ →
  s₁ ≡ t₁ →
  s₂ ≡ t₂ →
  s₃ ≡ t₃

functional : Spec → Set
functional 𝒮 = a-functional 𝒮 × r-functional 𝒮

a-persistent : Spec → Set
a-persistent 𝒮 = ∀ {s₁ s₂ t₁ t₂} →
  Spec.axiom 𝒮 s₁ s₂ →
  Spec.axiom 𝒮 t₁ t₂ →
  s₂ ≡ t₂ →
  s₁ ≡ t₁

r-persistent : Spec → Set
r-persistent 𝒮 = ∀ {s₁ s₂ s₃} →
  Spec.rule 𝒮 s₁ s₂ s₃ →
  s₂ ≡ s₃

persistent : Spec → Set
persistent 𝒮 = functional 𝒮 × a-persistent 𝒮 × r-persistent 𝒮

s-stratified : Spec → Set
s-stratified = {!!}

r-stratified : Spec → Set
r-stratified = {!!}
