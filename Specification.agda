module Specification where

  record Spec : Set₁ where
    field
      Sort : Set
      axiom : Sort → Sort → Set
      rule : Sort → Sort → Sort → Set