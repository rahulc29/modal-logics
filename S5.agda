{-# OPTIONS --cubical --guardedness #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Relation.Binary

module S5 (V : Set) where

-- Syntax of modal logic S5

data Term : Set where
  `_ : V → Term
  ⊥ : Term
  _⊃_ : Term → Term → Term
  □_ : Term → Term

-- Two extra constructors for derivable operators

-- negation
～_ : Term → Term
～ p = p ⊃ ⊥

-- Diamond
-- Modality of "possibly"
-- This is not a constructive interpretation but ok
◇_ : Term → Term
◇ p = ～ (□ (～ p))

-- Contexts
-- = Family of sets indexed by terms

Context : Set₁
Context = Term → Set

_∈_ : Term → Context → Set
t ∈ Γ = Γ t

data Empty : Set where
⟨⟩ : Context
⟨⟩ _ = Empty


-- Hilbert Styled Deductive System
data _⊢_ : Context → Term → Set₁ where
  axiom : ∀ {Γ t} → t ∈ Γ → Γ ⊢ t
  pl-2 : ∀ {Γ s t} → Γ ⊢ (s ⊃ (t ⊃ s))
  pl-3 : ∀ {Γ r s t} → Γ ⊢ ((r ⊃ (s ⊃ t)) ⊃ ((r ⊃ s) ⊃ (r ⊃ t)))
  ～-pl-2 : ∀ {Γ p q} → Γ ⊢ (((～ p) ⊃ (～ q)) ⊃ (((～ p) ⊃ q) ⊃ p))
  k : ∀ {Γ p q} → Γ ⊢ ( (□ (p ⊃ q)) ⊃ ((□ p) ⊃ (□ q)))
  t : ∀ {Γ p} → Γ ⊢ ((□ p) ⊃ p)
  s4 : ∀ {Γ p} → Γ ⊢ ((□ p) ⊃ (□ (□ p)))
  b : ∀ {Γ p} → Γ ⊢ (p ⊃ (□ (◇ p)))
  mp : ∀ {Γ p q} → Γ ⊢ (p ⊃ q) → Γ ⊢ p → Γ ⊢ q
  ne : ∀ {Γ p} → Γ ⊢ p → Γ ⊢ (□ p)
  dne : ∀ {Γ p} → Γ ⊢ (p ⊃ (～ (～ p)))

World : Set₁ 
World = Term → Set

record Model : Set₁ where
  field
    worlds : World → Set
    access : World → World → Set
    eval : V → World → Bool
    reflexive : ∀ {w : World} → access w w
    symmetric : ∀ {w v : World} → access w v → access v w
    transitive : ∀ {w v u : World} → access w v → access v u → access w u
open Model
