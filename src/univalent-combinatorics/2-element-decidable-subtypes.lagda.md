---
title: 2-element decidable subtypes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.2-element-decidable-subtypes where

open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ; zero-ℕ)
open import elementary-number-theory.equality-natural-numbers using (has-decidable-equality-ℕ)

open import foundation.automorphisms using (Aut)
open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-equality using
  ( has-decidable-equality; is-set-has-decidable-equality)
open import foundation.decidable-propositions using
  ( decidable-Prop; is-decidable-type-decidable-Prop; is-prop-type-decidable-Prop; type-decidable-Prop;
    equiv-bool-decidable-Prop; prop-decidable-Prop)
open import foundation.decidable-subtypes using
  ( decidable-subtype; type-decidable-subtype; subtype-decidable-subtype;
    is-decidable-subtype; is-decidable-subtype-subtype-decidable-subtype;
    type-prop-decidable-subtype; is-prop-type-prop-decidable-subtype)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-coprod; is-decidable-equiv; is-decidable-neg;
    dn-elim-is-decidable; is-prop-is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using
  ( _≃_; _∘e_; inv-equiv; is-equiv-has-inverse; id-equiv; map-inv-equiv; map-equiv;
    left-inverse-law-equiv)
open import foundation.functions using (_∘_; id)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; refl; inv; ap; _∙_; tr)
open import foundation.logical-equivalences using (iff-equiv)
open import foundation.mere-equivalences using (transitive-mere-equiv)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop; unit-trunc-Prop;
    trunc-Prop)
open import foundation.propositions using
  ( UU-Prop; is-prop; type-Prop; is-prop-function-type; eq-is-prop; is-prop-is-prop)
open import foundation.sets using (Id-Prop)
open import foundation.subtypes using (subtype; eq-subtype; equiv-subtype-equiv)
open import foundation.type-arithmetic-coproduct-types using
  ( map-commutative-coprod; is-equiv-map-commutative-coprod)
open import foundation.univalence using (eq-equiv)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc; lzero)

open import univalent-combinatorics.2-element-subtypes using
  ( type-prop-standard-2-Element-Subtype;
    is-prop-type-prop-standard-2-Element-Subtype;
    subtype-standard-2-Element-Subtype; type-standard-2-Element-Subtype;
    equiv-type-standard-2-Element-Subtype;
    has-two-elements-type-standard-2-Element-Subtype)
open import univalent-combinatorics.2-element-types using
  ( has-two-elements; 2-Element-Type; swap-2-Element-Type;
    map-swap-2-Element-Type; compute-swap-2-Element-Type;
    contradiction-3-distinct-element-2-Element-Type)
open import univalent-combinatorics.decidable-subtypes using (is-finite-decidable-subtype)
open import univalent-combinatorics.dependent-product-finite-types using (is-finite-Π)
open import univalent-combinatorics.finite-types using
  ( has-cardinality; UU-Fin-Level; type-UU-Fin-Level; mere-equiv-UU-Fin; is-finite; 
    equiv-has-cardinality-id-number-of-elements-is-finite; number-of-elements-is-finite;
    is-finite-type-UU-Fin-Level; is-finite-equiv; is-finite-Fin)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; zero-Fin; one-Fin; equiv-bool-Fin-two-ℕ)
```

## Idea

A 2-element decidable subtype of a type `A` is a decidable subtype of `A` of which the underlying type has 2 elements.

## Definition

### The type of 2-element decidable subtypes

```agda
2-Element-Decidable-Subtype :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
2-Element-Decidable-Subtype l2 X =
  Σ (decidable-subtype l2 X) (λ P → has-two-elements (type-decidable-subtype P))

module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Decidable-Subtype l2 X)
  where
  
  decidable-subtype-2-Element-Decidable-Subtype : decidable-subtype l2 X
  decidable-subtype-2-Element-Decidable-Subtype = pr1 P

  subtype-2-Element-Decidable-Subtype : subtype l2 X
  subtype-2-Element-Decidable-Subtype =
    subtype-decidable-subtype decidable-subtype-2-Element-Decidable-Subtype

  is-decidable-subtype-subtype-2-Element-Decidable-Subtype :
    is-decidable-subtype subtype-2-Element-Decidable-Subtype
  is-decidable-subtype-subtype-2-Element-Decidable-Subtype =
    is-decidable-subtype-subtype-decidable-subtype
      decidable-subtype-2-Element-Decidable-Subtype

  type-prop-2-Element-Decidable-Subtype : X → UU l2
  type-prop-2-Element-Decidable-Subtype =
    type-prop-decidable-subtype decidable-subtype-2-Element-Decidable-Subtype

  is-prop-type-prop-2-Element-Decidable-Subtype :
    (x : X) → is-prop (type-prop-2-Element-Decidable-Subtype x)
  is-prop-type-prop-2-Element-Decidable-Subtype =
    is-prop-type-prop-decidable-subtype
      decidable-subtype-2-Element-Decidable-Subtype

  eq-type-prop-2-Element-Decidable-Subtype :
    {x : X} {y z : type-prop-2-Element-Decidable-Subtype x} → Id y z
  eq-type-prop-2-Element-Decidable-Subtype {x} =
    eq-is-prop (is-prop-type-prop-2-Element-Decidable-Subtype x)
      
  type-2-Element-Decidable-Subtype : UU (l1 ⊔ l2)
  type-2-Element-Decidable-Subtype =
    type-decidable-subtype decidable-subtype-2-Element-Decidable-Subtype

  has-two-elements-type-2-Element-Decidable-Subtype :
    has-two-elements type-2-Element-Decidable-Subtype
  has-two-elements-type-2-Element-Decidable-Subtype = pr2 P

  2-element-type-2-Element-Decidable-Subtype : 2-Element-Type (l1 ⊔ l2)
  pr1 2-element-type-2-Element-Decidable-Subtype =
    type-2-Element-Decidable-Subtype
  pr2 2-element-type-2-Element-Decidable-Subtype =
    has-two-elements-type-2-Element-Decidable-Subtype
```

### The standard 2-element decidable subtypes in a type with decidable equality

```agda
module _
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (np : ¬ (Id x y))
  where

  type-prop-standard-2-Element-Decidable-Subtype : X → UU l
  type-prop-standard-2-Element-Decidable-Subtype =
    type-prop-standard-2-Element-Subtype
      ( pair X (is-set-has-decidable-equality d))
      ( np)

  is-prop-type-prop-standard-2-Element-Decidable-Subtype :
    (z : X) → is-prop (type-prop-standard-2-Element-Decidable-Subtype z)
  is-prop-type-prop-standard-2-Element-Decidable-Subtype =
    is-prop-type-prop-standard-2-Element-Subtype
      ( pair X (is-set-has-decidable-equality d))
      ( np)

  is-decidable-type-prop-standard-2-Element-Decidable-Subtype :
    (z : X) → is-decidable (type-prop-standard-2-Element-Decidable-Subtype z)
  is-decidable-type-prop-standard-2-Element-Decidable-Subtype z =
    is-decidable-coprod (d x z) (d y z)

  subtype-standard-2-Element-Decidable-Subtype : subtype l X
  subtype-standard-2-Element-Decidable-Subtype =
    subtype-standard-2-Element-Subtype
      ( pair X (is-set-has-decidable-equality d))
      ( np)
      
  decidable-subtype-standard-2-Element-Decidable-Subtype : decidable-subtype l X
  pr1 (decidable-subtype-standard-2-Element-Decidable-Subtype z) =
    type-prop-standard-2-Element-Decidable-Subtype z
  pr1 (pr2 (decidable-subtype-standard-2-Element-Decidable-Subtype z)) =
    is-prop-type-prop-standard-2-Element-Decidable-Subtype z
  pr2 (pr2 (decidable-subtype-standard-2-Element-Decidable-Subtype z)) =
    is-decidable-type-prop-standard-2-Element-Decidable-Subtype z

  type-standard-2-Element-Decidable-Subtype : UU l
  type-standard-2-Element-Decidable-Subtype =
    type-standard-2-Element-Subtype
      ( pair X (is-set-has-decidable-equality d))
      ( np)

  equiv-type-standard-2-Element-Decidable-Subtype :
    Fin 2 ≃ type-standard-2-Element-Decidable-Subtype
  equiv-type-standard-2-Element-Decidable-Subtype =
    equiv-type-standard-2-Element-Subtype
      ( pair X (is-set-has-decidable-equality d))
      ( np)

  has-two-elements-type-standard-2-Element-Decidable-Subtype :
    has-two-elements type-standard-2-Element-Decidable-Subtype
  has-two-elements-type-standard-2-Element-Decidable-Subtype =
    has-two-elements-type-standard-2-Element-Subtype
      ( pair X (is-set-has-decidable-equality d))
      ( np)

  2-element-type-standard-2-Element-Decidable-Subtype : 2-Element-Type l
  pr1 2-element-type-standard-2-Element-Decidable-Subtype =
    type-standard-2-Element-Decidable-Subtype
  pr2 2-element-type-standard-2-Element-Decidable-Subtype =
    has-two-elements-type-standard-2-Element-Decidable-Subtype

  standard-2-Element-Decidable-Subtype : 2-Element-Decidable-Subtype l X
  pr1 standard-2-Element-Decidable-Subtype =
    decidable-subtype-standard-2-Element-Decidable-Subtype
  pr2 standard-2-Element-Decidable-Subtype =
    has-two-elements-type-standard-2-Element-Decidable-Subtype

module _
  {l : Level} {X : UU l} (d : has-decidable-equality X) {x y : X}
  (np : ¬ (Id x y))
  where

  is-commutative-standard-2-Element-Decidable-Subtype :
    Id
      ( standard-2-Element-Decidable-Subtype d np)
      ( standard-2-Element-Decidable-Subtype d (λ p → np (inv p)))
  is-commutative-standard-2-Element-Decidable-Subtype =
    eq-pair-Σ
      ( eq-htpy
        (λ z →
          eq-pair-Σ
            ( eq-equiv
              ( coprod (Id x z) (Id y z))
              ( coprod (Id y z) (Id x z))
              ( pair
                ( map-commutative-coprod (Id x z) (Id y z))
                ( is-equiv-map-commutative-coprod (Id x z) (Id y z))))
            ( eq-pair-Σ
              ( eq-is-prop
                ( is-prop-is-prop
                  ( type-decidable-Prop
                    ( pr1 (standard-2-Element-Decidable-Subtype d (λ p → np (inv p))) z))))
              ( eq-is-prop
                ( is-prop-is-decidable
                  (is-prop-type-decidable-Prop
                    ( pr1 (standard-2-Element-Decidable-Subtype d (λ p → np (inv p))) z)))))))
      ( eq-is-prop is-prop-type-trunc-Prop)
```

### Swapping the elements in a 2-element subtype

```agda
module _
  {l1 l2 : Level} {X : UU l1} (P : 2-Element-Decidable-Subtype l2 X)
  where

  swap-2-Element-Decidable-Subtype : Aut (type-2-Element-Decidable-Subtype P)
  swap-2-Element-Decidable-Subtype =
    swap-2-Element-Type (2-element-type-2-Element-Decidable-Subtype P)

  map-swap-2-Element-Decidable-Subtype :
    type-2-Element-Decidable-Subtype P → type-2-Element-Decidable-Subtype P
  map-swap-2-Element-Decidable-Subtype =
    map-swap-2-Element-Type (2-element-type-2-Element-Decidable-Subtype P)

  compute-swap-2-Element-Decidable-Subtype :
    (x y : type-2-Element-Decidable-Subtype P) → ¬ (Id x y) →
    Id (map-swap-2-Element-Decidable-Subtype x) y
  compute-swap-2-Element-Decidable-Subtype =
    compute-swap-2-Element-Type (2-element-type-2-Element-Decidable-Subtype P)

module _
  {l1 l2 : Level} (n : ℕ) (X : UU-Fin-Level l1 n)
  where

  is-finite-2-Element-Decidable-Subtype :
    is-finite (2-Element-Decidable-Subtype l2 (type-UU-Fin-Level X))
  is-finite-2-Element-Decidable-Subtype =
    is-finite-decidable-subtype
      (λ P →
        pair
          ( has-cardinality 2 (Σ (type-UU-Fin-Level X) (λ x → type-decidable-Prop (P x))))
          ( pair
            ( is-prop-type-trunc-Prop)
            ( is-decidable-equiv
              ( equiv-has-cardinality-id-number-of-elements-is-finite
                ( Σ (type-UU-Fin-Level X) (λ x → type-decidable-Prop (P x)))
                ( is-finite-decidable-subtype P (is-finite-type-UU-Fin-Level X)) 2)
              ( has-decidable-equality-ℕ
                ( number-of-elements-is-finite (is-finite-decidable-subtype P (is-finite-type-UU-Fin-Level X)))
                ( 2)))))
      ( is-finite-Π
        ( is-finite-type-UU-Fin-Level X)
        ( λ x → is-finite-equiv (inv-equiv equiv-bool-decidable-Prop ∘e equiv-bool-Fin-two-ℕ) is-finite-Fin))

```

### 2-element decidable subtypes are closed under precomposition with an equivalence

```agda
precomp-equiv-2-Element-Decidable-Subtype :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} → X ≃ Y →
    2-Element-Decidable-Subtype l3 X → 2-Element-Decidable-Subtype l3 Y
pr1 (precomp-equiv-2-Element-Decidable-Subtype e (pair P H)) =
  P ∘ (map-inv-equiv e)
pr2 (precomp-equiv-2-Element-Decidable-Subtype e (pair P H)) =
  transitive-mere-equiv
    ( H)
    ( unit-trunc-Prop
      ( equiv-subtype-equiv
        ( e)
        ( subtype-decidable-subtype P)
        ( subtype-decidable-subtype (P ∘ (map-inv-equiv e)))
         λ x →
          iff-equiv
            ( prop-decidable-Prop (P x))
            ( prop-decidable-Prop (P (map-inv-equiv e (map-equiv e x))))
            ( tr
              ( λ g → (type-decidable-Prop (P x)) ≃ (type-decidable-Prop (P (map-equiv g x))))
              ( inv (left-inverse-law-equiv e))
              ( id-equiv))))
```
  
