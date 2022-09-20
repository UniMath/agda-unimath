---
title: Equality in finite types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.equality-finite-types where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.decidable-equality using
  ( has-decidable-equality; has-decidable-equality-Prop;
    has-decidable-equality-equiv')
open import foundation.dependent-pair-types using (pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.mere-equivalences using (is-set-mere-equiv')
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop)
open import foundation.sets using (is-set; is-set-Prop; Set)
open import foundation.universe-levels using (Level; UU; _⊔_; lzero)

open import univalent-combinatorics.counting using
  ( is-set-count; equiv-count; number-of-elements-count)
open import univalent-combinatorics.decidable-propositions using
  ( count-eq)
open import univalent-combinatorics.equality-standard-finite-types using
  ( has-decidable-equality-Fin)
open import univalent-combinatorics.finite-types using
  ( is-finite; has-cardinality; is-finite-count; 𝔽; type-𝔽; is-finite-type-𝔽;
    UU-Fin; type-UU-Fin; has-cardinality-type-UU-Fin)
open import univalent-combinatorics.standard-finite-types using (is-set-Fin)
```

## Idea

Any finite type is a set because it is merely equivalent to a standard finite type. Moreover, any finite type has decidable equality. In particular, this implies that the type of identifications between any two elements in a finite type is finite.

## Properties

### Any finite type has decidable equality

```agda
has-decidable-equality-is-finite :
  {l1 : Level} {X : UU l1} → is-finite X → has-decidable-equality X
has-decidable-equality-is-finite {l1} {X} is-finite-X =
  apply-universal-property-trunc-Prop is-finite-X
    ( has-decidable-equality-Prop X)
    ( λ e →
      has-decidable-equality-equiv'
        ( equiv-count e)
        ( has-decidable-equality-Fin (number-of-elements-count e)))
```

### Any type of finite cardinality has decidable equality

```agda
has-decidable-equality-has-cardinality :
  {l1 : Level} {X : UU l1} (k : ℕ) →
  has-cardinality k X → has-decidable-equality X
has-decidable-equality-has-cardinality {l1} {X} k H =
  apply-universal-property-trunc-Prop H
    ( has-decidable-equality-Prop X)
    ( λ e → has-decidable-equality-equiv' e (has-decidable-equality-Fin k))
```

### The type of identifications between any two elements in a finite type is finite

```agda
abstract
  is-finite-eq :
    {l1 : Level} {X : UU l1} →
    has-decidable-equality X → {x y : X} → is-finite (Id x y)
  is-finite-eq d {x} {y} = is-finite-count (count-eq d x y)

Id-𝔽 : {l : Level} → (X : 𝔽 l) (x y : type-𝔽 X) → 𝔽 l
pr1 (Id-𝔽 X x y) = Id x y
pr2 (Id-𝔽 X x y) =
  is-finite-eq (has-decidable-equality-is-finite (is-finite-type-𝔽 X))
```
