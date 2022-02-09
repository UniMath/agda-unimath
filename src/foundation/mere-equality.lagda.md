# Mere equality

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.mere-equality where

open import foundation.functoriality-propositional-truncation using
  ( functor-trunc-Prop)
open import foundation.identity-types using (Id; refl; inv; _∙_)
open import foundation.propositional-truncations using
  ( trunc-Prop; type-trunc-Prop; unit-trunc-Prop;
    apply-universal-property-trunc-Prop)
open import foundation.propositions using (UU-Prop)
open import foundation.universe-levels using (Level; UU)
```

## Idea

Two elements in a type are said to be merely equal if there is an element of the propositionally truncated identity type between them.

## Definition

```agda
mere-eq-Prop :
  {l : Level} {A : UU l} → A → A → UU-Prop l
mere-eq-Prop x y = trunc-Prop (Id x y)

mere-eq : {l : Level} {A : UU l} → A → A → UU l
mere-eq x y = type-trunc-Prop (Id x y)
```

## Properties

### Reflexivity

```agda
abstract
  refl-mere-eq :
    {l : Level} {A : UU l} {x : A} → mere-eq x x
  refl-mere-eq = unit-trunc-Prop refl
```

### Symmetry

```agda
abstract
  symm-mere-eq :
    {l : Level} {A : UU l} {x y : A} → mere-eq x y → mere-eq y x
  symm-mere-eq {x = x} {y} =
    functor-trunc-Prop inv
```

### Transitivity

```agda
abstract
  trans-mere-eq :
    {l : Level} {A : UU l} {x y z : A} →
    mere-eq x y → mere-eq y z → mere-eq x z
  trans-mere-eq {x = x} {y} {z} p q =
    apply-universal-property-trunc-Prop p
      ( mere-eq-Prop x z)
      ( λ p' → functor-trunc-Prop (λ q' → p' ∙ q') q)
```
