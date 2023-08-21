# Codiscrete maps

```agda
{-# OPTIONS --cohesion --flat-split --rewriting #-}

module modal-type-theory.codiscrete-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.fibers-of-maps
open import foundation.propositions
open import foundation.universe-levels

open import modal-type-theory.codiscrete-types
```

</details>

## Idea

A map is said to be **codiscrete** if its fibers are codiscrete.

## Definition

```agda
is-codiscrete-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-codiscrete-map f = is-codiscrete-family (fib f)
```

## Properties

### Being codiscrete is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-codiscrete-map-Prop : Prop (l1 ⊔ l2)
  is-codiscrete-map-Prop = is-codiscrete-family-Prop (fib f)

  is-property-is-codiscrete-map : is-prop (is-codiscrete-map f)
  is-property-is-codiscrete-map = is-prop-type-Prop is-codiscrete-map-Prop
```
