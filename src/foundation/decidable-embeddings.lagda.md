# Decidable embeddings

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.decidable-embeddings where

open import foundation.cartesian-product-types using (_×_)
open import foundation.decidable-maps using (is-decidable-map)
open import foundation.decidable-propositions using
  ( is-decidable-prop; is-prop-is-decidable-prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; _↪_)
open import foundation.fibers-of-maps using (fib)
open import foundation.propositional-maps using
  ( is-prop-map; is-emb-is-prop-map)
open import foundation.propositions using (is-prop; is-prop-Π)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

A map is said to be a decidable embedding if it is an embedding and its fibers are decidable types.

```agda
is-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → UU (l1 ⊔ l2)
is-decidable-emb {Y = Y} f = is-emb f × is-decidable-map f

abstract
  is-emb-is-decidable-emb :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
    is-decidable-emb f → is-emb f
  is-emb-is-decidable-emb H = pr1 H

is-decidable-map-is-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-decidable-emb f → is-decidable-map f
is-decidable-map-is-decidable-emb H = pr2 H
```

### Decidably propositional maps

```
is-decidable-prop-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (X → Y) → UU (l1 ⊔ l2)
is-decidable-prop-map {Y = Y} f = (y : Y) → is-decidable-prop (fib f y)

abstract
  is-prop-map-is-decidable-prop-map :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
    is-decidable-prop-map f → is-prop-map f
  is-prop-map-is-decidable-prop-map H y = pr1 (H y)

is-decidable-map-is-decidable-prop-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} {f : X → Y} →
  is-decidable-prop-map f → is-decidable-map f
is-decidable-map-is-decidable-prop-map H y = pr2 (H y)
```

## Properties

### Being a decidably propositional map is a proposition

```agda
abstract
  is-prop-is-decidable-prop-map :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
    is-prop (is-decidable-prop-map f)
  is-prop-is-decidable-prop-map f =
    is-prop-Π (λ y → is-prop-is-decidable-prop (fib f y))
```

```agda
abstract
  is-decidable-emb-is-decidable-prop-map :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
    is-decidable-prop-map f → is-decidable-emb f
  pr1 (is-decidable-emb-is-decidable-prop-map f H) =
    is-emb-is-prop-map (is-prop-map-is-decidable-prop-map H)
  pr2 (is-decidable-emb-is-decidable-prop-map f H) =
    is-decidable-map-is-decidable-prop-map H

_↪d_ :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
X ↪d Y = Σ (X → Y) is-decidable-emb

map-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↪d Y → X → Y
map-decidable-emb e = pr1 e

abstract
  is-decidable-emb-map-decidable-emb :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ↪d Y) →
    is-decidable-emb (map-decidable-emb e)
  is-decidable-emb-map-decidable-emb e = pr2 e

abstract
  is-emb-map-decidable-emb :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ↪d Y) →
    is-emb (map-decidable-emb e)
  is-emb-map-decidable-emb e =
    is-emb-is-decidable-emb (is-decidable-emb-map-decidable-emb e)

abstract
  is-decidable-map-map-decidable-emb :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ↪d Y) →
    is-decidable-map (map-decidable-emb e)
  is-decidable-map-map-decidable-emb e =
    is-decidable-map-is-decidable-emb (is-decidable-emb-map-decidable-emb e)

emb-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↪d Y → X ↪ Y
pr1 (emb-decidable-emb e) = map-decidable-emb e
pr2 (emb-decidable-emb e) = is-emb-map-decidable-emb e
```
