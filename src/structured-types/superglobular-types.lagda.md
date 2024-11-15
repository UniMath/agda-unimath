# Superglobular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.superglobular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.binary-dependent-reflexive-globular-types
open import structured-types.globular-types
open import structured-types.points-reflexive-globular-types
open import structured-types.pointwise-extensions-binary-families-reflexive-globular-types
open import structured-types.reflexive-globular-equivalences
open import structured-types.reflexive-globular-types
```

</details>

**Disclaimer.** The contents of this file are experimental, and likely to be
changed or reconsidered.

## Idea

An {{#concept "superglobular type" Agda=Superglobular-Type}} is a
[reflexive globular type](structured-types.reflexive-globular-types.md) `G` such
that the binary family of globular types

```text
  G' : G₀ → G₀ → Globular-Type
```

of 1-cells and higher cells
[extends pointwise](structured-types.pointwise-extensions-binary-families-globular-types.md)
to a
[binary dependent globular type](structured-types.binary-dependent-globular-types.md).
More specifically, a superglobular type consists of a reflexive globular type
`G` equipped with a binary dependent globular type

```text
  H : Binary-Dependent-Globular-Type l2 l2 G G
```

and a family of
[globular equivalences](structured-types.globular-equivalences.md)

```text
  (x y : G₀) → ev-point H x y ≃ G' x y.
```

The low-dimensional data of a superglobular type is therefore as follows:

```text
  G₀ : Type

  G₁ : (x y : G₀) → Type
  H₀ : (x y : G₀) → Type
  e₀ : {x y : G₀} → H₀ x y ≃ G₀ x y
  refl G : (x : G₀) → G₁ x x

  G₂ : {x y : G₀} (s t : G₁ x y) → Type
  H₁ : {x x' y y' : G₀} → G₁ x x' → G₁ y y' → H₀ x y → H₀ x' y' → Type
  e₁ : {x y : G₀} {s t : H₀ x y} → H₁ (refl G x) (refl G y) s t ≃ G₂ (e₀ s) (e₀ t)
  refl G : {x y : G₀} (s : G₁ x y) → G₂ s s

  G₃ : {x y : G₀} {s t : G₁ x y} (u v : G₂ s t) → Type
  H₂ : {x x' y y' : G₀} {s s' : G₁ x x'} {t t' : G₁ y y'}
       (p : G₂ s s') (q : G₂ t t') → H₁ s t → H₁ s' t' → Type
  e₂ : {x y : G₀} {s t : H₀ x y} {u v : H₁
       H₂ (refl G x) (refl G y) u v ≃ G₃ (e₁ u) (e₁ v)
```

Note that the type of pairs `(Gₙ₊₁ , eₙ)` in this structure is
[contractible](foundation-core.contractible-types.md). An equivalent way of
presenting the low-dimensional data of a superglobular type is therefore:

```text
  G₀ : Type

  H₀ : (x y : G₀) → Type
  refl G : (x : G₀) → H₀ x x

  H₁ : {x x' y y' : G₀} → H₁ x x' → H₁ y y' → H₀ x y → H₀ x' y' → Type
  refl G : {x y : G₀} (s : H₀ x y) → H₁ (refl G x) (refl G y) s s

  H₂ : {x x' y y' : G₀} {s s' : H₁ x x'} {t t' : H₁ y y'}
       (p : H₂ s s') (q : H₂ t t') → H₁ s t → H₁ s' t' → Type
```

## Definitions

### The predicate of being a superglobular type

```agda
module _
  {l1 l2 : Level} (l3 l4 : Level) (G : Reflexive-Globular-Type l1 l2)
  where

  is-superglobular-Reflexive-Globular-Type : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  is-superglobular-Reflexive-Globular-Type =
    pointwise-extension-binary-family-reflexive-globular-types l3 l4 G G
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G)

module _
  {l1 l2 l3 l4 : Level} {G : Reflexive-Globular-Type l1 l2}
  (H : is-superglobular-Reflexive-Globular-Type l3 l4 G)
  where

  1-cell-binary-dependent-reflexive-globular-type-is-superglobular-Reflexive-Globular-Type :
    Binary-Dependent-Reflexive-Globular-Type l3 l4 G G
  1-cell-binary-dependent-reflexive-globular-type-is-superglobular-Reflexive-Globular-Type =
    pr1 H

  reflexive-globular-equiv-is-superglobular-Reflexive-Globular-Type :
    (x y : point-Reflexive-Globular-Type G) →
    reflexive-globular-equiv
      ( ev-point-Binary-Dependent-Reflexive-Globular-Type G G
        ( 1-cell-binary-dependent-reflexive-globular-type-is-superglobular-Reflexive-Globular-Type)
        ( x)
        ( y))
      ( 1-cell-reflexive-globular-type-Reflexive-Globular-Type G x y)
  reflexive-globular-equiv-is-superglobular-Reflexive-Globular-Type =
    pr2 H
```

### Superglobular types

```agda
record
  Superglobular-Type
    (l1 l2 l3 l4 : Level) : UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3 ⊔ lsuc l4)
  where

  field
    reflexive-globular-type-Superglobular-Type : Reflexive-Globular-Type l1 l2

  globular-type-Superglobular-Type : Globular-Type l1 l2
  globular-type-Superglobular-Type =
    globular-type-Reflexive-Globular-Type
      reflexive-globular-type-Superglobular-Type

  0-cell-Superglobular-Type : UU l1
  0-cell-Superglobular-Type =
    0-cell-Reflexive-Globular-Type reflexive-globular-type-Superglobular-Type

  point-Superglobular-Type : UU l1
  point-Superglobular-Type =
    point-Reflexive-Globular-Type reflexive-globular-type-Superglobular-Type

  1-cell-reflexive-globular-type-Superglobular-Type :
    (x y : 0-cell-Superglobular-Type) →
    Reflexive-Globular-Type l2 l2
  1-cell-reflexive-globular-type-Superglobular-Type =
    1-cell-reflexive-globular-type-Reflexive-Globular-Type
      reflexive-globular-type-Superglobular-Type

  field
    is-superglobular-Superglobular-Type :
      is-superglobular-Reflexive-Globular-Type l3 l4
        reflexive-globular-type-Superglobular-Type

  1-cell-binary-dependent-reflexive-globular-type-Superglobular-Type :
    Binary-Dependent-Reflexive-Globular-Type l3 l4
      reflexive-globular-type-Superglobular-Type
      reflexive-globular-type-Superglobular-Type
  1-cell-binary-dependent-reflexive-globular-type-Superglobular-Type =
    1-cell-binary-dependent-reflexive-globular-type-is-superglobular-Reflexive-Globular-Type
      is-superglobular-Superglobular-Type

  reflexive-globular-equiv-Superglobular-Type :
    (x y : point-Superglobular-Type) →
    reflexive-globular-equiv
      ( ev-point-Binary-Dependent-Reflexive-Globular-Type
        ( reflexive-globular-type-Superglobular-Type)
        ( reflexive-globular-type-Superglobular-Type)
        ( 1-cell-binary-dependent-reflexive-globular-type-Superglobular-Type)
        ( x)
        ( y))
      ( 1-cell-reflexive-globular-type-Superglobular-Type x y)
  reflexive-globular-equiv-Superglobular-Type =
    reflexive-globular-equiv-is-superglobular-Reflexive-Globular-Type
      is-superglobular-Superglobular-Type
```
