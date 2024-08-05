# Mere units of H-spaces

```agda
module structured-types.mere-units-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.binary-equivalences
open import foundation.connected-components
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import structured-types.connected-h-spaces
open import structured-types.h-spaces
open import structured-types.pointed-types
```

</details>

## Idea

A {{#concept "mere unit" Disambiguation="H-space"}} in an
[H-space](structured-types.h-spaces.md) `A` is an element `x` that is
[merely equal](foundation.mere-equality.md) to the unit element of `A`. The type
of mere units of an H-space always forms a
[connected H-space](structured-types.connected-h-spaces.md). In particular,
since the multiplicative operation of a connected H-space is always a
[binary equivalence](foundation.binary-equivalences.md), it follows that the
binary operation restricted to the mere units of an H-space is a binary
equivalence.

## Definitions

### The predicate of being a mere unit of an H-space

```agda
module _
  {l1 : Level} (A : H-Space l1)
  where

  is-mere-unit-prop-H-Space : type-H-Space A → Prop l1
  is-mere-unit-prop-H-Space x = mere-eq-Prop (unit-H-Space A) x

  is-mere-unit-H-Space : type-H-Space A → UU l1
  is-mere-unit-H-Space x = mere-eq (unit-H-Space A) x

  is-prop-is-mere-unit-H-Space :
    (x : type-H-Space A) → is-prop (is-mere-unit-H-Space x)
  is-prop-is-mere-unit-H-Space x =
    is-prop-mere-eq (unit-H-Space A) x
```

### The type of mere units of an H-space

```agda
module _
  {l1 : Level} (A : H-Space l1)
  where

  mere-unit-H-Space : UU l1
  mere-unit-H-Space = Σ (type-H-Space A) (is-mere-unit-H-Space A)
```

### The connected component of the unit of an H-Space

```agda
module _
  {l1 : Level} (A : H-Space l1)
  where

  connected-component-unit-H-Space : UU l1
  connected-component-unit-H-Space =
    connected-component (type-H-Space A) (unit-H-Space A)

  is-0-connected-connected-component-unit-H-Space :
    is-0-connected connected-component-unit-H-Space
  is-0-connected-connected-component-unit-H-Space =
    is-0-connected-connected-component (type-H-Space A) (unit-H-Space A)

  inclusion-connected-component-unit-H-Space :
    connected-component-unit-H-Space → type-H-Space A
  inclusion-connected-component-unit-H-Space = pr1
```

## Properties

### The unit of an H-space is a mere unit

```agda
module _
  {l1 : Level} (A : H-Space l1)
  where

  is-mere-unit-unit-H-Space : is-mere-unit-H-Space A (unit-H-Space A)
  is-mere-unit-unit-H-Space = refl-mere-eq _
```

### The multiplicative operation of an H-space preserves mere units

```agda
module _
  {l1 : Level} (A : H-Space l1)
  where

  abstract
    preserves-mere-unit-mul-H-Space :
      {x y : type-H-Space A} →
      is-mere-unit-H-Space A x → is-mere-unit-H-Space A y →
      is-mere-unit-H-Space A (mul-H-Space A x y)
    preserves-mere-unit-mul-H-Space H K =
      apply-twice-universal-property-trunc-Prop H K
        ( is-mere-unit-prop-H-Space A _)
        ( λ where
          refl refl →
            unit-trunc-Prop (inv (left-unit-law-mul-H-Space A _)))
```

### The connected component of the unit of an H-space is a connected H-space

```agda
module _
  {l1 : Level} (A : H-Space l1)
  where

  unit-connected-component-unit-H-Space : connected-component-unit-H-Space A
  pr1 unit-connected-component-unit-H-Space = unit-H-Space A
  pr2 unit-connected-component-unit-H-Space = is-mere-unit-unit-H-Space A

  connected-component-unit-pointed-type-H-Space : Pointed-Type l1
  pr1 connected-component-unit-pointed-type-H-Space =
    connected-component-unit-H-Space A
  pr2 connected-component-unit-pointed-type-H-Space =
    unit-connected-component-unit-H-Space

  mul-connected-component-unit-H-Space :
    (x y : connected-component-unit-H-Space A) →
    connected-component-unit-H-Space A
  pr1 (mul-connected-component-unit-H-Space x y) =
    mul-H-Space A
      ( inclusion-connected-component-unit-H-Space A x)
      ( inclusion-connected-component-unit-H-Space A y)
  pr2 (mul-connected-component-unit-H-Space x y) =
    preserves-mere-unit-mul-H-Space A (pr2 x) (pr2 y)

  left-unit-law-mul-connected-component-unit-H-Space :
    (x : connected-component-unit-H-Space A) →
    mul-connected-component-unit-H-Space
      ( unit-connected-component-unit-H-Space)
      ( x) ＝
    x
  left-unit-law-mul-connected-component-unit-H-Space x =
    eq-type-subtype
      ( is-mere-unit-prop-H-Space A)
      ( left-unit-law-mul-H-Space A
        ( inclusion-connected-component-unit-H-Space A x))

  right-unit-law-mul-connected-component-unit-H-Space :
    (x : connected-component-unit-H-Space A) →
    mul-connected-component-unit-H-Space
      ( x)
      ( unit-connected-component-unit-H-Space) ＝
    x
  right-unit-law-mul-connected-component-unit-H-Space x =
    eq-type-subtype
      ( is-mere-unit-prop-H-Space A)
      ( right-unit-law-mul-H-Space A
        ( inclusion-connected-component-unit-H-Space A x))

  coh-unit-laws-mul-connected-component-unit-H-Space :
    left-unit-law-mul-connected-component-unit-H-Space
      ( unit-connected-component-unit-H-Space) ＝
    right-unit-law-mul-connected-component-unit-H-Space
      ( unit-connected-component-unit-H-Space)
  coh-unit-laws-mul-connected-component-unit-H-Space =
    ap
      ( eq-type-subtype (is-mere-unit-prop-H-Space A))
      ( coh-unit-laws-mul-H-Space A)

  connected-component-unit-h-space-H-Space : H-Space l1
  pr1 connected-component-unit-h-space-H-Space =
    connected-component-unit-pointed-type-H-Space
  pr1 (pr2 connected-component-unit-h-space-H-Space) =
    mul-connected-component-unit-H-Space
  pr1 (pr2 (pr2 connected-component-unit-h-space-H-Space)) =
    left-unit-law-mul-connected-component-unit-H-Space
  pr1 (pr2 (pr2 (pr2 connected-component-unit-h-space-H-Space))) =
    right-unit-law-mul-connected-component-unit-H-Space
  pr2 (pr2 (pr2 (pr2 connected-component-unit-h-space-H-Space))) =
    coh-unit-laws-mul-connected-component-unit-H-Space

  connected-component-unit-connected-h-space-H-Space :
    0-Connected-H-Space l1
  pr1 connected-component-unit-connected-h-space-H-Space =
    connected-component-unit-h-space-H-Space
  pr2 connected-component-unit-connected-h-space-H-Space =
    is-0-connected-connected-component-unit-H-Space A

  is-binary-equiv-mul-connected-component-unit-H-Space :
    is-binary-equiv mul-connected-component-unit-H-Space
  is-binary-equiv-mul-connected-component-unit-H-Space =
    is-binary-equiv-mul-0-Connected-H-Space
      ( connected-component-unit-connected-h-space-H-Space)
```
