# Connected H-spaces

```agda
module structured-types.connected-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.binary-equivalences
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.truncation-levels
open import foundation.universe-levels

open import structured-types.h-spaces
open import structured-types.pointed-types
```

</details>

## Idea

A {{#concept "connected H-space" Agda=Connected-H-Space}} is an [H-space](structured-types.h-spaces.md) of which the underlying type is [0-connected](foundation.0-connected-types.md). The binary operation `μ : A → A → A` of any connected H-space `A` is a [binary equivalence](foundation.binary-equivalences.md). This means that the maps

```text
  x ↦ μ x y : A → A        and         y ↦ μ x y : A → A
```

are [equivalences](foundation-core.equivalences.md) for any `x` and `y` in `A`. Furthermore, the [connected component](foundation.connected-components.md) of the unit element of an H-space is always a connected H-space. We will prove this fact in the file about [mere units](structured-types.mere-units-h-spaces.md).

## Definitions

### The predicate of being a connected H-space

```agda
module _
  {l1 : Level} (k : 𝕋) (A : H-Space l1)
  where

  is-connected-prop-H-Space : Prop l1
  is-connected-prop-H-Space = is-connected-Prop k (type-H-Space A)

  is-connected-H-Space : UU l1
  is-connected-H-Space = is-connected k (type-H-Space A)

  is-prop-is-connected-H-Space : is-prop is-connected-H-Space
  is-prop-is-connected-H-Space = is-prop-is-connected k (type-H-Space A)
```

### The predicate of being a 0-connected H-space

```agda
module _
  {l1 : Level} (A : H-Space l1)
  where

  is-0-connected-prop-H-Space : Prop l1
  is-0-connected-prop-H-Space = is-0-connected-Prop (type-H-Space A)

  is-0-connected-H-Space : UU l1
  is-0-connected-H-Space = is-0-connected (type-H-Space A)

  is-prop-is-0-connected-H-Space : is-prop is-0-connected-H-Space
  is-prop-is-0-connected-H-Space = is-prop-is-0-connected (type-H-Space A)
```

### The type of connected H-spaces

```agda
Connected-H-Space : (l : Level) (k : 𝕋) → UU (lsuc l)
Connected-H-Space l k = Σ (H-Space l) (is-connected-H-Space k)

module _
  {l : Level} {k : 𝕋} (A : Connected-H-Space l k)
  where

  h-space-Connected-H-Space : H-Space l
  h-space-Connected-H-Space = pr1 A

  pointed-type-Connected-H-Space : Pointed-Type l
  pointed-type-Connected-H-Space =
    pointed-type-H-Space h-space-Connected-H-Space

  type-Connected-H-Space : UU l
  type-Connected-H-Space = type-H-Space h-space-Connected-H-Space

  unit-Connected-H-Space : type-Connected-H-Space
  unit-Connected-H-Space = unit-H-Space h-space-Connected-H-Space

  mul-Connected-H-Space :
    (x y : type-Connected-H-Space) → type-Connected-H-Space
  mul-Connected-H-Space = mul-H-Space h-space-Connected-H-Space

  left-unit-law-mul-Connected-H-Space :
    (x : type-Connected-H-Space) →
    mul-Connected-H-Space unit-Connected-H-Space x ＝ x
  left-unit-law-mul-Connected-H-Space =
    left-unit-law-mul-H-Space h-space-Connected-H-Space

  right-unit-law-mul-Connected-H-Space :
    (x : type-Connected-H-Space) →
    mul-Connected-H-Space x unit-Connected-H-Space ＝ x
  right-unit-law-mul-Connected-H-Space =
    right-unit-law-mul-H-Space h-space-Connected-H-Space

  coh-unit-laws-mul-Connected-H-Space :
    left-unit-law-mul-Connected-H-Space unit-Connected-H-Space ＝
    right-unit-law-mul-Connected-H-Space unit-Connected-H-Space
  coh-unit-laws-mul-Connected-H-Space =
    coh-unit-laws-mul-H-Space h-space-Connected-H-Space

  is-connected-Connected-H-Space :
    is-connected-H-Space k h-space-Connected-H-Space
  is-connected-Connected-H-Space = pr2 A
```

### The type of 0-connected H-spaces

```agda
0-Connected-H-Space : (l : Level) → UU (lsuc l)
0-Connected-H-Space l = Σ (H-Space l) is-0-connected-H-Space

module _
  {l : Level} (A : 0-Connected-H-Space l)
  where

  h-space-0-Connected-H-Space : H-Space l
  h-space-0-Connected-H-Space = pr1 A

  pointed-type-0-Connected-H-Space : Pointed-Type l
  pointed-type-0-Connected-H-Space =
    pointed-type-H-Space h-space-0-Connected-H-Space

  type-0-Connected-H-Space : UU l
  type-0-Connected-H-Space = type-H-Space h-space-0-Connected-H-Space

  unit-0-Connected-H-Space : type-0-Connected-H-Space
  unit-0-Connected-H-Space = unit-H-Space h-space-0-Connected-H-Space

  mul-0-Connected-H-Space :
    (x y : type-0-Connected-H-Space) → type-0-Connected-H-Space
  mul-0-Connected-H-Space = mul-H-Space h-space-0-Connected-H-Space

  left-unit-law-mul-0-Connected-H-Space :
    (x : type-0-Connected-H-Space) →
    mul-0-Connected-H-Space unit-0-Connected-H-Space x ＝ x
  left-unit-law-mul-0-Connected-H-Space =
    left-unit-law-mul-H-Space h-space-0-Connected-H-Space

  right-unit-law-mul-0-Connected-H-Space :
    (x : type-0-Connected-H-Space) →
    mul-0-Connected-H-Space x unit-0-Connected-H-Space ＝ x
  right-unit-law-mul-0-Connected-H-Space =
    right-unit-law-mul-H-Space h-space-0-Connected-H-Space

  coh-unit-laws-mul-0-Connected-H-Space :
    left-unit-law-mul-0-Connected-H-Space unit-0-Connected-H-Space ＝
    right-unit-law-mul-0-Connected-H-Space unit-0-Connected-H-Space
  coh-unit-laws-mul-0-Connected-H-Space =
    coh-unit-laws-mul-H-Space h-space-0-Connected-H-Space

  is-0-connected-0-Connected-H-Space :
    is-0-connected-H-Space h-space-0-Connected-H-Space
  is-0-connected-0-Connected-H-Space = pr2 A
```

## Properties

### The binary operation of any 0-connected H-space is a binary equivalence

```agda
module _
  {l : Level} (A : 0-Connected-H-Space l)
  where

  abstract
    is-equiv-left-mul-0-Connected-H-Space :
      (x : type-0-Connected-H-Space A) →
      is-equiv (λ y → mul-0-Connected-H-Space A x y)
    is-equiv-left-mul-0-Connected-H-Space x =
      apply-universal-property-trunc-Prop
        ( mere-eq-is-0-connected
          ( is-0-connected-0-Connected-H-Space A)
          ( unit-0-Connected-H-Space A)
          ( x))
        ( is-equiv-Prop (mul-0-Connected-H-Space A x))
        ( λ where
          refl →
            is-equiv-htpy id
              ( left-unit-law-mul-0-Connected-H-Space A)
              ( is-equiv-id))

  abstract
    is-equiv-right-mul-0-Connected-H-Space :
      (y : type-0-Connected-H-Space A) →
      is-equiv (λ x → mul-0-Connected-H-Space A x y)
    is-equiv-right-mul-0-Connected-H-Space y =
      apply-universal-property-trunc-Prop
        ( mere-eq-is-0-connected
          ( is-0-connected-0-Connected-H-Space A)
          ( unit-0-Connected-H-Space A)
          ( y))
        ( is-equiv-Prop (λ x → mul-0-Connected-H-Space A x y))
        ( λ where
          refl →
            is-equiv-htpy id
              ( right-unit-law-mul-0-Connected-H-Space A)
              ( is-equiv-id))

  abstract
    is-binary-equiv-mul-0-Connected-H-Space :
      is-binary-equiv (mul-0-Connected-H-Space A)
    pr1 is-binary-equiv-mul-0-Connected-H-Space =
      is-equiv-right-mul-0-Connected-H-Space
    pr2 is-binary-equiv-mul-0-Connected-H-Space =
      is-equiv-left-mul-0-Connected-H-Space
```
