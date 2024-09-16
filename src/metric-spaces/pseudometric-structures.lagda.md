# Pseudometric structures on a type

```agda
module metric-spaces.pseudometric-structures where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.closed-premetric-structures
open import metric-spaces.discrete-premetric-structures
open import metric-spaces.extensional-premetric-structures
open import metric-spaces.monotonic-premetric-structures
open import metric-spaces.premetric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures
```

</details>

## Idea

A [premetric](metric-spaces.premetric-structures.md) is a
{{#concept "pseudometric structure" Agda=is-pseudometric-Premetric}} if it is
[reflexive](metric-spaces.reflexive-premetric-structures.md),
[symmetric](metric-spaces.symmetric-premetric-structures.md), and
[triangular](metric-spaces.triangular-premetric-structures.md).

## Definitions

### The property of being a pseudometric premetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-pseudometric-prop-Premetric : Prop (l1 ⊔ l2)
  is-pseudometric-prop-Premetric =
    product-Prop
      ( is-reflexive-prop-Premetric B)
      ( product-Prop
        ( is-symmetric-prop-Premetric B)
        ( is-triangular-prop-Premetric B))

  is-pseudometric-Premetric : UU (l1 ⊔ l2)
  is-pseudometric-Premetric =
    type-Prop is-pseudometric-prop-Premetric

  is-prop-is-pseudometric-Premetric :
    is-prop is-pseudometric-Premetric
  is-prop-is-pseudometric-Premetric =
    is-prop-type-Prop is-pseudometric-prop-Premetric
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (P : is-pseudometric-Premetric B)
  where

  is-reflexive-is-pseudometric-Premetric : is-reflexive-Premetric B
  is-reflexive-is-pseudometric-Premetric = pr1 P

  is-symmetric-is-pseudometric-Premetric : is-symmetric-Premetric B
  is-symmetric-is-pseudometric-Premetric = pr1 (pr2 P)

  is-triangular-is-pseudometric-Premetric : is-triangular-Premetric B
  is-triangular-is-pseudometric-Premetric = pr2 (pr2 P)
```

## Properties

### The discrete premetric on a type is a pseudometric

```agda
module _
  {l : Level} {A : UU l}
  where

  is-pseudometric-discrete-Premetric :
    is-pseudometric-Premetric (discrete-Premetric A)
  is-pseudometric-discrete-Premetric =
    is-reflexive-discrete-Premetric A ,
    is-symmetric-discrete-Premetric A ,
    is-triangular-discrete-Premetric A
```

### The closure of a pseudometric structure is pseudometric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (M : is-pseudometric-Premetric B)
  where

  preserves-is-pseudometric-closure-Premetric :
    is-pseudometric-Premetric (closure-Premetric B)
  preserves-is-pseudometric-closure-Premetric =
    ( is-reflexive-closure-Premetric
      ( B)
      ( is-reflexive-is-pseudometric-Premetric B M)) ,
    ( is-symmetric-closure-Premetric
      ( B)
      ( is-symmetric-is-pseudometric-Premetric B M)) ,
    ( is-triangular-closure-Premetric
      ( B)
      ( is-triangular-is-pseudometric-Premetric B M))
```

## See also

- Metric structures are defined in
  [metric-spaces.metric-structures](metric-spaces.metric-structures.md).
