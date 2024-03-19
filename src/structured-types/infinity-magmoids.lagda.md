# ∞-Magmoids

```agda
{-# OPTIONS --guardedness #-}

module structured-types.infinity-magmoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.telescopes
open import foundation.universe-levels

open import structured-types.globular-types
```

</details>

## Idea

An {{#concept "$∞$-magmoid" Agda=∞-Magmoid}} is a
[globular type](structured-types.globular-types.md) `A`
[equipped](foundation.structure.md) with a binary operator

```text
  - * - : (𝓃 + 1)-Cell A y z → (𝓃 + 1)-Cell A x y → (𝓃 + 1)-Cell A x z
```

at every level $n$.

## Definition

### The structure of an $∞$-magmoid on a globular type

```agda
record
  is-∞-magmoid-globular-structure
  {l : Level} {A : UU l} (G : globular-structure A) : UU l
  where
  coinductive
  field
    comp-1-cell-is-∞-magmoid-globular-structure :
      {x y z : A} →
      1-cell-globular-structure G y z →
      1-cell-globular-structure G x y →
      1-cell-globular-structure G x z

    is-∞-magmoid-globular-structure-1-cell-is-∞-magmoid-globular-structure :
      (x y : A) →
      is-∞-magmoid-globular-structure
        ( globular-structure-1-cell-globular-structure G x y)

open is-∞-magmoid-globular-structure public

module _
  {l : Level} {A : UU l} {G : globular-structure A}
  (r : is-∞-magmoid-globular-structure G)
  where

  comp-2-cell-is-∞-magmoid-globular-structure :
    {x y : A} {f g h : 1-cell-globular-structure G x y} →
    2-cell-globular-structure G g h →
    2-cell-globular-structure G f g →
    2-cell-globular-structure G f h
  comp-2-cell-is-∞-magmoid-globular-structure {x} {y} =
    comp-1-cell-is-∞-magmoid-globular-structure
      ( is-∞-magmoid-globular-structure-1-cell-is-∞-magmoid-globular-structure
        ( r)
        ( x)
        ( y))
```

### The type of $∞$-magmoid structures on a type

```agda
is-∞-magmoid : {l : Level} (A : UU l) → UU (lsuc l)
is-∞-magmoid A = Σ (globular-structure A) (is-∞-magmoid-globular-structure)
```

### The type of $∞$-magmoids

```agda
∞-Magmoid : (l : Level) → UU (lsuc l)
∞-Magmoid l = Σ (UU l) (is-∞-magmoid)
```

## Examples

### The $∞$-magmoid structure given by concatenation of a types identifications

```agda
is-∞-magmoid-globular-structure-Id :
  {l : Level} (A : UU l) →
  is-∞-magmoid-globular-structure (globular-structure-Id A)
is-∞-magmoid-globular-structure-Id A =
  λ where
  .comp-1-cell-is-∞-magmoid-globular-structure p q → q ∙ p
  .is-∞-magmoid-globular-structure-1-cell-is-∞-magmoid-globular-structure x y →
    is-∞-magmoid-globular-structure-Id (x ＝ y)

is-∞-magmoid-Id : {l : Level} (A : UU l) → is-∞-magmoid A
pr1 (is-∞-magmoid-Id A) = globular-structure-Id A
pr2 (is-∞-magmoid-Id A) = is-∞-magmoid-globular-structure-Id A
```
