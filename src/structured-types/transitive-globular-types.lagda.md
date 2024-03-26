# Transitive globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.transitive-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.globular-types
```

</details>

## Idea

A {{#concept "transitive globular type" Agda=Transitive-Globular-Type}} is a
[globular type](structured-types.globular-types.md) `A`
[equipped](foundation.structure.md) with a binary operator

```text
  - * - : (𝑛+1)-Cell A y z → (𝑛+1)-Cell A x y → (𝑛+1)-Cell A x z
```

at every level $n$.

**Note.** This is not established terminology and may change.

## Definition

### Transitivity structure on a globular type

```agda
record
  is-transitive-globular-structure
  {l1 l2 : Level} {A : UU l1} (G : globular-structure l2 A) : UU (l1 ⊔ l2)
  where
  coinductive
  field
    comp-1-cell-is-transitive-globular-structure :
      {x y z : A} →
      1-cell-globular-structure G y z →
      1-cell-globular-structure G x y →
      1-cell-globular-structure G x z

    is-transitive-globular-structure-1-cell-is-transitive-globular-structure :
      (x y : A) →
      is-transitive-globular-structure
        ( globular-structure-1-cell-globular-structure G x y)

open is-transitive-globular-structure public

module _
  {l1 l2 : Level} {A : UU l1} {G : globular-structure l2 A}
  (r : is-transitive-globular-structure G)
  where

  comp-2-cell-is-transitive-globular-structure :
    {x y : A} {f g h : 1-cell-globular-structure G x y} →
    2-cell-globular-structure G g h →
    2-cell-globular-structure G f g →
    2-cell-globular-structure G f h
  comp-2-cell-is-transitive-globular-structure {x} {y} =
    comp-1-cell-is-transitive-globular-structure
      ( is-transitive-globular-structure-1-cell-is-transitive-globular-structure
        ( r)
        ( x)
        ( y))

  is-transitive-globular-structure-2-cell-is-transitive-globular-structure :
    {x y : A} (f g : 1-cell-globular-structure G x y) →
    is-transitive-globular-structure
      ( globular-structure-2-cell-globular-structure G f g)
  is-transitive-globular-structure-2-cell-is-transitive-globular-structure
    { x} {y} =
    is-transitive-globular-structure-1-cell-is-transitive-globular-structure
      ( is-transitive-globular-structure-1-cell-is-transitive-globular-structure
        ( r)
        ( x)
        ( y))

  comp-3-cell-is-transitive-globular-structure :
    {x y : A} {f g : 1-cell-globular-structure G x y}
    {H K L : 2-cell-globular-structure G f g} →
    3-cell-globular-structure G K L →
    3-cell-globular-structure G H K →
    3-cell-globular-structure G H L
  comp-3-cell-is-transitive-globular-structure {x} {y} {f} {g} =
    comp-1-cell-is-transitive-globular-structure
      ( is-transitive-globular-structure-2-cell-is-transitive-globular-structure
        ( f)
        ( g))
```

### The type of transitive globular structures on a type

```agda
transitive-globular-structure :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
transitive-globular-structure l2 A =
  Σ (globular-structure l2 A) (is-transitive-globular-structure)
```

### The type of transitive globular types

```agda
Transitive-Globular-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Transitive-Globular-Type l1 l2 = Σ (UU l1) (transitive-globular-structure l2)
```

## Examples

### The transitive globular structure on a type given by its identity types

```agda
is-transitive-globular-structure-Id :
  {l : Level} (A : UU l) →
  is-transitive-globular-structure (globular-structure-Id A)
is-transitive-globular-structure-Id A =
  λ where
  .comp-1-cell-is-transitive-globular-structure
    p q →
    q ∙ p
  .is-transitive-globular-structure-1-cell-is-transitive-globular-structure
    x y →
    is-transitive-globular-structure-Id (x ＝ y)

transitive-globular-structure-Id :
  {l : Level} (A : UU l) → transitive-globular-structure l A
transitive-globular-structure-Id A =
  ( globular-structure-Id A , is-transitive-globular-structure-Id A)
```
