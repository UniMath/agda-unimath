# Transitive globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.transitive-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
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

## Definitions

### The predicate of being a transitive globular type

```agda
record
  is-transitive-Globular-Type
    {l1 l2 : Level} (G : Globular-Type l1 l2) : UU (l1 ⊔ l2)
  where
  coinductive

  field
    comp-1-cell-is-transitive-Globular-Type :
      is-transitive' (1-cell-Globular-Type G)

  field
    is-transitive-1-cell-globular-type-is-transitive-Globular-Type :
      {x y : 0-cell-Globular-Type G} →
      is-transitive-Globular-Type
        ( 1-cell-globular-type-Globular-Type G x y)

open is-transitive-Globular-Type public

module _
  {l1 l2 : Level} {G : Globular-Type l1 l2}
  (t : is-transitive-Globular-Type G)
  where

  comp-2-cell-is-transitive-Globular-Type :
    {x y : 0-cell-Globular-Type G} →
    is-transitive' (2-cell-Globular-Type G {x} {y})
  comp-2-cell-is-transitive-Globular-Type =
    comp-1-cell-is-transitive-Globular-Type
      ( is-transitive-1-cell-globular-type-is-transitive-Globular-Type t)

  is-transitive-2-cell-globular-type-is-transitive-Globular-Type :
    {x y : 0-cell-Globular-Type G}
    {f g : 1-cell-Globular-Type G x y} →
    is-transitive-Globular-Type
      ( 2-cell-globular-type-Globular-Type G f g)
  is-transitive-2-cell-globular-type-is-transitive-Globular-Type =
    is-transitive-1-cell-globular-type-is-transitive-Globular-Type
      ( is-transitive-1-cell-globular-type-is-transitive-Globular-Type t)

module _
  {l1 l2 : Level} {G : Globular-Type l1 l2}
  (t : is-transitive-Globular-Type G)
  where

  comp-3-cell-is-transitive-Globular-Type :
    {x y : 0-cell-Globular-Type G}
    {f g : 1-cell-Globular-Type G x y} →
    is-transitive' (3-cell-Globular-Type G {x} {y} {f} {g})
  comp-3-cell-is-transitive-Globular-Type =
    comp-2-cell-is-transitive-Globular-Type
      ( is-transitive-1-cell-globular-type-is-transitive-Globular-Type t)

  is-transitive-3-cell-globular-type-is-transitive-Globular-Type :
    {x y : 0-cell-Globular-Type G}
    {f g : 1-cell-Globular-Type G x y}
    {s t : 2-cell-Globular-Type G f g} →
    is-transitive-Globular-Type
      ( 3-cell-globular-type-Globular-Type G s t)
  is-transitive-3-cell-globular-type-is-transitive-Globular-Type =
    is-transitive-2-cell-globular-type-is-transitive-Globular-Type
      ( is-transitive-1-cell-globular-type-is-transitive-Globular-Type t)
```

### Transitive globular types

```agda
record
  Transitive-Globular-Type
    (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
  where

  constructor
    make-Transitive-Globular-Type

  field
    globular-type-Transitive-Globular-Type : Globular-Type l1 l2

  0-cell-Transitive-Globular-Type : UU l1
  0-cell-Transitive-Globular-Type =
    0-cell-Globular-Type globular-type-Transitive-Globular-Type

  1-cell-Transitive-Globular-Type :
    0-cell-Transitive-Globular-Type → 0-cell-Transitive-Globular-Type → UU l2
  1-cell-Transitive-Globular-Type =
    1-cell-Globular-Type globular-type-Transitive-Globular-Type

  2-cell-Transitive-Globular-Type :
    {x y : 0-cell-Transitive-Globular-Type}
    (f g : 1-cell-Transitive-Globular-Type x y) → UU l2
  2-cell-Transitive-Globular-Type =
    2-cell-Globular-Type globular-type-Transitive-Globular-Type

  3-cell-Transitive-Globular-Type :
    {x y : 0-cell-Transitive-Globular-Type}
    {f g : 1-cell-Transitive-Globular-Type x y}
    (s t : 2-cell-Transitive-Globular-Type f g) → UU l2
  3-cell-Transitive-Globular-Type =
    3-cell-Globular-Type globular-type-Transitive-Globular-Type

  globular-structure-Transitive-Globular-Type :
    globular-structure l2 0-cell-Transitive-Globular-Type
  globular-structure-Transitive-Globular-Type =
    globular-structure-0-cell-Globular-Type
      ( globular-type-Transitive-Globular-Type)

  field
    is-transitive-Transitive-Globular-Type :
      is-transitive-Globular-Type globular-type-Transitive-Globular-Type

  comp-1-cell-Transitive-Globular-Type :
    is-transitive' 1-cell-Transitive-Globular-Type
  comp-1-cell-Transitive-Globular-Type =
    comp-1-cell-is-transitive-Globular-Type
      is-transitive-Transitive-Globular-Type

  comp-2-cell-Transitive-Globular-Type :
    {x y : 0-cell-Transitive-Globular-Type} →
    is-transitive' (2-cell-Transitive-Globular-Type {x} {y})
  comp-2-cell-Transitive-Globular-Type =
    comp-2-cell-is-transitive-Globular-Type
      is-transitive-Transitive-Globular-Type

  comp-3-cell-Transitive-Globular-Type :
    {x y : 0-cell-Transitive-Globular-Type}
    {f g : 1-cell-Transitive-Globular-Type x y} →
    is-transitive' (3-cell-Transitive-Globular-Type {x} {y} {f} {g})
  comp-3-cell-Transitive-Globular-Type =
    comp-3-cell-is-transitive-Globular-Type
      is-transitive-Transitive-Globular-Type

open Transitive-Globular-Type public
```

### The predicate of being a transitive globular structure

```agda
is-transitive-globular-structure :
  {l1 l2 : Level} {A : UU l1} (G : globular-structure l2 A) → UU (l1 ⊔ l2)
is-transitive-globular-structure G =
  is-transitive-Globular-Type (make-Globular-Type G)
  
module _
  {l1 l2 : Level} {A : UU l1} {G : globular-structure l2 A}
  (t : is-transitive-globular-structure G)
  where

  comp-1-cell-is-transitive-globular-structure :
    is-transitive' (1-cell-globular-structure G)
  comp-1-cell-is-transitive-globular-structure =
    comp-1-cell-is-transitive-Globular-Type t

  is-transitive-globular-structure-1-cell-is-transitive-globular-structure :
    {x y : A} →
    is-transitive-globular-structure
      ( globular-structure-1-cell-globular-structure G x y)
  is-transitive-globular-structure-1-cell-is-transitive-globular-structure =
    is-transitive-1-cell-globular-type-is-transitive-Globular-Type t

  comp-2-cell-is-transitive-globular-structure :
    {x y : A} → is-transitive' (2-cell-globular-structure G {x} {y})
  comp-2-cell-is-transitive-globular-structure {x} {y} =
    comp-2-cell-is-transitive-Globular-Type t

  is-transitive-globular-structure-2-cell-is-transitive-globular-structure :
    {x y : A} {f g : 1-cell-globular-structure G x y} →
    is-transitive-globular-structure
      ( globular-structure-2-cell-globular-structure G f g)
  is-transitive-globular-structure-2-cell-is-transitive-globular-structure =
    is-transitive-2-cell-globular-type-is-transitive-Globular-Type t

  comp-3-cell-is-transitive-globular-structure :
    {x y : A} {f g : 1-cell-globular-structure G x y} →
    is-transitive' (3-cell-globular-structure G {x} {y} {f} {g})
  comp-3-cell-is-transitive-globular-structure =
    comp-3-cell-is-transitive-Globular-Type t
```

### The type of transitive globular structures on a type

```agda
transitive-globular-structure :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
transitive-globular-structure l2 A =
  Σ (globular-structure l2 A) (is-transitive-globular-structure)
```

## Examples

### The transitive globular structure on a type given by its identity types

```agda
is-transitive-globular-type-Type :
  {l : Level} (A : UU l) →
  is-transitive-Globular-Type (globular-type-Type A)
comp-1-cell-is-transitive-Globular-Type
  ( is-transitive-globular-type-Type A) q p =
  p ∙ q
is-transitive-1-cell-globular-type-is-transitive-Globular-Type
  ( is-transitive-globular-type-Type A) {x} {y} =
  is-transitive-globular-type-Type (x ＝ y)

is-transitive-globular-structure-Id :
  {l : Level} (A : UU l) →
  is-transitive-globular-structure (globular-structure-Id A)
comp-1-cell-is-transitive-Globular-Type
  ( is-transitive-globular-structure-Id A) q p = p ∙ q
is-transitive-1-cell-globular-type-is-transitive-Globular-Type
  ( is-transitive-globular-structure-Id A) {x} {y} =
  is-transitive-globular-structure-Id (x ＝ y)

transitive-globular-structure-Id :
  {l : Level} (A : UU l) → transitive-globular-structure l A
transitive-globular-structure-Id A =
  ( globular-structure-Id A , is-transitive-globular-structure-Id A)
```

## See also

- [Composition structure on globular types](structured-types.composition-structure-globular-types.md)
