# The globular type of dependent functions

```agda
{-# OPTIONS --guardedness #-}

module foundation.globular-type-of-dependent-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.homotopies

open import globular-types.globular-types
open import globular-types.reflexive-globular-types
open import globular-types.transitive-globular-types
```

</details>

## Idea

The
{{#concept "globular type of dependent functions" Agda=dependent-function-type-Globular-Type}}
is the [globular type](globular-types.globular-types.md) consisting of
[dependent functions](foundation.dependent-function-types.md) and
[homotopies](foundation-core.homotopies.md) between them. Since homotopies are
themselves defined to be certain dependent functions, they directly provide a
globular structure on dependent function types.

The globular type of dependent functions of a type family `B` over `A` is
[reflexive](globular-types.reflexive-globular-types.md) and
[transitive](globular-types.transitive-globular-types.md), so it is a
[noncoherent ω-precategory](wild-category-theory.noncoherent-omega-precategories.md).

The structures defined in this file are used to define the
[wild category of types](foundation.wild-category-of-types.md).

## Definitions

### The globular type of dependent functions

```agda
dependent-function-type-Globular-Type :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
0-cell-Globular-Type (dependent-function-type-Globular-Type A B) =
  (x : A) → B x
1-cell-globular-type-Globular-Type
  ( dependent-function-type-Globular-Type A B) f g =
  dependent-function-type-Globular-Type A (eq-value f g)
```

## Properties

### The globular type of dependent functions is reflexive

```agda
is-reflexive-dependent-function-type-Globular-Type :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-reflexive-Globular-Type (dependent-function-type-Globular-Type A B)
is-reflexive-1-cell-is-reflexive-Globular-Type
  is-reflexive-dependent-function-type-Globular-Type f =
  refl-htpy
is-reflexive-1-cell-globular-type-is-reflexive-Globular-Type
  is-reflexive-dependent-function-type-Globular-Type =
  is-reflexive-dependent-function-type-Globular-Type

dependent-function-type-Reflexive-Globular-Type :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  Reflexive-Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
globular-type-Reflexive-Globular-Type
  ( dependent-function-type-Reflexive-Globular-Type A B) =
  dependent-function-type-Globular-Type A B
refl-Reflexive-Globular-Type
  ( dependent-function-type-Reflexive-Globular-Type A B) =
  is-reflexive-dependent-function-type-Globular-Type
```

### The globular type of dependent functions is transitive

```agda
is-transitive-dependent-function-type-Globular-Type :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-transitive-Globular-Type (dependent-function-type-Globular-Type A B)
comp-1-cell-is-transitive-Globular-Type
  is-transitive-dependent-function-type-Globular-Type K H =
  H ∙h K
is-transitive-1-cell-globular-type-is-transitive-Globular-Type
  is-transitive-dependent-function-type-Globular-Type =
  is-transitive-dependent-function-type-Globular-Type

dependent-function-type-Transitive-Globular-Type :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  Transitive-Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
globular-type-Transitive-Globular-Type
  ( dependent-function-type-Transitive-Globular-Type A B) =
  dependent-function-type-Globular-Type A B
is-transitive-Transitive-Globular-Type
  ( dependent-function-type-Transitive-Globular-Type A B) =
  is-transitive-dependent-function-type-Globular-Type
```

## See also

- [The globular type of functions](foundation.globular-type-of-functions.md)
- [The wild category of types](foundation.wild-category-of-types.md)
