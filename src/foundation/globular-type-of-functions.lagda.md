# The globular type of functions

```agda
{-# OPTIONS --guardedness #-}

module foundation.globular-type-of-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.globular-type-of-dependent-functions
open import foundation.universe-levels

open import foundation-core.homotopies

open import globular-types.globular-types
open import globular-types.reflexive-globular-types
open import globular-types.transitive-globular-types
```

</details>

## Idea

The {{#concept "globular type of functions" Agda=function-type-Globular-Type}}
is the [globular type](globular-types.globular-types.md) consisting of
[functions](foundation.function-types.md) and
[homotopies](foundation-core.homotopies.md) between them. Since functions are
dependent functions of constant type families, we define the globular type of
functions in terms of the
[globular type of dependent functions](foundation.globular-type-of-dependent-functions.md).

The globular type of functions of a type family `B` over `A` is
[reflexive](globular-types.reflexive-globular-types.md) and
[transitive](globular-types.transitive-globular-types.md), so it is a
[noncoherent ω-precategory](wild-category-theory.noncoherent-omega-precategories.md).

The structures defined in this file are used to define the
[large category of types](foundation.wild-category-of-types.md).

## Definitions

### The globular type of functions

```agda
function-type-Globular-Type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
function-type-Globular-Type A B =
  dependent-function-type-Globular-Type A (λ _ → B)
```

## Properties

### The globular type of functions is reflexive

```agda
is-reflexive-function-type-Globular-Type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-reflexive-Globular-Type (function-type-Globular-Type A B)
is-reflexive-function-type-Globular-Type {l1} {l2} {A} {B} =
  is-reflexive-dependent-function-type-Globular-Type

function-type-Reflexive-Globular-Type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  Reflexive-Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
function-type-Reflexive-Globular-Type A B =
  dependent-function-type-Reflexive-Globular-Type A (λ _ → B)
```

### The globular type of functions is transitive

```agda
is-transitive-function-type-Globular-Type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-transitive-Globular-Type (function-type-Globular-Type A B)
is-transitive-function-type-Globular-Type =
  is-transitive-dependent-function-type-Globular-Type

function-type-Transitive-Globular-Type :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  Transitive-Globular-Type (l1 ⊔ l2) (l1 ⊔ l2)
function-type-Transitive-Globular-Type A B =
  dependent-function-type-Transitive-Globular-Type A (λ _ → B)
```

## See also

- [The globular type of functions](foundation.globular-type-of-functions.md)
- [The wild category of types](foundation.wild-category-of-types.md)
