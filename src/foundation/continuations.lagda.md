# The continuation monad

```agda
module foundation.continuations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.logical-equivalences
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-cartesian-product-types
open import foundation.universal-property-empty-type
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.transport-along-identifications

open import orthogonal-factorization-systems.extensions-dependent-maps
open import orthogonal-factorization-systems.extensions-maps
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.types-local-at-maps
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

Given a type `R`, the
{{#concept "continuation monad" Disambiguation="on a type" Agda=continuation}}
on `R` is the functorial construction defined on types by

```text
  A ↦ ((A → R) → R).
```

## Definitions

### The operator of the continuation monad

```agda
continuation :
  {l1 l2 : Level} (R : UU l1) (A : UU l2) → UU (l1 ⊔ l2)
continuation R A = (A → R) → R
```

### The functorial action of the continuation monad on maps

```agda
map-continuation :
  {l1 l2 l3 : Level} {R : UU l1} {A : UU l2} {B : UU l3} →
  (A → B) → continuation R A → continuation R B
map-continuation f c g = c (g ∘ f)
```

### The unit of the continuation monad

```agda
unit-continuation :
  {l1 l2 : Level} {R : UU l1} {A : UU l2} → A → continuation R A
unit-continuation = ev
```

### Maps into `continuation R A` extend along the unit

Every `f` as in the following diagram
[extends](orthogonal-factorization-systems.extensions-maps.md) along the unit of
its domain

```text
               f
         A -------> continuation R B
         |           ∧
     η_A |         ⋰
         ∨       ⋰
  continuation R A.
```

```agda
module _
  {l1 l2 l3 : Level} {R : UU l1} {A : UU l2} {B : UU l3}
  where

  extend-continuation :
    (A → continuation R B) → (continuation R A → continuation R B)
  extend-continuation f c g = c (λ a → f a g)

  is-extension-extend-continuation :
    (f : A → continuation R B) →
    is-extension unit-continuation f (extend-continuation f)
  is-extension-extend-continuation f = refl-htpy

  extension-continuation :
    (f : A → continuation R B) → extension unit-continuation f
  extension-continuation f =
    ( extend-continuation f , is-extension-extend-continuation f)
```

### The monoidal multiplication operation of the continuation monad

```agda
mul-continuation :
  {l1 l2 : Level} {R : UU l1} {A : UU l2} →
  continuation R (continuation R A) → continuation R A
mul-continuation f c = f (ev c)
```

## Properties

### The right unit law for the continuation monad

```agda
module _
  {l1 l2 : Level} {R : UU l1} {A : UU l2}
  where

  right-unit-law-mul-continuation :
    mul-continuation {R = R} ∘ unit-continuation {R = R} {continuation R A} ~ id
  right-unit-law-mul-continuation = refl-htpy
```

### The continuation monad on propositions gives propositions

```agda
is-prop-continuation :
  {l1 l2 : Level} {R : UU l1} {A : UU l2} →
  is-prop R → is-prop (continuation R A)
is-prop-continuation = is-prop-function-type

is-prop-continuation-Prop :
  {l1 l2 : Level} (R : Prop l1) {A : UU l2} →
  is-prop (continuation (type-Prop R) A)
is-prop-continuation-Prop R = is-prop-continuation (is-prop-type-Prop R)

continuation-Prop :
  {l1 l2 : Level} (R : Prop l1) (A : UU l2) → Prop (l1 ⊔ l2)
continuation-Prop R A =
  ( continuation (type-Prop R) A , is-prop-continuation (is-prop-type-Prop R))
```

### Computing `continuation R` on the unit type

We have the [equivalence](foundation-core.equivalences.md)

```text
  continuation R unit ≃ (R → R).
```

```agda
module _
  {l1 : Level} {R : UU l1}
  where

  compute-unit-continuation : continuation R unit ≃ (R → R)
  compute-unit-continuation =
    equiv-precomp (inv-left-unit-law-function-type R) R
```

### Computing `continuation R` on the empty type

We have the equivalence

```text
  continuation R empty ≃ R.
```

```agda
module _
  {l1 : Level} {R : UU l1}
  where

  compute-empty-continuation : continuation R empty ≃ R
  compute-empty-continuation =
    left-unit-law-Π-is-contr (universal-property-empty' R) ex-falso
```

## External links

- [continuation monad](https://ncatlab.org/nlab/show/continuation+monad) at
  $n$Lab
