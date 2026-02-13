# Cospans of types

```agda
module foundation.cospans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A {{#concept "cospan" Disambiguation="types" Agda=cospan}} from `A` to `B`
consists of a type `X` and maps `f : A → X` and `g : B → X`, as indicated in the
diagram

```text
      f         g
  A -----> X <----- B
```

We disambiguate between cospans and
[cospan diagrams](foundation.cospan-diagrams.md). We consider a cospan from `A`
to `B` a morphism from `A` to `B` in the category of types and cospans between
them, whereas we consider cospan diagrams to be _objects_ in the category of
diagrams of types of the form `* <---- * ----> *`. Conceptually there is a
subtle, but important distinction between cospans and cospan diagrams. Cospan
diagrams are more suitable for functorial operations that take "cospans" as
input, but for which the functorial action takes a natural transformation, i.e.,
a morphism of cospan diagrams, as input. Examples of this kind include
[pullbacks](foundation.pullbacks.md).

## Definitions

### Cospans

```agda
cospan :
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
cospan l A B = Σ (UU l) (λ X → (A → X) × (B → X))

module _
  {l1 l2 : Level} {l : Level} {A : UU l1} {B : UU l2} (c : cospan l A B)
  where

  cospanning-type-cospan : UU l
  cospanning-type-cospan = pr1 c

  left-map-cospan : A → cospanning-type-cospan
  left-map-cospan = pr1 (pr2 c)

  right-map-cospan : B → cospanning-type-cospan
  right-map-cospan = pr2 (pr2 c)
```

### The identity cospan

```agda
id-cospan : {l : Level} (A : UU l) → cospan l A A
id-cospan A = (A , id , id)
```

### The swapping operation on cospans

```agda
swap-cospan :
  {l1 l2 : Level} {l : Level} {A : UU l1} {B : UU l2} →
  cospan l A B → cospan l B A
swap-cospan (C , f , g) = (C , g , f)
```

## See also

- The formal dual of cospans is [spans](foundation.spans.md).
- [Pullbacks](foundation-core.pullbacks.md) are limits of
  [cospan diagrams](foundation.cospan-diagrams.md).

### Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
