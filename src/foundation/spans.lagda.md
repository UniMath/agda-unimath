# Spans of types

```agda
module foundation.spans where
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
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A **(binary) span** is a pair of functions with a common domain, i.e., it is a
diagram of the form

```text
  A <----- S -----> B.
```

More precisely, a **binary span from `A` to `B`** consists of a type `S` and two
maps `f : S → A` and `g : S → B`. In this case, the types `A` and `B` are also
referred to as the **domain** and **codomain** of the span, respectively, and
the type `S` is referred to as the **spanning type** of the span.

We also consider the notion of **total (binary) span**, which consists of two
types `A` and `B` and a binary span from `A` to `B`.

More generally, given a family of types `A i` indexed by `i : I`, a **span** on
`A` consists of a type `S` and a family of maps `f i : S → A i` indexed by
`i : I`.

## Definition

### (Binary) spans with fixed domain and codomain

```agda
span-fixed-domain-codomain :
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
span-fixed-domain-codomain l A B =
  Σ (UU l) (λ X → (X → A) × (X → B))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (c : span-fixed-domain-codomain l3 A B)
  where

  spanning-type-span-fixed-domain-codomain : UU l3
  spanning-type-span-fixed-domain-codomain = pr1 c

  left-map-span-fixed-domain-codomain :
    spanning-type-span-fixed-domain-codomain → A
  left-map-span-fixed-domain-codomain = pr1 (pr2 c)

  right-map-span-fixed-domain-codomain :
    spanning-type-span-fixed-domain-codomain → B
  right-map-span-fixed-domain-codomain = pr2 (pr2 c)
```

### (Binary) spans

```agda
span : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
span l1 l2 l3 =
  Σ (UU l1) (λ A → Σ (UU l2) (λ B → span-fixed-domain-codomain l3 A B))

module _
  {l1 l2 l3 : Level} (s : span l1 l2 l3)
  where

  domain-span : UU l1
  domain-span = pr1 s

  codomain-span : UU l2
  codomain-span = pr1 (pr2 s)

  span-fixed-domain-codomain-span :
    span-fixed-domain-codomain l3 domain-span codomain-span
  span-fixed-domain-codomain-span = pr2 (pr2 s)

  spanning-type-span : UU l3
  spanning-type-span =
    spanning-type-span-fixed-domain-codomain span-fixed-domain-codomain-span

  left-map-span : spanning-type-span → domain-span
  left-map-span =
    left-map-span-fixed-domain-codomain span-fixed-domain-codomain-span

  right-map-span : spanning-type-span → codomain-span
  right-map-span =
    right-map-span-fixed-domain-codomain span-fixed-domain-codomain-span
```

### Spans of fixed families of types

```agda
module _
  {l1 l2 : Level} (l3 : Level) {I : UU l1} (A : I → UU l2)
  where

  span-fixed-family-of-types : UU (l1 ⊔ l2 ⊔ lsuc l3)
  span-fixed-family-of-types = Σ (UU l3) (λ S → (i : I) → S → A i)

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2}
  (s : span-fixed-family-of-types l3 A)
  where

  spanning-type-span-fixed-family-of-types : UU l3
  spanning-type-span-fixed-family-of-types = pr1 s

  map-span-fixed-family-of-types :
    (i : I) → spanning-type-span-fixed-family-of-types → A i
  map-span-fixed-family-of-types = pr2 s
```

### Spans of families of types

Note: We might have to rename the following definition of spans of families of
types to _spans of families of types with fixed indexing type_.

```agda
span-family-of-types :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
span-family-of-types l2 l3 I =
  Σ (I → UU l2) (λ A → span-fixed-family-of-types l3 A)

module _
  {l1 l2 l3 : Level} {I : UU l1} (s : span-family-of-types l2 l3 I)
  where

  family-span-family-of-types : I → UU l2
  family-span-family-of-types = pr1 s

  span-fixed-family-of-types-span-family-of-types :
    span-fixed-family-of-types l3 family-span-family-of-types
  span-fixed-family-of-types-span-family-of-types = pr2 s

  spanning-type-span-family-of-types : UU l3
  spanning-type-span-family-of-types =
    spanning-type-span-fixed-family-of-types
      ( span-fixed-family-of-types-span-family-of-types)

  map-span-family-of-types :
    (i : I) → spanning-type-span-family-of-types →
    family-span-family-of-types i
  map-span-family-of-types =
    map-span-fixed-family-of-types
      ( span-fixed-family-of-types-span-family-of-types)
```

## Properties

### Binary spans with fixed domain and codomain are equivalent to binary relations

This remains to be shown.
[#767](https://github.com/UniMath/agda-unimath/issues/767)

## See also

- The dual concept of spans is [cospans](foundation.cospans.md).
