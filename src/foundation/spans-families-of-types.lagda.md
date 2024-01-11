# Spans of families of types

```agda
module foundation.spans-families-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
```

</details>

## Idea

Consider a family of types `A i` indexed by `i : I`. A {{#concept "span" Disambiguation="family of types"}} on `A` consists of a type `S` equipped with a family of maps

```text
  (i : I) → S → A i.
```

The type `S` is called the {{#concept "spanning type" Disambiguation="span of family of types"}} of the span.

## Definitions

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

### Permutations of spans of fixed families of types

Permutations of spans of fixed families of types are a generalization of the
opposite of a binary span with fixed domain and codomain.

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2}
  where

  permutation-span-fixed-family-of-types :
    (e : I ≃ I) → span-fixed-family-of-types l3 A →
    span-fixed-family-of-types l3 (A ∘ map-equiv e)
  pr1 (permutation-span-fixed-family-of-types e s) =
    spanning-type-span-fixed-family-of-types s
  pr2 (permutation-span-fixed-family-of-types e s) i =
    map-span-fixed-family-of-types s (map-equiv e i)
```

## See also

- [(Binary) spans](foundation.spans.md)
