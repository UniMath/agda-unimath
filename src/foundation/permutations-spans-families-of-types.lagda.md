# Permutations of spans of families of types

```agda
module foundation.permutations-spans-families-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.spans-families-of-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
```

</details>

## Idea

Permutations of spans of families of types are a generalization of the
[opposite](foundation.opposite-spans.md) of a
[binary span](foundation.spans.md). Consider a
[span](foundation.spans-families-of-types.md) `(S , f)` on a type family
`A : I → 𝒰` and an [equivalence](foundation-core.equivalences.md) `e : I ≃ I`.
Then the {{#concept "permutation" Disambiguation="spans of families of types"}}
is the span `(S , f ∘ e)` on the type family `A ∘ e`.

## Definitions

### Permutations of spans of families of types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2}
  where

  permutation-span-type-family :
    (e : I ≃ I) → span-type-family l3 A →
    span-type-family l3 (A ∘ map-equiv e)
  pr1 (permutation-span-type-family e s) =
    spanning-type-span-type-family s
  pr2 (permutation-span-type-family e s) i =
    map-span-type-family s (map-equiv e i)
```
