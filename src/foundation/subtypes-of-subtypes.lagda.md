# Subtypes of subtypes

```agda
module foundation.subtypes-of-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

If `S` is a [subtype](foundation-core.subtypes.md) of `X`, and `T` is a subtype
of the type of `S`, then `T` is [equivalent](foundation-core.equivalences.md) to
a subtype of `X`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  {X : UU l1}
  (S : subtype l2 X)
  (T : subtype l3 (type-subtype S))
  where

  subtype-subtype-of-subtype : subtype (l2 ⊔ l3) X
  subtype-subtype-of-subtype x = Σ-Prop (S x) (λ x∈S → T (x , x∈S))

  type-subtype-of-subtype : UU (l1 ⊔ l2 ⊔ l3)
  type-subtype-of-subtype = type-subtype subtype-subtype-of-subtype

  equiv-subtype-of-subtype : type-subtype T ≃ type-subtype-of-subtype
  equiv-subtype-of-subtype = associative-Σ

  map-subtype-of-subtype : type-subtype T → type-subtype-of-subtype
  map-subtype-of-subtype = map-associative-Σ

  map-inv-subtype-of-subtype : type-subtype-of-subtype → type-subtype T
  map-inv-subtype-of-subtype = map-inv-associative-Σ
```
