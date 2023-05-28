# Union of subtypes

```agda
module foundation.unions-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.large-locale-of-subtypes
open import foundation.propositional-truncations

open import foundation-core.subtypes
open import foundation-core.universe-levels
```

</details>

## Idea

The union of two subtypes `A` and `B` is the subtype that contains the elements
that are in `A` or in `B`.

## Definition

### Unions of subtypes

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  where

  union-subtype : subtype l1 X → subtype l2 X → subtype (l1 ⊔ l2) X
  union-subtype P Q x = disj-Prop (P x) (Q x)
```

### Unions of decidable subtypes

```agda
  union-decidable-subtype :
    decidable-subtype l1 X → decidable-subtype l2 X →
    decidable-subtype (l1 ⊔ l2) X
  union-decidable-subtype P Q x = disj-Decidable-Prop (P x) (Q x)
```

### Unions of families of subtypes

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1}
  where

  union-family-of-subtypes :
    {I : UU l2} (A : I → subtype l3 X) → subtype (l2 ⊔ l3) X
  union-family-of-subtypes = sup-power-set-Large-Locale
```

## Properties

### The union of families of subtypes preserves indexed inclusion

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {I : UU l2}
  (A : I → subtype l3 X) (B : I → subtype l4 X)
  where

  preserves-order-union-of-subtypes :
    ((i : I) → A i ⊆ B i) →
    union-family-of-subtypes A ⊆ union-family-of-subtypes B
  preserves-order-union-of-subtypes H x p =
    apply-universal-property-trunc-Prop p
      ( union-family-of-subtypes B x)
      ( λ (i , q) → unit-trunc-Prop (i , H i x q))
```
