# Empty subtypes

```agda
module foundation.empty-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.intersections-subtypes
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

A [subtype](foundation-core.subtypes.md) is an
{{#concept "empty" WDID=Q226183 WD="empty set" Agda=is-empty-subtype}} subtype
if is is [empty](foundation.empty-types.md) as a type.

## Definition

```agda
module _
  {l1 l2 : Level} {X : UU l1} (S : subtype l2 X)
  where

  is-empty-prop-subtype : Prop (l1 ⊔ l2)
  is-empty-prop-subtype = Π-Prop X (λ x → ¬' (S x))

  is-empty-subtype : UU (l1 ⊔ l2)
  is-empty-subtype = type-Prop is-empty-prop-subtype

empty-subtype : {l : Level} (l2 : Level) (X : UU l) → subtype l2 X
empty-subtype l2 _ _ = raise-empty-Prop l2

is-empty-subtype-empty-subtype :
  {l1 l2 : Level} (X : UU l1) → is-empty-subtype (empty-subtype l2 X)
is-empty-subtype-empty-subtype X x = map-inv-raise
```

## Properties

### A subtype is empty iff its type is empty

```agda
module _
  {l1 l2 : Level} {X : UU l1} (S : subtype l2 X)
  where

  is-empty-type-empty-subtype : is-empty-subtype S → is-empty (type-subtype S)
  is-empty-type-empty-subtype is-empty-S (x , x∈S) = is-empty-S x x∈S

  is-empty-subtype-is-empty-type-subtype :
    is-empty (type-subtype S) → is-empty-subtype S
  is-empty-subtype-is-empty-type-subtype is-empty-type-S x x∈S =
    is-empty-type-S (x , x∈S)
```

### Empty subtypes at a given level are torsorial

```agda
module _
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  abstract
    is-torsorial-is-empty-subtype :
      is-torsorial (is-empty-subtype {l2 = l2} {X = X})
    is-torsorial-is-empty-subtype =
      ( (empty-subtype l2 X , is-empty-subtype-empty-subtype X) ,
        λ (S , is-empty-S) →
          eq-pair-Σ
            ( eq-has-same-elements-subtype _ _
              ( λ x → (ex-falso ∘ map-inv-raise , map-raise ∘ is-empty-S x)))
            ( eq-is-prop (is-prop-type-Prop (is-empty-prop-subtype {X = X} S))))
```

### The empty subtype is contained in all other subtypes

```agda
module _
  {l1 l2 : Level} (l3 : Level) {X : UU l1} (S : subtype l2 X)
  where

  empty-subtype-leq-subtype : empty-subtype l3 X ⊆ S
  empty-subtype-leq-subtype x (map-raise ⊥) = ex-falso ⊥
```
