# Strict complemented boundedness on cardinals

```agda
module set-theory.strict-complemented-boundedness-cardinalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-embeddings
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.law-of-excluded-middle
open import foundation.mere-embeddings
open import foundation.nonsurjective-maps
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.univalence
open import foundation.universe-levels

open import set-theory.cardinalities
open import set-theory.inequality-cardinalities
```

</details>

## Idea

We say a [cardinal of sets](set-theory.cardinalities.md) `X` is
{{#concept "strictly complemented bounded" Agda=strictly-complemented-bounded-Cardinal}}
by a cardinal `Y` if every decidable embedding of a
[set](foundation-core.sets.md) in the isomorphism class represented by `X` into
a set in the isomorphism class represented by `Y` is
[nonsurjective](foundation.nonsurjective-maps.md) in the sense that there is an
element in `Y` it does not hit.

## Definition

### Strict complemented boundedness of cardinality of a set with respect to a set

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  strictly-complemented-bounded-cardinality : UU (l1 ⊔ l2)
  strictly-complemented-bounded-cardinality =
    (f : type-Set X ↪ᵈ type-Set Y) → is-nonsurjective (map-decidable-emb f)

  strictly-complemented-bounded-prop-cardinality : Prop (l1 ⊔ l2)
  strictly-complemented-bounded-prop-cardinality =
    Π-Prop
      ( type-Set X ↪ᵈ type-Set Y)
      ( is-nonsurjective-Prop ∘ map-decidable-emb)

  is-prop-strictly-complemented-bounded-cardinality :
    is-prop strictly-complemented-bounded-cardinality
  is-prop-strictly-complemented-bounded-cardinality =
    is-prop-type-Prop strictly-complemented-bounded-prop-cardinality
```

### Strict complemented boundedness of a cardinal with respect to a set

```agda
module _
  {l1 l2 : Level} (X : Set l1)
  where

  strictly-complemented-bounded-prop-Cardinal' : Cardinal l2 → Prop (l1 ⊔ l2)
  strictly-complemented-bounded-prop-Cardinal' =
    map-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ l2))
      ( strictly-complemented-bounded-prop-cardinality X)

  strictly-complemented-bounded-Cardinal' : Cardinal l2 → UU (l1 ⊔ l2)
  strictly-complemented-bounded-Cardinal' Y =
    type-Prop (strictly-complemented-bounded-prop-Cardinal' Y)

  compute-strictly-complemented-bounded-prop-Cardinal' :
    (Y : Set l2) →
    strictly-complemented-bounded-prop-Cardinal' (cardinality Y) ＝
    strictly-complemented-bounded-prop-cardinality X Y
  compute-strictly-complemented-bounded-prop-Cardinal' =
    triangle-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ l2))
      ( strictly-complemented-bounded-prop-cardinality X)
```

### Strict complemented boundedness of cardinals

```agda
module _
  {l1 l2 : Level}
  where

  strictly-complemented-bounded-prop-Cardinal :
    Cardinal l1 → Cardinal l2 → Prop (l1 ⊔ l2)
  strictly-complemented-bounded-prop-Cardinal =
    map-universal-property-trunc-Set
      ( hom-set-Set (Cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
      ( strictly-complemented-bounded-prop-Cardinal')

  strictly-complemented-bounded-Cardinal :
    Cardinal l1 → Cardinal l2 → UU (l1 ⊔ l2)
  strictly-complemented-bounded-Cardinal X Y =
    type-Prop (strictly-complemented-bounded-prop-Cardinal X Y)

  compute-strictly-complemented-bounded-prop-Cardinal :
    (X : Set l1) (Y : Set l2) →
    strictly-complemented-bounded-prop-Cardinal
      ( cardinality X)
      ( cardinality Y) ＝
    strictly-complemented-bounded-prop-cardinality X Y
  compute-strictly-complemented-bounded-prop-Cardinal X Y =
    ( htpy-eq
      ( triangle-universal-property-trunc-Set
        ( hom-set-Set (Cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
        ( strictly-complemented-bounded-prop-Cardinal')
        ( X))
      ( cardinality Y)) ∙
    ( compute-strictly-complemented-bounded-prop-Cardinal' X Y)
```
