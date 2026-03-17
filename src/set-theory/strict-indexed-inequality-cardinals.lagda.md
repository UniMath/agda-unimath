# Strict indexed inequality on cardinals

```agda
module set-theory.strict-indexed-inequality-cardinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.large-binary-relations
open import foundation.law-of-excluded-middle
open import foundation.mere-embeddings
open import foundation.negation
open import foundation.nonsurjective-maps
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.univalence
open import foundation.universe-levels

open import set-theory.cardinals
open import set-theory.complemented-inequality-cardinals
open import set-theory.inequality-cardinals
open import set-theory.inhabited-cardinals
```

</details>

## Idea

We may say a [cardinal](set-theory.cardinals.md) `X` is
{{#concept "indexed less than" Disambiguation="set-cardinal" Agda=le-indexed-Cardinal}}
a cardinal `Y` if `Y` is inhabited and any map `f` of
[sets](foundation-core.sets.md) from the isomorphism class of `X` into sets in
the isomorphism class of `Y` is
[nonsurjective](foundation.nonsurjective-maps.md) in the sense that there exists
an element in `Y` that `f` does not hit. This is a positive way of saying that
`X` is less than `Y`. This defines the
{{#concept "strict indexing ordering" Disambiguation="on set-cardinals"}}.

## Definition

### The underlying strict indexed inequality between cardinalities of sets

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  le-indexed-cardinality' : UU (l1 ⊔ l2)
  le-indexed-cardinality' =
    is-inhabited (type-Set Y) ×
    ((f : type-Set X → type-Set Y) → is-nonsurjective f)

  le-indexed-prop-cardinality' : Prop (l1 ⊔ l2)
  le-indexed-prop-cardinality' =
    product-Prop
      ( is-inhabited-Prop (type-Set Y))
      ( Π-Prop
        ( type-Set X → type-Set Y)
        ( is-nonsurjective-Prop))

  is-prop-le-indexed-cardinality' :
    is-prop le-indexed-cardinality'
  is-prop-le-indexed-cardinality' =
    is-prop-type-Prop le-indexed-prop-cardinality'
```

### Strict indexed inequality of a cardinal with respect to a set

```agda
module _
  {l1 l2 : Level} (X : Set l1)
  where

  le-indexed-prop-Cardinal' : Cardinal l2 → Prop (l1 ⊔ l2)
  le-indexed-prop-Cardinal' =
    map-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ l2))
      ( le-indexed-prop-cardinality' X)

  le-indexed-Cardinal' : Cardinal l2 → UU (l1 ⊔ l2)
  le-indexed-Cardinal' Y =
    type-Prop (le-indexed-prop-Cardinal' Y)

  compute-le-indexed-prop-Cardinal' :
    (Y : Set l2) →
    le-indexed-prop-Cardinal' (cardinality Y) ＝
    le-indexed-prop-cardinality' X Y
  compute-le-indexed-prop-Cardinal' =
    triangle-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ l2))
      ( le-indexed-prop-cardinality' X)
```

### Strict indexed inequality of cardinals

```agda
module _
  {l1 l2 : Level}
  where

  le-indexed-prop-Cardinal :
    Cardinal l1 → Cardinal l2 → Prop (l1 ⊔ l2)
  le-indexed-prop-Cardinal =
    map-universal-property-trunc-Set
      ( hom-set-Set (Cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
      ( le-indexed-prop-Cardinal')

  le-indexed-Cardinal : Cardinal l1 → Cardinal l2 → UU (l1 ⊔ l2)
  le-indexed-Cardinal X Y = type-Prop (le-indexed-prop-Cardinal X Y)
```

### Strict indexed inequality of cardinalities of sets

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  le-indexed-prop-cardinality : Prop (l1 ⊔ l2)
  le-indexed-prop-cardinality =
    le-indexed-prop-Cardinal (cardinality X) (cardinality Y)

  le-indexed-cardinality : UU (l1 ⊔ l2)
  le-indexed-cardinality = type-Prop le-indexed-prop-cardinality

  is-prop-le-indexed-cardinality : is-prop le-indexed-cardinality
  is-prop-le-indexed-cardinality = is-prop-type-Prop le-indexed-prop-cardinality

  eq-compute-le-indexed-prop-cardinality :
    le-indexed-prop-cardinality ＝ le-indexed-prop-cardinality' X Y
  eq-compute-le-indexed-prop-cardinality =
    ( htpy-eq
      ( triangle-universal-property-trunc-Set
        ( hom-set-Set (Cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
        ( le-indexed-prop-Cardinal')
        ( X))
      ( cardinality Y)) ∙
    ( compute-le-indexed-prop-Cardinal' X Y)

  eq-compute-le-indexed-cardinality :
    le-indexed-cardinality ＝ le-indexed-cardinality' X Y
  eq-compute-le-indexed-cardinality =
    ap type-Prop eq-compute-le-indexed-prop-cardinality

  compute-le-indexed-cardinality :
    le-indexed-cardinality ≃ le-indexed-cardinality' X Y
  compute-le-indexed-cardinality =
    equiv-eq eq-compute-le-indexed-cardinality

  unit-le-indexed-cardinality :
    le-indexed-cardinality' X Y → le-indexed-cardinality
  unit-le-indexed-cardinality = map-inv-equiv compute-le-indexed-cardinality

  inv-unit-le-indexed-cardinality :
    le-indexed-cardinality → le-indexed-cardinality' X Y
  inv-unit-le-indexed-cardinality = map-equiv compute-le-indexed-cardinality
```

## Properties

### Strict indexed inequality is irreflexive

```agda
module _
  {l : Level}
  where abstract

  irreflexive-le-indexed-cardinality' :
    (A : Set l) → ¬ le-indexed-cardinality' A A
  irreflexive-le-indexed-cardinality' A p =
    rec-trunc-Prop empty-Prop (λ (x , p) → p (x , refl)) (pr2 p id)

  irreflexive-le-indexed-cardinality :
    (A : Set l) → ¬ le-indexed-cardinality A A
  irreflexive-le-indexed-cardinality A =
    map-neg
      ( inv-unit-le-indexed-cardinality A A)
      ( irreflexive-le-indexed-cardinality' A)

  irreflexive-le-indexed-Cardinal :
    (A : Cardinal l) → ¬ le-indexed-Cardinal A A
  irreflexive-le-indexed-Cardinal =
    apply-dependent-universal-property-trunc-Set'
      ( λ X → set-Prop (neg-Prop (le-indexed-prop-Cardinal X X)))
      ( irreflexive-le-indexed-cardinality)
```
