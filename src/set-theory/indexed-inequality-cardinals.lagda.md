# Indexed inequality on cardinals

```agda
module set-theory.indexed-inequality-cardinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality-axiom
open import foundation.identity-types
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.univalence
open import foundation.universe-levels

open import set-theory.cardinals
```

</details>

## Idea

A [cardinal](set-theory.cardinals.md) `X` is
{{#concept "indexed less than or equal to" Disambiguation="cardinal" Agda=leq-indexed-Cardinal}}
a cardinal `Y`, written `X ≤ⁱ Y`, if there
[merely exists](foundation.propositional-truncations.md) a
[surjection](foundation.surjective-maps.md) from a representative of `Y` onto a
representative of `X`.

## Definitions

### Indexed boundedness of the cardinality of a set

```agda
module _
  {l1 l2 : Level} (X : Set l1)
  where

  leq-indexed-prop-Cardinal' : Cardinal l2 → Prop (l1 ⊔ l2)
  leq-indexed-prop-Cardinal' =
    map-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ l2))
      ( λ Y' → trunc-Prop (type-Set Y' ↠ type-Set X))

  compute-leq-indexed-prop-Cardinal' :
    (Y : Set l2) →
    leq-indexed-prop-Cardinal' (cardinality Y) ＝
    trunc-Prop (type-Set Y ↠ type-Set X)
  compute-leq-indexed-prop-Cardinal' =
    triangle-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ l2))
      ( λ Y' → trunc-Prop (type-Set Y' ↠ type-Set X))
```

### Indexed inequality of cardinals

```agda
module _
  {l1 l2 : Level}
  where

  leq-indexed-prop-Cardinal :
    Cardinal l1 → Cardinal l2 → Prop (l1 ⊔ l2)
  leq-indexed-prop-Cardinal =
    map-universal-property-trunc-Set
      ( hom-set-Set (Cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
      ( leq-indexed-prop-Cardinal')

  leq-indexed-Cardinal :
    Cardinal l1 → Cardinal l2 → UU (l1 ⊔ l2)
  leq-indexed-Cardinal X Y =
    type-Prop (leq-indexed-prop-Cardinal X Y)

  is-prop-leq-indexed-Cardinal :
    {X : Cardinal l1} {Y : Cardinal l2} →
    is-prop (leq-indexed-Cardinal X Y)
  is-prop-leq-indexed-Cardinal {X} {Y} =
    is-prop-type-Prop (leq-indexed-prop-Cardinal X Y)
```

### Indexed inequality of cardinalities

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2)
  where

  leq-indexed-prop-cardinality : Prop (l1 ⊔ l2)
  leq-indexed-prop-cardinality =
    leq-indexed-prop-Cardinal (cardinality X) (cardinality Y)

  leq-indexed-cardinality : UU (l1 ⊔ l2)
  leq-indexed-cardinality =
    leq-indexed-Cardinal (cardinality X) (cardinality Y)

  is-prop-leq-indexed-cardinality :
    is-prop leq-indexed-cardinality
  is-prop-leq-indexed-cardinality =
    is-prop-leq-indexed-Cardinal

  compute-leq-indexed-prop-cardinality' :
    leq-indexed-prop-cardinality ＝
    trunc-Prop (type-Set Y ↠ type-Set X)
  compute-leq-indexed-prop-cardinality' =
    ( htpy-eq
      ( triangle-universal-property-trunc-Set
        ( hom-set-Set (Cardinal-Set l2) (Prop-Set (l1 ⊔ l2)))
        ( leq-indexed-prop-Cardinal') X) (cardinality Y)) ∙
    ( compute-leq-indexed-prop-Cardinal' X Y)

  compute-leq-indexed-cardinality' :
    leq-indexed-cardinality ＝
    type-trunc-Prop (type-Set Y ↠ type-Set X)
  compute-leq-indexed-cardinality' =
    ap type-Prop compute-leq-indexed-prop-cardinality'

  compute-leq-indexed-cardinality :
    leq-indexed-cardinality ≃
    type-trunc-Prop (type-Set Y ↠ type-Set X)
  compute-leq-indexed-cardinality =
    equiv-eq compute-leq-indexed-cardinality'

  unit-leq-indexed-cardinality :
    type-trunc-Prop (type-Set Y ↠ type-Set X) →
    leq-indexed-cardinality
  unit-leq-indexed-cardinality =
    map-inv-equiv compute-leq-indexed-cardinality

  inv-unit-leq-indexed-cardinality :
    leq-indexed-cardinality →
    type-trunc-Prop (type-Set Y ↠ type-Set X)
  inv-unit-leq-indexed-cardinality =
    pr1 compute-leq-indexed-cardinality
```

## See also

- [Strict indexed inequality on cardinals](set-theory.strict-indexed-inequality-cardinals.md)
