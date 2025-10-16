# Inhabited cardinals

```agda
module set-theory.inhabited-cardinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.univalence
open import foundation.universe-levels

open import set-theory.cardinalities
```

</details>

## Idea

A [cardinal of sets](set-theory.cardinalities.lagda.md) `κ` is
{{#concept "inhabited" Disambiguation="cardinal"  Agda=is-inhabited-Cardinal}},
if any [set](foundation-core.sets.md) in its isomorphism class is
[inhabited](foundation-core.inhabited.md).

## Definitions

### The predicate on cardinals of being inhabited

```agda
module _
  {l : Level} (κ : Cardinal l)
  where

  is-inhabited-prop-Cardinal : Prop l
  is-inhabited-prop-Cardinal =
    apply-universal-property-trunc-Set' κ
      ( Prop-Set l)
      ( is-inhabited-Prop ∘ type-Set)

  is-inhabited-Cardinal : UU l
  is-inhabited-Cardinal = type-Prop is-inhabited-prop-Cardinal

  is-prop-is-inhabited-Cardinal : is-prop is-inhabited-Cardinal
  is-prop-is-inhabited-Cardinal =
    is-prop-type-Prop is-inhabited-prop-Cardinal
```

### Inhabited cardinalities

```agda
module _
  {l : Level} (X : Set l)
  where

  is-inhabited-prop-cardinality : Prop l
  is-inhabited-prop-cardinality = is-inhabited-prop-Cardinal (cardinality X)

  is-inhabited-cardinality : UU l
  is-inhabited-cardinality = is-inhabited-Cardinal (cardinality X)

  is-prop-is-inhabited-cardinality : is-prop is-inhabited-cardinality
  is-prop-is-inhabited-cardinality =
    is-prop-is-inhabited-Cardinal (cardinality X)

  eq-compute-is-inhabited-prop-cardinality :
    is-inhabited-prop-cardinality ＝ is-inhabited-Prop (type-Set X)
  eq-compute-is-inhabited-prop-cardinality =
    triangle-universal-property-trunc-Set
      ( Prop-Set l)
      ( is-inhabited-Prop ∘ type-Set)
      ( X)

  eq-compute-is-inhabited-cardinality :
    is-inhabited-cardinality ＝ is-inhabited (type-Set X)
  eq-compute-is-inhabited-cardinality =
    ap type-Prop eq-compute-is-inhabited-prop-cardinality

  compute-is-inhabited-cardinality :
    is-inhabited-cardinality ≃ is-inhabited (type-Set X)
  compute-is-inhabited-cardinality =
    equiv-eq eq-compute-is-inhabited-cardinality

  unit-is-inhabited-cardinality :
    is-inhabited (type-Set X) → is-inhabited-cardinality
  unit-is-inhabited-cardinality =
    map-inv-equiv compute-is-inhabited-cardinality

  inv-unit-is-inhabited-cardinality :
    is-inhabited-cardinality → is-inhabited (type-Set X)
  inv-unit-is-inhabited-cardinality =
    map-equiv compute-is-inhabited-cardinality
```

### The universe of inhabited cardinals

```agda
Inhabited-Cardinal : (l : Level) → UU (lsuc l)
Inhabited-Cardinal l = Σ (Cardinal l) is-inhabited-Cardinal

module _
  {l : Level} (κ : Inhabited-Cardinal l)
  where

  cardinal-Inhabited-Cardinal : Cardinal l
  cardinal-Inhabited-Cardinal = pr1 κ

  is-inhabited-Inhabited-Cardinal :
    is-inhabited-Cardinal cardinal-Inhabited-Cardinal
  is-inhabited-Inhabited-Cardinal = pr2 κ
```
