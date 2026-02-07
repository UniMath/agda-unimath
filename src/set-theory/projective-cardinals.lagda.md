# Projective cardinals

```agda
module set-theory.projective-cardinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.projective-types
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.set-truncations
open import foundation.sets
open import foundation.subtypes
open import foundation.univalence
open import foundation.universe-levels

open import set-theory.cardinals
```

</details>

## Idea

A [cardinal](set-theory.cardinals.md) `κ` is
{{#concept "projective" Disambiguation="set-cardinal" Agda=is-projective-Cardinal}},
if any [set](foundation-core.sets.md) in its isomorphism class is
[projective](foundation.projective-types.md).

## Definitions

### The predicate on cardinals of being projective

```agda
module _
  {l1 : Level} (l2 : Level) (κ : Cardinal l1)
  where

  is-projective-prop-Cardinal : Prop (l1 ⊔ lsuc l2)
  is-projective-prop-Cardinal =
    apply-universal-property-trunc-Set' κ
      ( Prop-Set (l1 ⊔ lsuc l2))
      ( is-projective-prop-Level' l2 ∘ type-Set)

  is-projective-Cardinal : UU (l1 ⊔ lsuc l2)
  is-projective-Cardinal = type-Prop is-projective-prop-Cardinal

  is-prop-is-projective-Cardinal : is-prop is-projective-Cardinal
  is-prop-is-projective-Cardinal =
    is-prop-type-Prop is-projective-prop-Cardinal
```

### Projective cardinalities

```agda
module _
  {l1 : Level} (l2 : Level) (X : Set l1)
  where

  is-projective-prop-cardinality : Prop (l1 ⊔ lsuc l2)
  is-projective-prop-cardinality =
    is-projective-prop-Cardinal l2 (cardinality X)

  is-projective-cardinality : UU (l1 ⊔ lsuc l2)
  is-projective-cardinality = is-projective-Cardinal l2 (cardinality X)

module _
  {l1 l2 : Level} (X : Set l1)
  where

  is-prop-is-projective-cardinality : is-prop (is-projective-cardinality l2 X)
  is-prop-is-projective-cardinality =
    is-prop-is-projective-Cardinal l2 (cardinality X)

  eq-compute-is-projective-prop-cardinality :
    is-projective-prop-cardinality l2 X ＝
    is-projective-prop-Level' l2 (type-Set X)
  eq-compute-is-projective-prop-cardinality =
    triangle-universal-property-trunc-Set
      ( Prop-Set (l1 ⊔ lsuc l2))
      ( is-projective-prop-Level' l2 ∘ type-Set)
      ( X)

  eq-compute-is-projective-cardinality :
    is-projective-cardinality l2 X ＝ is-projective-Level' l2 (type-Set X)
  eq-compute-is-projective-cardinality =
    ap type-Prop eq-compute-is-projective-prop-cardinality

  compute-is-projective-cardinality :
    is-projective-cardinality l2 X ≃ is-projective-Level' l2 (type-Set X)
  compute-is-projective-cardinality =
    equiv-eq eq-compute-is-projective-cardinality

  unit-is-projective-cardinality :
    is-projective-Level' l2 (type-Set X) → is-projective-cardinality l2 X
  unit-is-projective-cardinality =
    map-inv-equiv compute-is-projective-cardinality

  inv-unit-is-projective-cardinality :
    is-projective-cardinality l2 X → is-projective-Level' l2 (type-Set X)
  inv-unit-is-projective-cardinality =
    map-equiv compute-is-projective-cardinality
```

### The universe of projective cardinals

```agda
Projective-Cardinal : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Projective-Cardinal l1 l2 = Σ (Cardinal l1) (is-projective-Cardinal l2)

is-set-Projective-Cardinal :
  {l1 l2 : Level} → is-set (Projective-Cardinal l1 l2)
is-set-Projective-Cardinal {l1} {l2} =
  is-set-type-subtype (is-projective-prop-Cardinal l2) is-set-Cardinal

Projective-Cardinal-Set : (l1 l2 : Level) → Set (lsuc l1 ⊔ lsuc l2)
Projective-Cardinal-Set l1 l2 =
  (Projective-Cardinal l1 l2 , is-set-Projective-Cardinal)

module _
  {l1 l2 : Level} (κ : Projective-Cardinal l1 l2)
  where

  cardinal-Projective-Cardinal : Cardinal l1
  cardinal-Projective-Cardinal = pr1 κ

  is-projective-Projective-Cardinal :
    is-projective-Cardinal l2 cardinal-Projective-Cardinal
  is-projective-Projective-Cardinal = pr2 κ
```
