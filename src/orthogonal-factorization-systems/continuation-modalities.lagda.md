# Continuation modalities

```agda
module orthogonal-factorization-systems.continuation-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.continuations
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.unit-type
open import foundation.universal-property-cartesian-product-types
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import orthogonal-factorization-systems.large-lawvere-tierney-topologies
open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

Given a [proposition](foundation-core.propositions.md) `R`, the
[continuations](foundation.continuations.md) on `R`

```text
  A ↦ ((A → R) → R)
```

defines a
[higher modality](orthogonal-factorization-systems.higher-modalities.md).

## Definitions

### The underlying operators of continuation modalities

```agda
module _
  {l1 : Level} (l2 : Level) (R : Prop l1)
  where

  operator-continuation-modality : operator-modality l2 (l1 ⊔ l2)
  operator-continuation-modality = continuation (type-Prop R)

  unit-continuation-modality :
    unit-modality operator-continuation-modality
  unit-continuation-modality = unit-continuation
```

## Properties

### Continuations on propositions form uniquely eliminating modalities

```agda
is-uniquely-eliminating-modality-continuation-modality :
  {l1 : Level} (l : Level) (R : Prop l1) →
  is-uniquely-eliminating-modality (unit-continuation-modality l R)
is-uniquely-eliminating-modality-continuation-modality l R P =
  is-local-dependent-type-is-prop
    ( unit-continuation-modality l R)
    ( continuation (type-Prop R) ∘ P)
    ( λ _ → is-prop-continuation-Prop R)
    ( λ f c →
      extend-continuation
        ( λ a →
          tr
            ( continuation (type-Prop R) ∘ P)
            ( eq-is-prop (is-prop-continuation-Prop R))
            ( f a))
        ( c))
```

This proof is a generalization of Example 1.9 in {{#cite RSS20}}, where the
special case when `R` is the [empty type](foundation-core.empty-types.md) is
considered.

### Continuations on propositions define Lawvere–Tierney topologies

Every operator taking values in propositions that has a unit map trivially
preserves the unit type.

```agda
preserves-unit-continuation-modality' :
  {l1 : Level} {R : UU l1} → continuation R unit ↔ unit
preserves-unit-continuation-modality' {R = R} =
  ( terminal-map (continuation R unit) , unit-continuation)

preserves-unit-continuation-modality :
  {l1 : Level} (R : Prop l1) → continuation (type-Prop R) unit ≃ unit
preserves-unit-continuation-modality R =
  equiv-iff'
    ( continuation-Prop R unit)
    ( unit-Prop)
    ( preserves-unit-continuation-modality')
```

We must verify that continuations distribute over products. Notice that for a
general type `R`, there are two canonical candidates for a map

```text
  continuation R A × continuation R B → continuation R (A × B)
```

either by first computing the continuation at `A` and then computing the
continuation at `B`, or the other way around. When `R` is a proposition, these
agree and we get the appropriate distributivity law.

```agda
module _
  {l1 l2 l3 : Level} {R : UU l1} {A : UU l2} {B : UU l3}
  where

  map-distributive-product-continuation :
    continuation R (A × B) → continuation R A × continuation R B
  pr1 (map-distributive-product-continuation f) g = f (λ (a , b) → g a)
  pr2 (map-distributive-product-continuation f) g = f (λ (a , b) → g b)

  map-inv-distributive-product-left-first-continuation :
    continuation R A × continuation R B → continuation R (A × B)
  map-inv-distributive-product-left-first-continuation (fa , fb) g =
    fb (λ b → fa (λ a → g (a , b)))

  map-inv-distributive-product-right-first-continuation :
    continuation R A × continuation R B → continuation R (A × B)
  map-inv-distributive-product-right-first-continuation (fa , fb) g =
    fa (λ a → fb (λ b → g (a , b)))

  distributive-product-continuation-modality' :
    continuation R (A × B) ↔ continuation R A × continuation R B
  distributive-product-continuation-modality' =
    ( map-distributive-product-continuation ,
      map-inv-distributive-product-left-first-continuation)

module _
  {l1 l2 l3 : Level} (R : Prop l1) {A : UU l2} {B : UU l3}
  where

  distributive-product-continuation-modality :
    continuation (type-Prop R) (A × B) ≃
    continuation (type-Prop R) A × continuation (type-Prop R) B
  distributive-product-continuation-modality =
    equiv-iff'
      ( continuation-Prop R (A × B))
      ( product-Prop (continuation-Prop R A) (continuation-Prop R B))
      ( distributive-product-continuation-modality')
```

```agda
module _
  {l : Level} (R : Prop l)
  where

  is-large-lawvere-tierney-topology-continuation :
    is-large-lawvere-tierney-topology (continuation-Prop R ∘ type-Prop)
  is-large-lawvere-tierney-topology-continuation =
    λ where
    .is-idempotent-is-large-lawvere-tierney-topology P →
      ( mul-continuation , unit-continuation)
    .preserves-unit-is-large-lawvere-tierney-topology →
      preserves-unit-continuation-modality'
    .preserves-conjunction-is-large-lawvere-tierney-topology P Q →
      distributive-product-continuation-modality'

  continuation-large-lawvere-tierney-topology :
    large-lawvere-tierney-topology (l ⊔_)
  continuation-large-lawvere-tierney-topology =
    λ where
    .operator-large-lawvere-tierney-topology →
      continuation-Prop R ∘ type-Prop
    .is-large-lawvere-tierney-topology-large-lawvere-tierney-topology →
      is-large-lawvere-tierney-topology-continuation
```

### `A → R` is `continuation R`-stable

```agda
is-continuation-stable-exp :
  {l1 l2 : Level} (R : Prop l1) {A : UU l2} →
  is-modal (unit-continuation-modality (l1 ⊔ l2) R) (A → type-Prop R)
is-continuation-stable-exp R {A} =
  is-equiv-has-converse
    ( function-Prop A R)
    ( continuation-Prop R (A → type-Prop R))
    ( _∘ unit-continuation)
```

## References

{{#bibliography}}

## External links

- [continuation monad](https://ncatlab.org/nlab/show/continuation+monad) at
  $n$Lab
