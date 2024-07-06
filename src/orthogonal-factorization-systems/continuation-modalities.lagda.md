# The continuation modalities

```agda
module orthogonal-factorization-systems.continuation-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.logical-equivalences
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universal-property-cartesian-product-types
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.transport-along-identifications

open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

Given a [proposition](foundation-core.propositions.md) `R`, the continuation
monad

```text
  A ↦ ((A → R) → R)
```

defines a
[higher modality](orthogonal-factorization-systems.higher-modalities.md).

## Definitions

### The underlying operators of the continuation modalities

```agda
module _
  {l1 l2 : Level} (R : UU l1)
  where

  continuation : (A : UU l2) → UU (l1 ⊔ l2)
  continuation A = ((A → R) → R)

module _
  {l1 : Level} (l : Level) (R : UU l1)
  where

  operator-continuation-modality : operator-modality l (l1 ⊔ l)
  operator-continuation-modality = continuation R

  unit-continuation-modality :
    unit-modality operator-continuation-modality
  unit-continuation-modality = ev

continuation-extend :
  {l1 l2 l3 : Level} {R : UU l1} {A : UU l2} {B : UU l3} →
  (A → continuation R B) → (continuation R A → continuation R B)
continuation-extend f c g = c (λ a → f a g)
```

## Properties

### Continuations into propositions are propositions

```agda
is-prop-continuation :
  {l1 l2 : Level} {R : UU l1} {A : UU l2} →
  is-prop R → is-prop (continuation R A)
is-prop-continuation = is-prop-function-type

is-prop-continuation-Prop :
  {l1 l2 : Level} (R : Prop l1) {A : UU l2} → is-prop (continuation (type-Prop R) A)
is-prop-continuation-Prop R = is-prop-continuation (is-prop-type-Prop R)

continuation-Prop :
  {l1 l2 : Level} (R : Prop l1) (A : UU l2) → Prop (l1 ⊔ l2)
continuation-Prop R A =
  ( continuation (type-Prop R) A , is-prop-continuation (is-prop-type-Prop R))
```

### Continuations into propositions form uniquely eliminating modalities

```agda
is-uniquely-eliminating-modality-continuation-modality :
  {l1 : Level} (l : Level) (R : Prop l1) →
  is-uniquely-eliminating-modality (unit-continuation-modality l (type-Prop R))
is-uniquely-eliminating-modality-continuation-modality l R P =
  is-local-dependent-type-is-prop
    ( unit-continuation-modality l (type-Prop R))
    ( continuation (type-Prop R) ∘ P)
    ( λ _ → is-prop-continuation-Prop R)
    ( λ f c →
      continuation-extend
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
preserves the unit type, so it remains to verify that continuations distribute
over products. Notice that for a general type `R`, there are two canonical
candidates for a map

```text
  continuation R A × continuation R B → continuation R (A × B)
```

either by first computing the continuation on `A` followed by on `B`, or the
other way around. When `R` is a proposition, these agree and we get the
appropriate distributivity law.

```agda
module _
  {l1 l2 l3 : Level} {R : UU l1} {A : UU l2} {B : UU l3}
  where

  map-distributive-product-continuation :
    continuation R (A × B) → continuation R A × continuation R B
  pr1 (map-distributive-product-continuation f) g = f (λ (a , b) → g a)
  pr2 (map-distributive-product-continuation f) g = f (λ (a , b) → g b)

  map-inv-distributive-product-continuation :
    continuation R A × continuation R B → continuation R (A × B)
  map-inv-distributive-product-continuation (fa , fb) g =
    fa (λ a → fb (λ b → g (a , b)))

  map-inv-distributive-product-continuation' :
    continuation R A × continuation R B → continuation R (A × B)
  map-inv-distributive-product-continuation' (fa , fb) g =
    fb (λ b → fa (λ a → g (a , b)))

module _
  {l1 l2 l3 : Level} (R : Prop l1) {A : UU l2} {B : UU l3}
  where

  distributive-product-continuation-modality :
    continuation (type-Prop R) (A × B) ≃
    continuation (type-Prop R) A × continuation (type-Prop R) B
  distributive-product-continuation-modality =
    equiv-iff
      ( continuation-Prop R (A × B))
      ( product-Prop (continuation-Prop R A) (continuation-Prop R B))
      ( map-distributive-product-continuation)
      ( map-inv-distributive-product-continuation)
```

## References

{{#bibliography}}

## External links

- [continuation monad](https://ncatlab.org/nlab/show/continuation+monad) at
  $n$Lab
