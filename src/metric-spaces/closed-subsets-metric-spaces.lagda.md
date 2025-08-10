# Closed subsets of metric spaces

```agda
module metric-spaces.closed-subsets-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.complements-subtypes
open import foundation.dependent-pair-types
open import foundation.dependent-products-subtypes
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.intersections-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.closure-subsets-metric-spaces
open import metric-spaces.dense-subsets-metric-spaces
open import metric-spaces.dependent-products-metric-spaces
open import metric-spaces.discrete-metric-spaces
open import metric-spaces.located-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.open-subsets-metric-spaces
open import metric-spaces.subspaces-metric-spaces
```

</details>

## Idea

A [subset](foundation.subtypes.md) `S` of a
[metric space](metric-spaces.metric-spaces.md) `X` is
{{#concept "closed" disambiguation="subset of a metric space" WDID=Q320357 WD="closed set" Agda=is-closed-subset-Metric-Space}}
if its [closure](metric-spaces.closure-subsets-metric-spaces.md) is a subset of
`S`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2) (S : subset-Metric-Space l3 X)
  where

  is-closed-prop-subset-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-closed-prop-subset-Metric-Space =
    leq-prop-subtype (closure-subset-Metric-Space X S) S

  is-closed-subset-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-closed-subset-Metric-Space = type-Prop is-closed-prop-subset-Metric-Space

closed-subset-Metric-Space :
  {l1 l2 : Level} (l3 : Level) (X : Metric-Space l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l3)
closed-subset-Metric-Space l3 X =
  type-subtype (is-closed-prop-subset-Metric-Space {l3 = l3} X)

module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2)
  (S : closed-subset-Metric-Space l3 X)
  where

  subset-closed-subset-Metric-Space : subset-Metric-Space l3 X
  subset-closed-subset-Metric-Space = pr1 S

  is-closed-subset-closed-subset-Metric-Space :
    is-closed-subset-Metric-Space X subset-closed-subset-Metric-Space
  is-closed-subset-closed-subset-Metric-Space = pr2 S
```

### Closed subsets of located metric spaces

```agda
module _
  {l1 l2 l3 : Level}
  (X : Located-Metric-Space l1 l2) (S : subset-Located-Metric-Space l3 X)
  where

  is-closed-prop-subset-Located-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-closed-prop-subset-Located-Metric-Space =
    is-closed-prop-subset-Metric-Space
      ( metric-space-Located-Metric-Space X)
      ( S)

  is-closed-subset-Located-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-closed-subset-Located-Metric-Space =
    type-Prop is-closed-prop-subset-Located-Metric-Space

closed-subset-Located-Metric-Space :
  {l1 l2 : Level} (l3 : Level)
  (X : Located-Metric-Space l1 l2) → UU (l1 ⊔ l2 ⊔ lsuc l3)
closed-subset-Located-Metric-Space l3 X =
  closed-subset-Metric-Space l3 (metric-space-Located-Metric-Space X)
```

## Properties

### If a set is closed, its closure has the same elements as itself

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  has-same-elements-closure-closed-subset-Metric-Space :
    {l3 : Level} (S : closed-subset-Metric-Space l3 X) →
    has-same-elements-subtype
      ( subset-closed-subset-Metric-Space X S)
      ( closure-subset-Metric-Space X (subset-closed-subset-Metric-Space X S))
  pr1 (has-same-elements-closure-closed-subset-Metric-Space (S , closed-S) x) =
    is-subset-closure-subset-Metric-Space X S x
  pr2 (has-same-elements-closure-closed-subset-Metric-Space (S , closed-S) x) =
    closed-S x
```

### The empty set is closed

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  is-closed-empty-subset-Metric-Space :
    is-closed-subset-Metric-Space X (empty-subset-Metric-Space X)
  is-closed-empty-subset-Metric-Space x x∈closure =
    map-raise (is-empty-closure-empty-subset-Metric-Space X x x∈closure)
```

### A metric space is closed in itself

```agda
  is-closed-full-subset-Metric-Space :
    is-closed-subset-Metric-Space X (full-subset-Metric-Space X)
  is-closed-full-subset-Metric-Space x _ = map-raise star
```

### Every subset of a discrete metric space is closed

```agda
module _
  {l1 l2 l3 : Level} (X : Discrete-Metric-Space l1 l2)
  where

  is-closed-subset-Discrete-Metric-Space :
    (S : subtype l3 (type-Discrete-Metric-Space X)) →
    is-closed-subset-Metric-Space
      ( metric-space-Discrete-Metric-Space X)
      ( S)
  is-closed-subset-Discrete-Metric-Space S x x∈closure =
    let open do-syntax-trunc-Prop (S x)
    in do
      (y , y∈N1x , y∈S) ← x∈closure one-ℚ⁺
      inv-tr
        ( type-Prop ∘ S)
        ( is-discrete-metric-space-Discrete-Metric-Space X one-ℚ⁺ x y y∈N1x)
        ( y∈S)
```

### The intersection of a family of closed subsets is closed

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2)
  {I : UU l3} (F : I → closed-subset-Metric-Space l4 X)
  where

  subset-intersection-family-closed-subset-Metric-Space :
    subset-Metric-Space (l3 ⊔ l4) X
  subset-intersection-family-closed-subset-Metric-Space =
    intersection-family-of-subtypes
      ( λ i → subset-closed-subset-Metric-Space X (F i))

  abstract
    is-closed-subset-intersection-family-closed-subset-Metric-Space :
      is-closed-subset-Metric-Space
        ( X)
        ( subset-intersection-family-closed-subset-Metric-Space)
    is-closed-subset-intersection-family-closed-subset-Metric-Space x x∈cl i =
      is-closed-subset-closed-subset-Metric-Space X (F i) x
        ( λ ε → map-tot-exists (λ _ (y∈Nεx , y∈F) → (y∈Nεx , y∈F i)) (x∈cl ε))

  intersection-family-closed-subset-Metric-Space :
    closed-subset-Metric-Space (l3 ⊔ l4) X
  intersection-family-closed-subset-Metric-Space =
    ( subset-intersection-family-closed-subset-Metric-Space ,
      is-closed-subset-intersection-family-closed-subset-Metric-Space)
```

### If the union of two closed sets is always closed, then LLPO

This has yet to be formalized.

### In a metric space, the complement of an open metric space is closed

```agda
module _
  {l1 l2 l3 : Level} (X : Metric-Space l1 l2)
  (S : open-subset-Metric-Space l3 X)
  where

  subset-complement-open-subset-Metric-Space :
    subset-Metric-Space l3 X
  subset-complement-open-subset-Metric-Space =
    complement-subtype (subset-open-subset-Metric-Space X S)

  is-closed-subset-complement-open-subset-Metric-Space :
    is-closed-subset-Metric-Space
      ( X)
      ( subset-complement-open-subset-Metric-Space)
  is-closed-subset-complement-open-subset-Metric-Space x x∈cl-¬S x∈S =
    let open do-syntax-trunc-Prop empty-Prop
    in do
      (ε , Nεx⊆S) ← is-open-subset-open-subset-Metric-Space X S x x∈S
      (y , y∈Nεx , y∈¬S) ← x∈cl-¬S ε
      y∈¬S (Nεx⊆S y y∈Nεx)
```

To prove: the converse implies a constructive taboo.

### The dependent product of closed subsets is closed in the product metric space

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} (X : I → Metric-Space l2 l3)
  (C : (i : I) → closed-subset-Metric-Space l4 (X i))
  where

  subset-Π-closed-subset-Metric-Space :
    subset-Metric-Space (l1 ⊔ l4) (Π-Metric-Space I X)
  subset-Π-closed-subset-Metric-Space =
    Π-subtype (λ i → subset-closed-subset-Metric-Space (X i) (C i))

  is-closed-subset-Π-closed-subset-Metric-Space :
    is-closed-subset-Metric-Space
      ( Π-Metric-Space I X)
      ( subset-Π-closed-subset-Metric-Space)
  is-closed-subset-Π-closed-subset-Metric-Space f f∈ΠC i =
    is-closed-subset-closed-subset-Metric-Space
      ( X i)
      ( C i)
      ( f i)
      ( λ ε →
        rec-trunc-Prop
          ( trunc-Prop
            ( type-subtype
              ( intersection-subtype
                ( neighborhood-prop-Metric-Space (X i) ε (f i))
                ( subset-closed-subset-Metric-Space (X i) (C i)))))
          ( λ ( g , g∈Nεf , k) → unit-trunc-Prop (g i , g∈Nεf i , k i))
          ( f∈ΠC ε))
```
