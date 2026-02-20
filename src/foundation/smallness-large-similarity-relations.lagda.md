# Smallness relative to large similarity relations

```agda
module foundation.smallness-large-similarity-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-similarity-relations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given a [large similarity relation](foundation.large-similarity-relations.md)
`R` on a universe-polymorphic type family `X`, a value `x : X l0` is
{{#concept "small" Disambiguation="relative to a large similarity relation" Agda=is-small-Large-Similarity-Relation}}
relative to a universe level `l` if it is similar to a value in `X l`.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {X : (l : Level) → UU (α l)}
  (R : Large-Similarity-Relation β X)
  where

  is-small-Large-Similarity-Relation :
    {l0 : Level} (l : Level) → X l0 → UU (α l ⊔ β l0 l)
  is-small-Large-Similarity-Relation l x =
    Σ (X l) (sim-Large-Similarity-Relation R x)
```

## Properties

### Being small relative to a universe level is a proposition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {X : (l : Level) → UU (α l)}
  (R : Large-Similarity-Relation β X)
  {l0 : Level}
  (l : Level)
  (x : X l0)
  where

  abstract
    all-elements-equal-is-small-Large-Similarity-Relation :
      all-elements-equal (is-small-Large-Similarity-Relation R l x)
    all-elements-equal-is-small-Large-Similarity-Relation (y , Rxy) (z , Rxz) =
      eq-type-subtype
        ( sim-prop-Large-Similarity-Relation R x)
        ( eq-sim-Large-Similarity-Relation R y z
          ( transitive-sim-Large-Similarity-Relation R y x z
            ( Rxz)
            ( symmetric-sim-Large-Similarity-Relation R x y Rxy)))

    is-prop-is-small-Large-Similarity-Relation :
      is-prop (is-small-Large-Similarity-Relation R l x)
    is-prop-is-small-Large-Similarity-Relation =
      is-prop-all-elements-equal
        ( all-elements-equal-is-small-Large-Similarity-Relation)

  is-small-prop-Large-Similarity-Relation : Prop (α l ⊔ β l0 l)
  is-small-prop-Large-Similarity-Relation =
    ( is-small-Large-Similarity-Relation R l x ,
      is-prop-is-small-Large-Similarity-Relation)
```

## Properties

### A value is small relative to its own universe level

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {X : (l : Level) → UU (α l)}
  (R : Large-Similarity-Relation β X)
  where

  is-small-level-Large-Similarity-Relation :
    {l : Level} (x : X l) →
    is-small-Large-Similarity-Relation R l x
  is-small-level-Large-Similarity-Relation x =
    ( x , refl-sim-Large-Similarity-Relation R x)
```

## See also

- [Smallness in cumulative large sets](foundation.smallness-cumulative-large-sets.md)
