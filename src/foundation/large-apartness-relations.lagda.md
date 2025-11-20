# Large apartness relations

```agda
module foundation.large-apartness-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "large apartness relation" WD="apartness relation" WDID=Q4779193 Agda=Large-Apartness-Relation}}
on a family of types indexed by [universe levels](foundation.universe-levels.md)
`A` is a [large binary relation](foundation.large-binary-relations.md) `R` which
is

- **Antireflexive:** For any `a : A` we have `¬ (R a a)`
- **Symmetric:** For any `a b : A` we have `R a b → R b a`
- **Cotransitive:** For any `a b c : A` we have `R a b → R a c ∨ R b c`.

This is analogous to the notion of small
[apartness relations](foundation.apartness-relations.md).

## Definitions

```agda
record Large-Apartness-Relation
  {α : Level → Level} (β : Level → Level → Level)
  (A : (l : Level) → UU (α l)) : UUω
  where

  field
    apart-prop-Large-Apartness-Relation : Large-Relation-Prop β A
    antirefl-Large-Apartness-Relation :
      is-antireflexive-Large-Relation-Prop A apart-prop-Large-Apartness-Relation
    symmetric-Large-Apartness-Relation :
      is-symmetric-Large-Relation-Prop A apart-prop-Large-Apartness-Relation
    cotransitive-Large-Apartness-Relation :
      is-cotransitive-Large-Relation-Prop A apart-prop-Large-Apartness-Relation

  apart-Large-Apartness-Relation : Large-Relation β A
  apart-Large-Apartness-Relation a b =
    type-Prop (apart-prop-Large-Apartness-Relation a b)

  consistent-Large-Apartness-Relation :
    {l : Level} →
    (a b : A l) →
    a ＝ b → ¬ (apart-Large-Apartness-Relation a b)
  consistent-Large-Apartness-Relation a .a refl =
    antirefl-Large-Apartness-Relation a

open Large-Apartness-Relation public
```

### Type families equipped with large apartness relations

```agda
record Type-Family-With-Large-Apartness
  (α : Level → Level) (β : Level → Level → Level) : UUω
  where

  field
    type-family-Type-Family-With-Large-Apartness : (l : Level) → UU (α l)
    large-apartness-relation-Type-Family-With-Large-Apartness :
      Large-Apartness-Relation β type-family-Type-Family-With-Large-Apartness

  large-rel-Type-Family-With-Large-Apartness :
    Large-Relation-Prop β type-family-Type-Family-With-Large-Apartness
  large-rel-Type-Family-With-Large-Apartness =
    Large-Apartness-Relation.apart-prop-Large-Apartness-Relation
      large-apartness-relation-Type-Family-With-Large-Apartness

open Type-Family-With-Large-Apartness public
```

## Properties

### If two elements are apart, then they are nonequal

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)} (R : Large-Apartness-Relation β A)
  where

  nonequal-apart-Large-Apartness-Relation :
    {l : Level} {a b : A l} → apart-Large-Apartness-Relation R a b → a ≠ b
  nonequal-apart-Large-Apartness-Relation {a = a} p refl =
    antirefl-Large-Apartness-Relation R a p
```

### Small apartness relations from large apartness relations

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {A : (l : Level) → UU (α l)} (R : Large-Apartness-Relation β A)
  where

  apartness-relation-Large-Apartness-Relation :
    (l : Level) → Apartness-Relation (β l l) (A l)
  apartness-relation-Large-Apartness-Relation l =
    ( apart-prop-Large-Apartness-Relation R ,
      antirefl-Large-Apartness-Relation R ,
      symmetric-Large-Apartness-Relation R ,
      λ a b c a#b →
        map-disjunction
          ( id)
          ( symmetric-Large-Apartness-Relation R c b)
          ( cotransitive-Large-Apartness-Relation R a b c a#b))
```
