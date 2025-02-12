# Large apartness relations

```agda
module foundation.large-apartness-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.disjunction
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "large apartness relation" Agda=Large-Apartness-Relation}} on a family of types indexed by universe levels
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
    large-rel-Large-Apartness-Relation : Large-Relation-Prop β A
    antirefl-Large-Apartness-Relation :
      is-antireflexive-Large-Relation-Prop A large-rel-Large-Apartness-Relation
    symmetric-Large-Apartness-Relation :
      is-symmetric-Large-Relation-Prop A large-rel-Large-Apartness-Relation
    cotransitive-Large-Apartness-Relation :
      is-cotransitive-Large-Relation-Prop A large-rel-Large-Apartness-Relation

  consistent-Large-Apartness-Relation :
    {l : Level} →
    (a b : A l) →
    a ＝ b →
    ¬ (type-Prop (large-rel-Large-Apartness-Relation a b))
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
    Large-Apartness-Relation.large-rel-Large-Apartness-Relation
      large-apartness-relation-Type-Family-With-Large-Apartness

open Type-Family-With-Large-Apartness public
```
