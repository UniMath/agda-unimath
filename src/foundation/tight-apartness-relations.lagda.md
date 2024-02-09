# Tight apartness relations

```agda
module foundation.tight-apartness-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositions
```

</details>

## Idea

A [relation](foundation.binary-relations.md) `R` is said to be **tight** if for
every `x y : A` we have `¬ (R x y) → (x ＝ y)`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : A → A → Prop l2)
  where

  is-tight : UU (l1 ⊔ l2)
  is-tight = (x y : A) → ¬ (type-Prop (R x y)) → x ＝ y

  is-tight-apartness-relation : UU (l1 ⊔ l2)
  is-tight-apartness-relation =
    is-apartness-relation R × is-tight

is-tight-Apartness-Relation :
  {l1 l2 : Level} {A : UU l1} (R : Apartness-Relation l2 A) → UU (l1 ⊔ l2)
is-tight-Apartness-Relation R = is-tight (rel-Apartness-Relation R)

Tight-Apartness-Relation :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
Tight-Apartness-Relation l2 A =
  Σ (Apartness-Relation l2 A) (is-tight-Apartness-Relation)

module _
  {l1 l2 : Level} {A : UU l1} (R : Tight-Apartness-Relation l2 A)
  where

  apartness-relation-Tight-Apartness-Relation :
    Apartness-Relation l2 A
  apartness-relation-Tight-Apartness-Relation = pr1 R

  is-tight-apartness-relation-Tight-Apartness-Relation :
    is-tight-Apartness-Relation apartness-relation-Tight-Apartness-Relation
  is-tight-apartness-relation-Tight-Apartness-Relation = pr2 R
```

### Types with tight apartness

```agda
Type-With-Tight-Apartness : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Type-With-Tight-Apartness l1 l2 =
  Σ ( Type-With-Apartness l1 l2)
    ( λ X → is-tight (rel-apart-Type-With-Apartness X))

module _
  {l1 l2 : Level} (X : Type-With-Tight-Apartness l1 l2)
  where

  type-with-apartness-Type-With-Tight-Apartness : Type-With-Apartness l1 l2
  type-with-apartness-Type-With-Tight-Apartness = pr1 X

  type-Type-With-Tight-Apartness : UU l1
  type-Type-With-Tight-Apartness =
    type-Type-With-Apartness type-with-apartness-Type-With-Tight-Apartness

  rel-apart-Type-With-Tight-Apartness :
    Relation-Prop l2 type-Type-With-Tight-Apartness
  rel-apart-Type-With-Tight-Apartness =
    rel-apart-Type-With-Apartness type-with-apartness-Type-With-Tight-Apartness

  apart-Type-With-Tight-Apartness :
    Relation l2 type-Type-With-Tight-Apartness
  apart-Type-With-Tight-Apartness =
    apart-Type-With-Apartness type-with-apartness-Type-With-Tight-Apartness

  is-tight-apart-Type-With-Tight-Apartness :
    is-tight rel-apart-Type-With-Tight-Apartness
  is-tight-apart-Type-With-Tight-Apartness = pr2 X
```

## Properties

### The apartness relation of functions into a type with tight apartness is tight

```agda
is-tight-apartness-function-into-Type-With-Tight-Apartness :
  {l1 l2 l3 : Level} {X : UU l1} (Y : Type-With-Tight-Apartness l2 l3) →
  is-tight
    ( rel-apart-function-into-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness Y))
is-tight-apartness-function-into-Type-With-Tight-Apartness Y f g H =
  eq-htpy
    ( λ x →
      is-tight-apart-Type-With-Tight-Apartness Y
        ( f x)
        ( g x)
        ( λ u → H ( unit-trunc-Prop (x , u))))

exp-Type-With-Tight-Apartness :
  {l1 l2 l3 : Level} (X : UU l1) → Type-With-Tight-Apartness l2 l3 →
  Type-With-Tight-Apartness (l1 ⊔ l2) (l1 ⊔ l3)
pr1 (exp-Type-With-Tight-Apartness X Y) =
  exp-Type-With-Apartness X (type-with-apartness-Type-With-Tight-Apartness Y)
pr2 (exp-Type-With-Tight-Apartness X Y) =
  is-tight-apartness-function-into-Type-With-Tight-Apartness Y
```
