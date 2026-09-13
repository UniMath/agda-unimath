# Apartness relations on dependent function types

```agda
module foundation.dependent-function-types-with-apartness-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.propositional-truncations
open import foundation.tight-apartness-relations
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.propositions
```

</details>

## Idea

Given a family `Y` of types with
[apartness relations](foundation.apartness-relations.md) over `X`, then the
[dependent function type](foundation.dependent-function-types.md) `Π X Y` again
has an apartness relation. Two dependent functions `f` and `g` are **apart** in
`Π X Y` if there [exists](foundation.existential-quantification.md) an `x : X`
such that `f x` is apart from `g x` in `Y x`. If the apartness relations on `Y`
are [tight](foundation.tight-apartness-relations.md) then so is the apartness
relation on `Π X Y`.

## Properties

### Apartness on the type of dependent functions into a family of types with an apartness relation

```agda
module _
  {l1 l2 l3 : Level} (X : UU l1) (Y : X → Type-With-Apartness l2 l3)
  where

  rel-apart-Π-Type-With-Apartness :
    Relation-Prop (l1 ⊔ l3) ((x : X) → type-Type-With-Apartness (Y x))
  rel-apart-Π-Type-With-Apartness f g =
    ∃ X (λ x → rel-apart-Type-With-Apartness (Y x) (f x) (g x))

  apart-Π-Type-With-Apartness :
    Relation (l1 ⊔ l3) ((x : X) → type-Type-With-Apartness (Y x))
  apart-Π-Type-With-Apartness f g =
    type-Prop (rel-apart-Π-Type-With-Apartness f g)

  is-prop-apart-Π-Type-With-Apartness :
    (f g : (x : X) → type-Type-With-Apartness (Y x)) →
    is-prop (apart-Π-Type-With-Apartness f g)
  is-prop-apart-Π-Type-With-Apartness f g =
    is-prop-type-Prop (rel-apart-Π-Type-With-Apartness f g)
```

```agda
module _
  {l1 l2 l3 : Level} (X : UU l1) (Y : X → Type-With-Apartness l2 l3)
  where

  is-antireflexive-apart-Π-Type-With-Apartness :
    is-antireflexive (rel-apart-Π-Type-With-Apartness X Y)
  is-antireflexive-apart-Π-Type-With-Apartness f H =
    apply-universal-property-trunc-Prop H
      ( empty-Prop)
      ( λ (x , a) → antirefl-apart-Type-With-Apartness (Y x) (f x) a)

  is-symmetric-apart-Π-Type-With-Apartness :
    is-symmetric (apart-Π-Type-With-Apartness X Y)
  is-symmetric-apart-Π-Type-With-Apartness f g H =
    apply-universal-property-trunc-Prop H
      ( rel-apart-Π-Type-With-Apartness X Y g f)
      ( λ (x , a) →
        unit-trunc-Prop
          ( x , symmetric-apart-Type-With-Apartness (Y x) (f x) (g x) a))

  abstract
    is-cotransitive-apart-Π-Type-With-Apartness :
      is-cotransitive (rel-apart-Π-Type-With-Apartness X Y)
    is-cotransitive-apart-Π-Type-With-Apartness f g h H =
      apply-universal-property-trunc-Prop H
        ( disjunction-Prop
          ( rel-apart-Π-Type-With-Apartness X Y f g)
          ( rel-apart-Π-Type-With-Apartness X Y g h))
        ( λ (x , a) →
          apply-universal-property-trunc-Prop
            ( cotransitive-apart-Type-With-Apartness (Y x) (f x) (g x) (h x) a)
            ( disjunction-Prop
              ( rel-apart-Π-Type-With-Apartness X Y f g)
              ( rel-apart-Π-Type-With-Apartness X Y g h))
            ( λ where
              ( inl b) → inl-disjunction (intro-exists x b)
              ( inr b) → inr-disjunction (intro-exists x b)))

  is-apartness-relation-apart-Π-Type-With-Apartness :
    is-apartness-relation (rel-apart-Π-Type-With-Apartness X Y)
  is-apartness-relation-apart-Π-Type-With-Apartness =
    is-antireflexive-apart-Π-Type-With-Apartness ,
    is-symmetric-apart-Π-Type-With-Apartness ,
    is-cotransitive-apart-Π-Type-With-Apartness

  apartness-relation-Π-Type-With-Apartness :
    Apartness-Relation (l1 ⊔ l3) ((x : X) → type-Type-With-Apartness (Y x))
  apartness-relation-Π-Type-With-Apartness =
    rel-apart-Π-Type-With-Apartness X Y ,
    is-apartness-relation-apart-Π-Type-With-Apartness

  Π-Type-With-Apartness : Type-With-Apartness (l1 ⊔ l2) (l1 ⊔ l3)
  Π-Type-With-Apartness =
    ((x : X) → type-Type-With-Apartness (Y x)) ,
    rel-apart-Π-Type-With-Apartness X Y ,
    is-antireflexive-apart-Π-Type-With-Apartness ,
    is-symmetric-apart-Π-Type-With-Apartness ,
    is-cotransitive-apart-Π-Type-With-Apartness
```

### Tight apartness on the type of dependent functions into a family of types with tight apartness

```agda
module _
  {l1 l2 l3 : Level} (X : UU l1) (Y : X → Type-With-Tight-Apartness l2 l3)
  where

  rel-apart-Π-Type-With-Tight-Apartness :
    Relation-Prop (l1 ⊔ l3) ((x : X) → type-Type-With-Tight-Apartness (Y x))
  rel-apart-Π-Type-With-Tight-Apartness =
    rel-apart-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  apart-Π-Type-With-Tight-Apartness :
    Relation (l1 ⊔ l3) ((x : X) → type-Type-With-Tight-Apartness (Y x))
  apart-Π-Type-With-Tight-Apartness =
    apart-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  is-prop-apart-Π-Type-With-Tight-Apartness :
    (f g : (x : X) → type-Type-With-Tight-Apartness (Y x)) →
    is-prop (apart-Π-Type-With-Tight-Apartness f g)
  is-prop-apart-Π-Type-With-Tight-Apartness =
    is-prop-apart-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  is-antireflexive-apart-Π-Type-With-Tight-Apartness :
    is-antireflexive rel-apart-Π-Type-With-Tight-Apartness
  is-antireflexive-apart-Π-Type-With-Tight-Apartness =
    is-antireflexive-apart-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  is-symmetric-apart-Π-Type-With-Tight-Apartness :
    is-symmetric apart-Π-Type-With-Tight-Apartness
  is-symmetric-apart-Π-Type-With-Tight-Apartness =
    is-symmetric-apart-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  is-cotransitive-apart-Π-Type-With-Tight-Apartness :
    is-cotransitive rel-apart-Π-Type-With-Tight-Apartness
  is-cotransitive-apart-Π-Type-With-Tight-Apartness =
    is-cotransitive-apart-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  is-apartness-relation-apart-Π-Type-With-Tight-Apartness :
    is-apartness-relation rel-apart-Π-Type-With-Tight-Apartness
  is-apartness-relation-apart-Π-Type-With-Tight-Apartness =
    is-apartness-relation-apart-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  apartness-relation-Π-Type-With-Tight-Apartness :
    Apartness-Relation
      ( l1 ⊔ l3)
      ( (x : X) → type-Type-With-Tight-Apartness (Y x))
  apartness-relation-Π-Type-With-Tight-Apartness =
    apartness-relation-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y)

  is-tight-apart-Π-Type-With-Tight-Apartness :
    is-tight rel-apart-Π-Type-With-Tight-Apartness
  is-tight-apart-Π-Type-With-Tight-Apartness f g H =
    eq-htpy
      ( λ x →
        is-tight-apart-Type-With-Tight-Apartness
          ( Y x)
          ( f x)
          ( g x)
          ( λ u → H (unit-trunc-Prop (x , u))))

  tight-apartness-relation-Π-Type-With-Tight-Apartness :
    Tight-Apartness-Relation (l1 ⊔ l3)
      ( (x : X) → type-Type-With-Tight-Apartness (Y x))
  tight-apartness-relation-Π-Type-With-Tight-Apartness =
    apartness-relation-Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y) ,
    is-tight-apart-Π-Type-With-Tight-Apartness

  Π-Type-With-Tight-Apartness : Type-With-Tight-Apartness (l1 ⊔ l2) (l1 ⊔ l3)
  Π-Type-With-Tight-Apartness =
    Π-Type-With-Apartness X
      ( type-with-apartness-Type-With-Tight-Apartness ∘ Y) ,
    is-tight-apart-Π-Type-With-Tight-Apartness
```

## See also

- [Function types with apartness relations](foundation.function-types-with-apartness-relations.md)
