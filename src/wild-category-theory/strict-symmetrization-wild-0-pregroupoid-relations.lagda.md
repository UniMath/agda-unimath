# Strict symmetrization of wild 0-pregroupoid relations

```agda
module wild-category-theory.strict-symmetrization-wild-0-pregroupoid-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.contratransitive-binary-relations
open import foundation.dependent-pair-types
open import foundation.reflexive-relations
open import foundation.strict-symmetrization-binary-relations
open import foundation.transitive-binary-relations
open import foundation.universe-levels
open import foundation.function-types
open import wild-category-theory.wild-0-pregroupoid-relations

open import foundation-core.cartesian-product-types
open import foundation-core.identity-types
open import foundation-core.retractions
```

</details>

## Idea

Given a
[wild 0-pregroupoid relation](wild-category-theory.wild-0-pregroupoids.md) `R`
on `A`, we can construct the
{{#concept "strict symmetrization" Disambiguation="of wild 0-pregroupoid relations" Agda=}}
of `R`. This is another wild 0-pregroupoid structure `Rˢ` on `A` that is
logically equivalent to `R`, but is strictly
[symmetric](foundation.binary-relations.md). I.e., for every `r : R' x y`, we
have a symmetry operation `inv r : R' y x` such that

```text
  inv (inv r) ≐ r.
```

An essential fact about the strict symmetrization of a wild 0-pregroupoid
relation as defined here is that as soon as the relation is univalent, it is
equivalent to its strict symmetrization.

## Definition

### The strict symmetrization construction on wild 0-pregroupoid relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Wild-0-Pregroupoid-Relation l2 A)
  where

  sim-strict-symmetrization-Wild-0-Pregroupoid-Relation : Relation (l1 ⊔ l2) A
  sim-strict-symmetrization-Wild-0-Pregroupoid-Relation =
    strict-symmetrization-Relation (sim-Wild-0-Pregroupoid-Relation R)

  symmetric-strict-symmetrization-Wild-0-Pregroupoid-Relation :
    is-symmetric sim-strict-symmetrization-Wild-0-Pregroupoid-Relation
  symmetric-strict-symmetrization-Wild-0-Pregroupoid-Relation =
    symmetric-strict-symmetrization-Relation (sim-Wild-0-Pregroupoid-Relation R)

  inv-strict-symmetrization-Wild-0-Pregroupoid-Relation :
    {x y : A} →
    sim-strict-symmetrization-Wild-0-Pregroupoid-Relation x y →
    sim-strict-symmetrization-Wild-0-Pregroupoid-Relation y x
  inv-strict-symmetrization-Wild-0-Pregroupoid-Relation {x} {y} =
    symmetric-strict-symmetrization-Wild-0-Pregroupoid-Relation x y

  is-involution-symmetric-strict-symmetrization-Wild-0-Pregroupoid-Relation :
    {x y : A} (p : sim-strict-symmetrization-Wild-0-Pregroupoid-Relation x y) →
    ( symmetric-strict-symmetrization-Wild-0-Pregroupoid-Relation y x
      ( symmetric-strict-symmetrization-Wild-0-Pregroupoid-Relation x y p)) ＝
    ( p)
  is-involution-symmetric-strict-symmetrization-Wild-0-Pregroupoid-Relation p =
    refl

  unit-strict-symmetrization-Wild-0-Pregroupoid-Relation :
    {x y : A} → sim-Wild-0-Pregroupoid-Relation R x y →
    sim-strict-symmetrization-Wild-0-Pregroupoid-Relation x y
  unit-strict-symmetrization-Wild-0-Pregroupoid-Relation =
    unit-strict-symmetrization-Relation
      ( sim-Wild-0-Pregroupoid-Relation R)
      ( reflexive-Wild-0-Pregroupoid-Relation R)

  counit-strict-symmetrization-Wild-0-Pregroupoid-Relation :
    {x y : A} →
    sim-strict-symmetrization-Wild-0-Pregroupoid-Relation x y →
    sim-Wild-0-Pregroupoid-Relation R x y
  counit-strict-symmetrization-Wild-0-Pregroupoid-Relation =
    counit-strict-symmetrization-Relation
       ( sim-Wild-0-Pregroupoid-Relation R)
       ( λ p q →
        comp-Wild-0-Pregroupoid-Relation R
          ( q)
          ( inv-Wild-0-Pregroupoid-Relation R p))

  reflexive-strict-symmetrization-Wild-0-Pregroupoid-Relation :
    is-reflexive sim-strict-symmetrization-Wild-0-Pregroupoid-Relation
  reflexive-strict-symmetrization-Wild-0-Pregroupoid-Relation =
    unit-strict-symmetrization-Wild-0-Pregroupoid-Relation ∘
    reflexive-Wild-0-Pregroupoid-Relation R

  refl-strict-symmetrization-Wild-0-Pregroupoid-Relation :
    {x : A} → sim-strict-symmetrization-Wild-0-Pregroupoid-Relation x x
  refl-strict-symmetrization-Wild-0-Pregroupoid-Relation {x} =
    reflexive-strict-symmetrization-Wild-0-Pregroupoid-Relation x

  comp-strict-symmetrization-Wild-0-Pregroupoid-Relation :
    {x y z : A} →
    sim-strict-symmetrization-Wild-0-Pregroupoid-Relation y z →
    sim-strict-symmetrization-Wild-0-Pregroupoid-Relation x y →
    sim-strict-symmetrization-Wild-0-Pregroupoid-Relation x z
  comp-strict-symmetrization-Wild-0-Pregroupoid-Relation
    ( w , p , q) (w' , p' , q') =
    ( w' ,
      p' ,
      comp-Wild-0-Pregroupoid-Relation R
        ( q)
        ( comp-Wild-0-Pregroupoid-Relation R
          ( inv-Wild-0-Pregroupoid-Relation R p)
          ( q')))

  transitive-strict-symmetrization-Wild-0-Pregroupoid-Relation :
    is-transitive sim-strict-symmetrization-Wild-0-Pregroupoid-Relation
  transitive-strict-symmetrization-Wild-0-Pregroupoid-Relation _ _ _ =
    comp-strict-symmetrization-Wild-0-Pregroupoid-Relation

  is-wild-0-pregroupoid-strict-symmetrization-Wild-0-Pregroupoid-Relation :
    is-wild-0-pregroupoid sim-strict-symmetrization-Wild-0-Pregroupoid-Relation
  is-wild-0-pregroupoid-strict-symmetrization-Wild-0-Pregroupoid-Relation =
    ( reflexive-strict-symmetrization-Wild-0-Pregroupoid-Relation ,
      symmetric-strict-symmetrization-Wild-0-Pregroupoid-Relation ,
      transitive-strict-symmetrization-Wild-0-Pregroupoid-Relation)

  strict-symmetrization-Wild-0-Pregroupoid-Relation :
    Wild-0-Pregroupoid-Relation (l1 ⊔ l2) A
  strict-symmetrization-Wild-0-Pregroupoid-Relation =
    ( sim-strict-symmetrization-Wild-0-Pregroupoid-Relation ,
      is-wild-0-pregroupoid-strict-symmetrization-Wild-0-Pregroupoid-Relation)
```

## See also

- [Strictly involutive identity types](foundation.strictly-involutive-identity-types.md)
