# Binary relations on tuples

```agda
module lists.binary-relations-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import lists.tuples
```

</details>

## Idea

Any [binary relation](foundation.binary-relations.md) `R` on a type `A` induces
a corresponding relation on the type of `n`-[tuples](lists.tuples.md) in `A`.

## Definition

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : Relation l2 A)
  where

  rel-tuple-Relation : (n : ℕ) → Relation l2 (tuple A n)
  rel-tuple-Relation 0 empty-tuple empty-tuple = raise-unit l2
  rel-tuple-Relation (succ-ℕ n) (x ∷ xs) (y ∷ ys) =
    R x y × rel-tuple-Relation n xs ys

module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : Relation-Prop l2 A)
  where

  rel-tuple-Relation-Prop : (n : ℕ) → Relation l2 (tuple A n)
  rel-tuple-Relation-Prop n =
    rel-tuple-Relation (type-Relation-Prop R) n

  abstract
    is-prop-rel-tuple-Relation-Prop :
      (n : ℕ) (x y : tuple A n) → is-prop (rel-tuple-Relation-Prop n x y)
    is-prop-rel-tuple-Relation-Prop 0 empty-tuple empty-tuple =
      is-prop-raise-unit
    is-prop-rel-tuple-Relation-Prop (succ-ℕ n) (x ∷ xs) (y ∷ ys) =
      is-prop-product
        ( is-prop-type-Prop (R x y))
        ( is-prop-rel-tuple-Relation-Prop n xs ys)

  prop-tuple-Relation-Prop : (n : ℕ) → Relation-Prop l2 (tuple A n)
  prop-tuple-Relation-Prop n x y =
    ( rel-tuple-Relation-Prop n x y , is-prop-rel-tuple-Relation-Prop n x y)
```

## Properties

### Reflexivity of the induced relation on tuples

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : Relation l2 A)
  where

  refl-rel-tuple-Relation :
    is-reflexive R → (n : ℕ) → is-reflexive (rel-tuple-Relation R n)
  refl-rel-tuple-Relation refl-R 0 empty-tuple = map-raise star
  refl-rel-tuple-Relation refl-R (succ-ℕ n) (x ∷ xs) =
    ( refl-R x , refl-rel-tuple-Relation refl-R n xs)
```

### Symmetry of the induced relation on tuples

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : Relation l2 A)
  where

  symmetric-rel-tuple-Relation :
    is-symmetric R → (n : ℕ) → is-symmetric (rel-tuple-Relation R n)
  symmetric-rel-tuple-Relation sym-R 0 empty-tuple empty-tuple 0~0 =
    map-raise star
  symmetric-rel-tuple-Relation
    sym-R (succ-ℕ n) (x ∷ xs) (y ∷ ys) (x~y , xs~ys) =
    ( sym-R x y x~y , symmetric-rel-tuple-Relation sym-R n xs ys xs~ys)
```

### Transitivity of the induced relation on tuples

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  (R : Relation l2 A)
  where

  transitive-rel-tuple-Relation :
    is-transitive R → (n : ℕ) → is-transitive (rel-tuple-Relation R n)
  transitive-rel-tuple-Relation
    trans-R 0 empty-tuple empty-tuple empty-tuple _ _ =
    map-raise star
  transitive-rel-tuple-Relation
    trans-R (succ-ℕ n) (x ∷ xs) (y ∷ ys) (z ∷ zs) (y~z , ys~zs) (x~y , xs~ys) =
    ( trans-R x y z y~z x~y ,
      transitive-rel-tuple-Relation trans-R n xs ys zs ys~zs xs~ys)
```
