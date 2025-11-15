# Finite abelian groups

```agda
module finite-group-theory.finite-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import finite-group-theory.finite-groups

open import foundation.equivalences
open import foundation.identity-types
open import foundation.interchange-law
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.conjugation
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

{{#concept "Finite abelian groups" WD="finite abelian group" WDID=Q3117606 Agda=Finite-Ab}}
are [abelian groups](group-theory.abelian-groups.md) whose carrier type is
[finite](univalent-combinatorics.finite-types.md).

## Definition

### The condition of being an abelian group

```agda
is-abelian-prop-Finite-Group : {l : Level} → Finite-Group l → Prop l
is-abelian-prop-Finite-Group G = is-abelian-prop-Group (group-Finite-Group G)

is-abelian-Finite-Group : {l : Level} → Finite-Group l → UU l
is-abelian-Finite-Group G = type-Prop (is-abelian-prop-Finite-Group G)

is-prop-is-abelian-Finite-Group :
  {l : Level} (G : Finite-Group l) → is-prop (is-abelian-Finite-Group G)
is-prop-is-abelian-Finite-Group G =
  is-prop-type-Prop (is-abelian-prop-Finite-Group G)
```

### The type of abelian groups

```agda
Finite-Ab : (l : Level) → UU (lsuc l)
Finite-Ab l = Σ (Finite-Group l) is-abelian-Finite-Group

finite-abelian-group-is-finite-Ab :
  {l : Level} → (A : Ab l) → is-finite (type-Ab A) → Finite-Ab l
pr1 (finite-abelian-group-is-finite-Ab A f) =
  finite-group-is-finite-Group (group-Ab A) f
pr2 (finite-abelian-group-is-finite-Ab A f) = pr2 A

module _
  {l : Level} (A : Finite-Ab l)
  where

  finite-group-Finite-Ab : Finite-Group l
  finite-group-Finite-Ab = pr1 A

  group-Finite-Ab : Group l
  group-Finite-Ab = group-Finite-Group finite-group-Finite-Ab

  finite-type-Finite-Ab : Finite-Type l
  finite-type-Finite-Ab = finite-type-Finite-Group finite-group-Finite-Ab

  type-Finite-Ab : UU l
  type-Finite-Ab = type-Finite-Group finite-group-Finite-Ab

  is-finite-type-Finite-Ab : is-finite type-Finite-Ab
  is-finite-type-Finite-Ab = is-finite-type-Finite-Group finite-group-Finite-Ab

  set-Finite-Ab : Set l
  set-Finite-Ab = set-Group group-Finite-Ab

  is-set-type-Finite-Ab : is-set type-Finite-Ab
  is-set-type-Finite-Ab = is-set-type-Group group-Finite-Ab

  has-associative-add-Finite-Ab : has-associative-mul-Set set-Finite-Ab
  has-associative-add-Finite-Ab = has-associative-mul-Group group-Finite-Ab

  add-Finite-Ab : type-Finite-Ab → type-Finite-Ab → type-Finite-Ab
  add-Finite-Ab = mul-Group group-Finite-Ab

  add-Finite-Ab' : type-Finite-Ab → type-Finite-Ab → type-Finite-Ab
  add-Finite-Ab' = mul-Group' group-Finite-Ab

  commutative-add-Finite-Ab :
    (x y : type-Finite-Ab) → add-Finite-Ab x y ＝ add-Finite-Ab y x
  commutative-add-Finite-Ab = pr2 A

  ab-Finite-Ab : Ab l
  pr1 ab-Finite-Ab = group-Finite-Ab
  pr2 ab-Finite-Ab = commutative-add-Finite-Ab

  ap-add-Finite-Ab :
    {x y x' y' : type-Finite-Ab} →
    x ＝ x' → y ＝ y' → add-Finite-Ab x y ＝ add-Finite-Ab x' y'
  ap-add-Finite-Ab = ap-add-Ab ab-Finite-Ab

  associative-add-Finite-Ab :
    (x y z : type-Finite-Ab) →
    add-Finite-Ab (add-Finite-Ab x y) z ＝ add-Finite-Ab x (add-Finite-Ab y z)
  associative-add-Finite-Ab = associative-mul-Group group-Finite-Ab

  semigroup-Finite-Ab : Semigroup l
  semigroup-Finite-Ab = semigroup-Group group-Finite-Ab

  is-group-Finite-Ab : is-group-Semigroup semigroup-Finite-Ab
  is-group-Finite-Ab = is-group-Group group-Finite-Ab

  has-zero-Finite-Ab : is-unital-Semigroup semigroup-Finite-Ab
  has-zero-Finite-Ab = is-unital-Group group-Finite-Ab

  zero-Finite-Ab : type-Finite-Ab
  zero-Finite-Ab = unit-Group group-Finite-Ab

  is-zero-Finite-Ab : type-Finite-Ab → UU l
  is-zero-Finite-Ab = is-unit-Group group-Finite-Ab

  is-prop-is-zero-Finite-Ab :
    (x : type-Finite-Ab) → is-prop (is-zero-Finite-Ab x)
  is-prop-is-zero-Finite-Ab = is-prop-is-unit-Group group-Finite-Ab

  is-zero-prop-Finite-Ab : type-Finite-Ab → Prop l
  is-zero-prop-Finite-Ab = is-unit-prop-Group group-Finite-Ab

  left-unit-law-add-Finite-Ab :
    (x : type-Finite-Ab) → add-Finite-Ab zero-Finite-Ab x ＝ x
  left-unit-law-add-Finite-Ab = left-unit-law-mul-Group group-Finite-Ab

  right-unit-law-add-Finite-Ab :
    (x : type-Finite-Ab) → add-Finite-Ab x zero-Finite-Ab ＝ x
  right-unit-law-add-Finite-Ab = right-unit-law-mul-Group group-Finite-Ab

  has-negatives-Finite-Ab :
    is-group-is-unital-Semigroup semigroup-Finite-Ab has-zero-Finite-Ab
  has-negatives-Finite-Ab = has-inverses-Group group-Finite-Ab

  neg-Finite-Ab : type-Finite-Ab → type-Finite-Ab
  neg-Finite-Ab = inv-Group group-Finite-Ab

  left-inverse-law-add-Finite-Ab :
    (x : type-Finite-Ab) → add-Finite-Ab (neg-Finite-Ab x) x ＝ zero-Finite-Ab
  left-inverse-law-add-Finite-Ab = left-inverse-law-mul-Group group-Finite-Ab

  right-inverse-law-add-Finite-Ab :
    (x : type-Finite-Ab) → add-Finite-Ab x (neg-Finite-Ab x) ＝ zero-Finite-Ab
  right-inverse-law-add-Finite-Ab = right-inverse-law-mul-Group group-Finite-Ab

  interchange-add-add-Finite-Ab :
    (a b c d : type-Finite-Ab) →
    add-Finite-Ab (add-Finite-Ab a b) (add-Finite-Ab c d) ＝
    add-Finite-Ab (add-Finite-Ab a c) (add-Finite-Ab b d)
  interchange-add-add-Finite-Ab =
    interchange-law-commutative-and-associative
      add-Finite-Ab
      commutative-add-Finite-Ab
      associative-add-Finite-Ab

  right-swap-add-Finite-Ab :
    (a b c : type-Finite-Ab) →
    add-Finite-Ab (add-Finite-Ab a b) c ＝ add-Finite-Ab (add-Finite-Ab a c) b
  right-swap-add-Finite-Ab = right-swap-add-Ab ab-Finite-Ab

  left-swap-add-Finite-Ab :
    (a b c : type-Finite-Ab) →
    add-Finite-Ab a (add-Finite-Ab b c) ＝ add-Finite-Ab b (add-Finite-Ab a c)
  left-swap-add-Finite-Ab = left-swap-add-Ab ab-Finite-Ab

  distributive-neg-add-Finite-Ab :
    (x y : type-Finite-Ab) →
    neg-Finite-Ab (add-Finite-Ab x y) ＝
    add-Finite-Ab (neg-Finite-Ab x) (neg-Finite-Ab y)
  distributive-neg-add-Finite-Ab = distributive-neg-add-Ab ab-Finite-Ab

  neg-neg-Finite-Ab :
    (x : type-Finite-Ab) → neg-Finite-Ab (neg-Finite-Ab x) ＝ x
  neg-neg-Finite-Ab = neg-neg-Ab ab-Finite-Ab

  neg-zero-Finite-Ab : neg-Finite-Ab zero-Finite-Ab ＝ zero-Finite-Ab
  neg-zero-Finite-Ab = neg-zero-Ab ab-Finite-Ab
```

### Conjugation in an abelian group

```agda
module _
  {l : Level} (A : Finite-Ab l)
  where

  equiv-conjugation-Finite-Ab :
    (x : type-Finite-Ab A) → type-Finite-Ab A ≃ type-Finite-Ab A
  equiv-conjugation-Finite-Ab = equiv-conjugation-Group (group-Finite-Ab A)

  conjugation-Finite-Ab :
    (x : type-Finite-Ab A) → type-Finite-Ab A → type-Finite-Ab A
  conjugation-Finite-Ab = conjugation-Group (group-Finite-Ab A)

  equiv-conjugation-Finite-Ab' :
    (x : type-Finite-Ab A) → type-Finite-Ab A ≃ type-Finite-Ab A
  equiv-conjugation-Finite-Ab' = equiv-conjugation-Group' (group-Finite-Ab A)

  conjugation-Finite-Ab' :
    (x : type-Finite-Ab A) → type-Finite-Ab A → type-Finite-Ab A
  conjugation-Finite-Ab' = conjugation-Group' (group-Finite-Ab A)
```

## Properties

### There is a finite number of ways to equip a finite type with the structure of an abelian group

```agda
module _
  {l : Level}
  (X : Finite-Type l)
  where

  structure-abelian-group-Finite-Type : UU l
  structure-abelian-group-Finite-Type =
    Σ ( structure-group-Finite-Type X)
      ( λ g →
        is-abelian-Finite-Group (finite-group-structure-group-Finite-Type X g))

  finite-abelian-group-structure-abelian-group-Finite-Type :
    structure-abelian-group-Finite-Type → Finite-Ab l
  pr1 (finite-abelian-group-structure-abelian-group-Finite-Type (m , c)) =
    finite-group-structure-group-Finite-Type X m
  pr2 (finite-abelian-group-structure-abelian-group-Finite-Type (m , c)) = c

  is-finite-structure-abelian-group-Finite-Type :
    is-finite structure-abelian-group-Finite-Type
  is-finite-structure-abelian-group-Finite-Type =
    is-finite-Σ
      ( is-finite-structure-group-Finite-Type X)
      ( λ g →
        is-finite-Π
          ( is-finite-type-Finite-Type X)
          ( λ x →
            is-finite-Π
              ( is-finite-type-Finite-Type X)
              ( λ y → is-finite-eq-Finite-Type X)))
```
