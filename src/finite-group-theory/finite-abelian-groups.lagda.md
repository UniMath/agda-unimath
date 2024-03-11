# Abelian groups

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

Abelian groups are groups of which the group operation is commutative

## Definition

### The condition of being an abelian group

```agda
is-abelian-prop-Group-𝔽 : {l : Level} → Group-𝔽 l → Prop l
is-abelian-prop-Group-𝔽 G = is-abelian-prop-Group (group-Group-𝔽 G)

is-abelian-Group-𝔽 : {l : Level} → Group-𝔽 l → UU l
is-abelian-Group-𝔽 G = type-Prop (is-abelian-prop-Group-𝔽 G)

is-prop-is-abelian-Group-𝔽 :
  {l : Level} (G : Group-𝔽 l) → is-prop (is-abelian-Group-𝔽 G)
is-prop-is-abelian-Group-𝔽 G =
  is-prop-type-Prop (is-abelian-prop-Group-𝔽 G)
```

### The type of abelian groups

```agda
Ab-𝔽 : (l : Level) → UU (lsuc l)
Ab-𝔽 l = Σ (Group-𝔽 l) is-abelian-Group-𝔽

finite-abelian-group-is-finite-Ab :
  {l : Level} → (A : Ab l) → is-finite (type-Ab A) → Ab-𝔽 l
pr1 (finite-abelian-group-is-finite-Ab A f) =
  finite-group-is-finite-Group (group-Ab A) f
pr2 (finite-abelian-group-is-finite-Ab A f) = pr2 A

module _
  {l : Level} (A : Ab-𝔽 l)
  where

  finite-group-Ab-𝔽 : Group-𝔽 l
  finite-group-Ab-𝔽 = pr1 A

  group-Ab-𝔽 : Group l
  group-Ab-𝔽 = group-Group-𝔽 finite-group-Ab-𝔽

  finite-type-Ab-𝔽 : 𝔽 l
  finite-type-Ab-𝔽 = finite-type-Group-𝔽 finite-group-Ab-𝔽

  type-Ab-𝔽 : UU l
  type-Ab-𝔽 = type-Group-𝔽 finite-group-Ab-𝔽

  is-finite-type-Ab-𝔽 : is-finite type-Ab-𝔽
  is-finite-type-Ab-𝔽 = is-finite-type-Group-𝔽 finite-group-Ab-𝔽

  set-Ab-𝔽 : Set l
  set-Ab-𝔽 = set-Group group-Ab-𝔽

  is-set-type-Ab-𝔽 : is-set type-Ab-𝔽
  is-set-type-Ab-𝔽 = is-set-type-Group group-Ab-𝔽

  has-associative-add-Ab-𝔽 : has-associative-mul-Set set-Ab-𝔽
  has-associative-add-Ab-𝔽 = has-associative-mul-Group group-Ab-𝔽

  add-Ab-𝔽 : type-Ab-𝔽 → type-Ab-𝔽 → type-Ab-𝔽
  add-Ab-𝔽 = mul-Group group-Ab-𝔽

  add-Ab-𝔽' : type-Ab-𝔽 → type-Ab-𝔽 → type-Ab-𝔽
  add-Ab-𝔽' = mul-Group' group-Ab-𝔽

  commutative-add-Ab-𝔽 : (x y : type-Ab-𝔽) → Id (add-Ab-𝔽 x y) (add-Ab-𝔽 y x)
  commutative-add-Ab-𝔽 = pr2 A

  ab-Ab-𝔽 : Ab l
  pr1 ab-Ab-𝔽 = group-Ab-𝔽
  pr2 ab-Ab-𝔽 = commutative-add-Ab-𝔽

  ap-add-Ab-𝔽 :
    {x y x' y' : type-Ab-𝔽} → x ＝ x' → y ＝ y' → add-Ab-𝔽 x y ＝ add-Ab-𝔽 x' y'
  ap-add-Ab-𝔽 = ap-add-Ab ab-Ab-𝔽

  associative-add-Ab-𝔽 :
    (x y z : type-Ab-𝔽) → add-Ab-𝔽 (add-Ab-𝔽 x y) z ＝ add-Ab-𝔽 x (add-Ab-𝔽 y z)
  associative-add-Ab-𝔽 = associative-mul-Group group-Ab-𝔽

  semigroup-Ab-𝔽 : Semigroup l
  semigroup-Ab-𝔽 = semigroup-Group group-Ab-𝔽

  is-group-Ab-𝔽 : is-group-Semigroup semigroup-Ab-𝔽
  is-group-Ab-𝔽 = is-group-Group group-Ab-𝔽

  has-zero-Ab-𝔽 : is-unital-Semigroup semigroup-Ab-𝔽
  has-zero-Ab-𝔽 = is-unital-Group group-Ab-𝔽

  zero-Ab-𝔽 : type-Ab-𝔽
  zero-Ab-𝔽 = unit-Group group-Ab-𝔽

  is-zero-Ab-𝔽 : type-Ab-𝔽 → UU l
  is-zero-Ab-𝔽 = is-unit-Group group-Ab-𝔽

  is-prop-is-zero-Ab-𝔽 : (x : type-Ab-𝔽) → is-prop (is-zero-Ab-𝔽 x)
  is-prop-is-zero-Ab-𝔽 = is-prop-is-unit-Group group-Ab-𝔽

  is-zero-prop-Ab-𝔽 : type-Ab-𝔽 → Prop l
  is-zero-prop-Ab-𝔽 = is-unit-prop-Group group-Ab-𝔽

  left-unit-law-add-Ab-𝔽 : (x : type-Ab-𝔽) → add-Ab-𝔽 zero-Ab-𝔽 x ＝ x
  left-unit-law-add-Ab-𝔽 = left-unit-law-mul-Group group-Ab-𝔽

  right-unit-law-add-Ab-𝔽 : (x : type-Ab-𝔽) → add-Ab-𝔽 x zero-Ab-𝔽 ＝ x
  right-unit-law-add-Ab-𝔽 = right-unit-law-mul-Group group-Ab-𝔽

  has-negatives-Ab-𝔽 : is-group-is-unital-Semigroup semigroup-Ab-𝔽 has-zero-Ab-𝔽
  has-negatives-Ab-𝔽 = has-inverses-Group group-Ab-𝔽

  neg-Ab-𝔽 : type-Ab-𝔽 → type-Ab-𝔽
  neg-Ab-𝔽 = inv-Group group-Ab-𝔽

  left-inverse-law-add-Ab-𝔽 :
    (x : type-Ab-𝔽) → add-Ab-𝔽 (neg-Ab-𝔽 x) x ＝ zero-Ab-𝔽
  left-inverse-law-add-Ab-𝔽 = left-inverse-law-mul-Group group-Ab-𝔽

  right-inverse-law-add-Ab-𝔽 :
    (x : type-Ab-𝔽) → add-Ab-𝔽 x (neg-Ab-𝔽 x) ＝ zero-Ab-𝔽
  right-inverse-law-add-Ab-𝔽 = right-inverse-law-mul-Group group-Ab-𝔽

  interchange-add-add-Ab-𝔽 :
    (a b c d : type-Ab-𝔽) →
    add-Ab-𝔽 (add-Ab-𝔽 a b) (add-Ab-𝔽 c d) ＝
    add-Ab-𝔽 (add-Ab-𝔽 a c) (add-Ab-𝔽 b d)
  interchange-add-add-Ab-𝔽 =
    interchange-law-commutative-and-associative
      add-Ab-𝔽
      commutative-add-Ab-𝔽
      associative-add-Ab-𝔽

  right-swap-add-Ab-𝔽 :
    (a b c : type-Ab-𝔽) → add-Ab-𝔽 (add-Ab-𝔽 a b) c ＝ add-Ab-𝔽 (add-Ab-𝔽 a c) b
  right-swap-add-Ab-𝔽 = right-swap-add-Ab ab-Ab-𝔽

  left-swap-add-Ab-𝔽 :
    (a b c : type-Ab-𝔽) → add-Ab-𝔽 a (add-Ab-𝔽 b c) ＝ add-Ab-𝔽 b (add-Ab-𝔽 a c)
  left-swap-add-Ab-𝔽 = left-swap-add-Ab ab-Ab-𝔽

  distributive-neg-add-Ab-𝔽 :
    (x y : type-Ab-𝔽) →
    neg-Ab-𝔽 (add-Ab-𝔽 x y) ＝ add-Ab-𝔽 (neg-Ab-𝔽 x) (neg-Ab-𝔽 y)
  distributive-neg-add-Ab-𝔽 = distributive-neg-add-Ab ab-Ab-𝔽

  neg-neg-Ab-𝔽 : (x : type-Ab-𝔽) → neg-Ab-𝔽 (neg-Ab-𝔽 x) ＝ x
  neg-neg-Ab-𝔽 = neg-neg-Ab ab-Ab-𝔽

  neg-zero-Ab-𝔽 : neg-Ab-𝔽 zero-Ab-𝔽 ＝ zero-Ab-𝔽
  neg-zero-Ab-𝔽 = neg-zero-Ab ab-Ab-𝔽
```

### Conjugation in an abelian group

```agda
module _
  {l : Level} (A : Ab-𝔽 l)
  where

  equiv-conjugation-Ab-𝔽 : (x : type-Ab-𝔽 A) → type-Ab-𝔽 A ≃ type-Ab-𝔽 A
  equiv-conjugation-Ab-𝔽 = equiv-conjugation-Group (group-Ab-𝔽 A)

  conjugation-Ab-𝔽 : (x : type-Ab-𝔽 A) → type-Ab-𝔽 A → type-Ab-𝔽 A
  conjugation-Ab-𝔽 = conjugation-Group (group-Ab-𝔽 A)

  equiv-conjugation-Ab-𝔽' : (x : type-Ab-𝔽 A) → type-Ab-𝔽 A ≃ type-Ab-𝔽 A
  equiv-conjugation-Ab-𝔽' = equiv-conjugation-Group' (group-Ab-𝔽 A)

  conjugation-Ab-𝔽' : (x : type-Ab-𝔽 A) → type-Ab-𝔽 A → type-Ab-𝔽 A
  conjugation-Ab-𝔽' = conjugation-Group' (group-Ab-𝔽 A)
```

## Properties

### There is a finite number of ways to equip a finite type with the structure of an abelian group

```agda
module _
  {l : Level}
  (X : 𝔽 l)
  where

  structure-abelian-group-𝔽 : UU l
  structure-abelian-group-𝔽 =
    Σ ( structure-group-𝔽 X)
      ( λ g → is-abelian-Group-𝔽 (finite-group-structure-group-𝔽 X g))

  finite-abelian-group-structure-abelian-group-𝔽 :
    structure-abelian-group-𝔽 → Ab-𝔽 l
  pr1 (finite-abelian-group-structure-abelian-group-𝔽 (m , c)) =
    finite-group-structure-group-𝔽 X m
  pr2 (finite-abelian-group-structure-abelian-group-𝔽 (m , c)) = c

  is-finite-structure-abelian-group-𝔽 :
    is-finite structure-abelian-group-𝔽
  is-finite-structure-abelian-group-𝔽 =
    is-finite-Σ
      ( is-finite-structure-group-𝔽 X)
      ( λ g →
        is-finite-Π
          ( is-finite-type-𝔽 X)
          ( λ x →
            is-finite-Π
              ( is-finite-type-𝔽 X)
              ( λ y → is-finite-eq-𝔽 X)))
```
