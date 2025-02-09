# Finite rings

```agda
module finite-algebra.finite-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.finite-abelian-groups
open import finite-group-theory.finite-groups
open import finite-group-theory.finite-monoids

open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.involutions
open import foundation.propositions
open import foundation.sets
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import lists.concatenation-lists
open import lists.lists

open import ring-theory.rings
open import ring-theory.semirings

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A **finite ring** is a ring where the underlying type is finite.

## Definitions

### Finite Rings

```agda
has-mul-Finite-Ab : {l1 : Level} (A : Finite-Ab l1) → UU l1
has-mul-Finite-Ab A = has-mul-Ab (ab-Finite-Ab A)

Finite-Ring : (l1 : Level) → UU (lsuc l1)
Finite-Ring l1 = Σ (Finite-Ab l1) (λ A → has-mul-Finite-Ab A)

finite-ring-is-finite-Ring :
  {l : Level} → (R : Ring l) → is-finite (type-Ring R) → Finite-Ring l
pr1 (finite-ring-is-finite-Ring R f) =
  finite-abelian-group-is-finite-Ab (ab-Ring R) f
pr2 (finite-ring-is-finite-Ring R f) = pr2 R

module _
  {l : Level} (R : Finite-Ring l)
  where

  finite-ab-Finite-Ring : Finite-Ab l
  finite-ab-Finite-Ring = pr1 R

  ab-Finite-Ring : Ab l
  ab-Finite-Ring = ab-Finite-Ab finite-ab-Finite-Ring

  ring-Finite-Ring : Ring l
  pr1 ring-Finite-Ring = ab-Finite-Ring
  pr2 ring-Finite-Ring = pr2 R

  finite-type-Finite-Ring : 𝔽 l
  finite-type-Finite-Ring = finite-type-Finite-Ab finite-ab-Finite-Ring

  type-Finite-Ring : UU l
  type-Finite-Ring = type-Finite-Ab finite-ab-Finite-Ring

  is-finite-type-Finite-Ring : is-finite type-Finite-Ring
  is-finite-type-Finite-Ring = is-finite-type-Finite-Ab finite-ab-Finite-Ring

  finite-group-Finite-Ring : Finite-Group l
  finite-group-Finite-Ring = finite-group-Finite-Ab finite-ab-Finite-Ring

  group-Finite-Ring : Group l
  group-Finite-Ring = group-Ab ab-Finite-Ring

  additive-commutative-monoid-Finite-Ring : Commutative-Monoid l
  additive-commutative-monoid-Finite-Ring =
    commutative-monoid-Ab ab-Finite-Ring

  additive-monoid-Finite-Ring : Monoid l
  additive-monoid-Finite-Ring = monoid-Ab ab-Finite-Ring

  additive-semigroup-Finite-Ring : Semigroup l
  additive-semigroup-Finite-Ring = semigroup-Ab ab-Finite-Ring

  set-Finite-Ring : Set l
  set-Finite-Ring = set-Ab ab-Finite-Ring

  is-set-type-Finite-Ring : is-set type-Finite-Ring
  is-set-type-Finite-Ring = is-set-type-Ab ab-Finite-Ring
```

### Addition in a ring

```agda
module _
  {l : Level} (R : Finite-Ring l)
  where

  has-associative-add-Finite-Ring : has-associative-mul-Set (set-Finite-Ring R)
  has-associative-add-Finite-Ring = has-associative-add-Ring (ring-Finite-Ring R)

  add-Finite-Ring : type-Finite-Ring R → type-Finite-Ring R → type-Finite-Ring R
  add-Finite-Ring = add-Ring (ring-Finite-Ring R)

  add-Finite-Ring' : type-Finite-Ring R → type-Finite-Ring R → type-Finite-Ring R
  add-Finite-Ring' = add-Ring' (ring-Finite-Ring R)

  ap-add-Finite-Ring :
    {x y x' y' : type-Finite-Ring R} →
    Id x x' → Id y y' → Id (add-Finite-Ring x y) (add-Finite-Ring x' y')
  ap-add-Finite-Ring = ap-add-Ring (ring-Finite-Ring R)

  associative-add-Finite-Ring :
    (x y z : type-Finite-Ring R) →
    Id (add-Finite-Ring (add-Finite-Ring x y) z) (add-Finite-Ring x (add-Finite-Ring y z))
  associative-add-Finite-Ring = associative-add-Ring (ring-Finite-Ring R)

  is-group-additive-semigroup-Finite-Ring :
    is-group-Semigroup (additive-semigroup-Finite-Ring R)
  is-group-additive-semigroup-Finite-Ring =
    is-group-additive-semigroup-Ring (ring-Finite-Ring R)

  commutative-add-Finite-Ring :
    (x y : type-Finite-Ring R) → Id (add-Finite-Ring x y) (add-Finite-Ring y x)
  commutative-add-Finite-Ring = commutative-add-Ring (ring-Finite-Ring R)

  interchange-add-add-Finite-Ring :
    (x y x' y' : type-Finite-Ring R) →
    ( add-Finite-Ring (add-Finite-Ring x y) (add-Finite-Ring x' y')) ＝
    ( add-Finite-Ring (add-Finite-Ring x x') (add-Finite-Ring y y'))
  interchange-add-add-Finite-Ring =
    interchange-add-add-Ring (ring-Finite-Ring R)

  right-swap-add-Finite-Ring :
    (x y z : type-Finite-Ring R) →
    add-Finite-Ring (add-Finite-Ring x y) z ＝ add-Finite-Ring (add-Finite-Ring x z) y
  right-swap-add-Finite-Ring = right-swap-add-Ring (ring-Finite-Ring R)

  left-swap-add-Finite-Ring :
    (x y z : type-Finite-Ring R) →
    add-Finite-Ring x (add-Finite-Ring y z) ＝ add-Finite-Ring y (add-Finite-Ring x z)
  left-swap-add-Finite-Ring = left-swap-add-Ring (ring-Finite-Ring R)

  is-equiv-add-Finite-Ring : (x : type-Finite-Ring R) → is-equiv (add-Finite-Ring x)
  is-equiv-add-Finite-Ring = is-equiv-add-Ring (ring-Finite-Ring R)

  is-equiv-add-Finite-Ring' : (x : type-Finite-Ring R) → is-equiv (add-Finite-Ring' x)
  is-equiv-add-Finite-Ring' = is-equiv-add-Ring' (ring-Finite-Ring R)

  is-binary-equiv-add-Finite-Ring : is-binary-equiv add-Finite-Ring
  is-binary-equiv-add-Finite-Ring = is-binary-equiv-add-Ring (ring-Finite-Ring R)

  is-binary-emb-add-Finite-Ring : is-binary-emb add-Finite-Ring
  is-binary-emb-add-Finite-Ring = is-binary-emb-add-Ring (ring-Finite-Ring R)

  is-emb-add-Finite-Ring : (x : type-Finite-Ring R) → is-emb (add-Finite-Ring x)
  is-emb-add-Finite-Ring = is-emb-add-Ring (ring-Finite-Ring R)

  is-emb-add-Finite-Ring' : (x : type-Finite-Ring R) → is-emb (add-Finite-Ring' x)
  is-emb-add-Finite-Ring' = is-emb-add-Ring' (ring-Finite-Ring R)

  is-injective-add-Finite-Ring : (x : type-Finite-Ring R) → is-injective (add-Finite-Ring x)
  is-injective-add-Finite-Ring = is-injective-add-Ring (ring-Finite-Ring R)

  is-injective-add-Finite-Ring' : (x : type-Finite-Ring R) → is-injective (add-Finite-Ring' x)
  is-injective-add-Finite-Ring' = is-injective-add-Ring' (ring-Finite-Ring R)
```

### The zero element of a ring

```agda
module _
  {l : Level} (R : Finite-Ring l)
  where

  has-zero-Finite-Ring : is-unital (add-Finite-Ring R)
  has-zero-Finite-Ring = has-zero-Ring (ring-Finite-Ring R)

  zero-Finite-Ring : type-Finite-Ring R
  zero-Finite-Ring = zero-Ring (ring-Finite-Ring R)

  is-zero-Finite-Ring : type-Finite-Ring R → UU l
  is-zero-Finite-Ring = is-zero-Ring (ring-Finite-Ring R)

  is-nonzero-Finite-Ring : type-Finite-Ring R → UU l
  is-nonzero-Finite-Ring = is-nonzero-Ring (ring-Finite-Ring R)

  is-zero-finite-ring-Prop : type-Finite-Ring R → Prop l
  is-zero-finite-ring-Prop = is-zero-ring-Prop (ring-Finite-Ring R)

  is-nonzero-finite-ring-Prop : type-Finite-Ring R → Prop l
  is-nonzero-finite-ring-Prop = is-nonzero-ring-Prop (ring-Finite-Ring R)

  left-unit-law-add-Finite-Ring :
    (x : type-Finite-Ring R) → Id (add-Finite-Ring R zero-Finite-Ring x) x
  left-unit-law-add-Finite-Ring = left-unit-law-add-Ring (ring-Finite-Ring R)

  right-unit-law-add-Finite-Ring :
    (x : type-Finite-Ring R) → Id (add-Finite-Ring R x zero-Finite-Ring) x
  right-unit-law-add-Finite-Ring = right-unit-law-add-Ring (ring-Finite-Ring R)
```

### Additive inverses in a ring

```agda
module _
  {l : Level} (R : Finite-Ring l)
  where

  has-negatives-Finite-Ring :
    is-group-is-unital-Semigroup
      ( additive-semigroup-Finite-Ring R)
      ( has-zero-Finite-Ring R)
  has-negatives-Finite-Ring = has-negatives-Ring (ring-Finite-Ring R)

  neg-Finite-Ring : type-Finite-Ring R → type-Finite-Ring R
  neg-Finite-Ring = neg-Ring (ring-Finite-Ring R)

  left-inverse-law-add-Finite-Ring :
    (x : type-Finite-Ring R) → Id (add-Finite-Ring R (neg-Finite-Ring x) x) (zero-Finite-Ring R)
  left-inverse-law-add-Finite-Ring = left-inverse-law-add-Ring (ring-Finite-Ring R)

  right-inverse-law-add-Finite-Ring :
    (x : type-Finite-Ring R) → Id (add-Finite-Ring R x (neg-Finite-Ring x)) (zero-Finite-Ring R)
  right-inverse-law-add-Finite-Ring = right-inverse-law-add-Ring (ring-Finite-Ring R)

  neg-neg-Finite-Ring : (x : type-Finite-Ring R) → neg-Finite-Ring (neg-Finite-Ring x) ＝ x
  neg-neg-Finite-Ring = neg-neg-Ring (ring-Finite-Ring R)

  distributive-neg-add-Finite-Ring :
    (x y : type-Finite-Ring R) →
    neg-Finite-Ring (add-Finite-Ring R x y) ＝ add-Finite-Ring R (neg-Finite-Ring x) (neg-Finite-Ring y)
  distributive-neg-add-Finite-Ring = distributive-neg-add-Ring (ring-Finite-Ring R)
```

### Multiplication in a ring

```agda
module _
  {l : Level} (R : Finite-Ring l)
  where

  has-associative-mul-Finite-Ring : has-associative-mul-Set (set-Finite-Ring R)
  has-associative-mul-Finite-Ring = has-associative-mul-Ring (ring-Finite-Ring R)

  mul-Finite-Ring : type-Finite-Ring R → type-Finite-Ring R → type-Finite-Ring R
  mul-Finite-Ring = mul-Ring (ring-Finite-Ring R)

  mul-Finite-Ring' : type-Finite-Ring R → type-Finite-Ring R → type-Finite-Ring R
  mul-Finite-Ring' = mul-Ring' (ring-Finite-Ring R)

  ap-mul-Finite-Ring :
    {x x' y y' : type-Finite-Ring R} (p : Id x x') (q : Id y y') →
    Id (mul-Finite-Ring x y) (mul-Finite-Ring x' y')
  ap-mul-Finite-Ring = ap-mul-Ring (ring-Finite-Ring R)

  associative-mul-Finite-Ring :
    (x y z : type-Finite-Ring R) →
    Id (mul-Finite-Ring (mul-Finite-Ring x y) z) (mul-Finite-Ring x (mul-Finite-Ring y z))
  associative-mul-Finite-Ring = associative-mul-Ring (ring-Finite-Ring R)

  multiplicative-semigroup-Finite-Ring : Semigroup l
  multiplicative-semigroup-Finite-Ring =
    multiplicative-semigroup-Ring (ring-Finite-Ring R)

  left-distributive-mul-add-Finite-Ring :
    (x y z : type-Finite-Ring R) →
    mul-Finite-Ring x (add-Finite-Ring R y z) ＝
    add-Finite-Ring R (mul-Finite-Ring x y) (mul-Finite-Ring x z)
  left-distributive-mul-add-Finite-Ring =
    left-distributive-mul-add-Ring (ring-Finite-Ring R)

  right-distributive-mul-add-Finite-Ring :
    (x y z : type-Finite-Ring R) →
    mul-Finite-Ring (add-Finite-Ring R x y) z ＝
    add-Finite-Ring R (mul-Finite-Ring x z) (mul-Finite-Ring y z)
  right-distributive-mul-add-Finite-Ring =
    right-distributive-mul-add-Ring (ring-Finite-Ring R)
```

### Multiplicative units in a ring

```agda
module _
  {l : Level} (R : Finite-Ring l)
  where

  is-unital-Finite-Ring : is-unital (mul-Finite-Ring R)
  is-unital-Finite-Ring = is-unital-Ring (ring-Finite-Ring R)

  multiplicative-monoid-Finite-Ring : Monoid l
  multiplicative-monoid-Finite-Ring = multiplicative-monoid-Ring (ring-Finite-Ring R)

  one-Finite-Ring : type-Finite-Ring R
  one-Finite-Ring = one-Ring (ring-Finite-Ring R)

  left-unit-law-mul-Finite-Ring :
    (x : type-Finite-Ring R) → Id (mul-Finite-Ring R one-Finite-Ring x) x
  left-unit-law-mul-Finite-Ring = left-unit-law-mul-Ring (ring-Finite-Ring R)

  right-unit-law-mul-Finite-Ring :
    (x : type-Finite-Ring R) → Id (mul-Finite-Ring R x one-Finite-Ring) x
  right-unit-law-mul-Finite-Ring = right-unit-law-mul-Ring (ring-Finite-Ring R)
```

### The zero laws for multiplication of a ring

```agda
module _
  {l : Level} (R : Finite-Ring l)
  where

  left-zero-law-mul-Finite-Ring :
    (x : type-Finite-Ring R) → Id (mul-Finite-Ring R (zero-Finite-Ring R) x) (zero-Finite-Ring R)
  left-zero-law-mul-Finite-Ring =
    left-zero-law-mul-Ring (ring-Finite-Ring R)

  right-zero-law-mul-Finite-Ring :
    (x : type-Finite-Ring R) → Id (mul-Finite-Ring R x (zero-Finite-Ring R)) (zero-Finite-Ring R)
  right-zero-law-mul-Finite-Ring =
    right-zero-law-mul-Ring (ring-Finite-Ring R)
```

### Rings are semirings

```agda
module _
  {l : Level} (R : Finite-Ring l)
  where

  has-mul-Finite-Ring :
    has-mul-Commutative-Monoid (additive-commutative-monoid-Finite-Ring R)
  has-mul-Finite-Ring = has-mul-Ring (ring-Finite-Ring R)

  zero-laws-mul-Finite-Ring :
    zero-laws-Commutative-Monoid
      ( additive-commutative-monoid-Finite-Ring R)
      ( has-mul-Finite-Ring)
  zero-laws-mul-Finite-Ring = zero-laws-mul-Ring (ring-Finite-Ring R)

  semiring-Finite-Ring : Semiring l
  semiring-Finite-Ring = semiring-Ring (ring-Finite-Ring R)
```

### Computing multiplication with minus one in a ring

```agda
module _
  {l : Level} (R : Finite-Ring l)
  where

  neg-one-Finite-Ring : type-Finite-Ring R
  neg-one-Finite-Ring = neg-one-Ring (ring-Finite-Ring R)

  mul-neg-one-Finite-Ring :
    (x : type-Finite-Ring R) → mul-Finite-Ring R neg-one-Finite-Ring x ＝ neg-Finite-Ring R x
  mul-neg-one-Finite-Ring =
    mul-neg-one-Ring (ring-Finite-Ring R)

  mul-neg-one-Finite-Ring' :
    (x : type-Finite-Ring R) → mul-Finite-Ring R x neg-one-Finite-Ring ＝ neg-Finite-Ring R x
  mul-neg-one-Finite-Ring' =
    mul-neg-one-Ring' (ring-Finite-Ring R)

  is-involution-mul-neg-one-Finite-Ring :
    is-involution (mul-Finite-Ring R neg-one-Finite-Ring)
  is-involution-mul-neg-one-Finite-Ring =
    is-involution-mul-neg-one-Ring (ring-Finite-Ring R)

  is-involution-mul-neg-one-Finite-Ring' :
    is-involution (mul-Finite-Ring' R neg-one-Finite-Ring)
  is-involution-mul-neg-one-Finite-Ring' =
    is-involution-mul-neg-one-Ring' (ring-Finite-Ring R)
```

### Left and right negative laws for multiplication

```agda
module _
  {l : Level} (R : Finite-Ring l)
  where

  left-negative-law-mul-Finite-Ring :
    (x y : type-Finite-Ring R) →
    mul-Finite-Ring R (neg-Finite-Ring R x) y ＝ neg-Finite-Ring R (mul-Finite-Ring R x y)
  left-negative-law-mul-Finite-Ring =
    left-negative-law-mul-Ring (ring-Finite-Ring R)

  right-negative-law-mul-Finite-Ring :
    (x y : type-Finite-Ring R) →
    mul-Finite-Ring R x (neg-Finite-Ring R y) ＝ neg-Finite-Ring R (mul-Finite-Ring R x y)
  right-negative-law-mul-Finite-Ring =
    right-negative-law-mul-Ring (ring-Finite-Ring R)

  mul-neg-Finite-Ring :
    (x y : type-Finite-Ring R) →
    mul-Finite-Ring R (neg-Finite-Ring R x) (neg-Finite-Ring R y) ＝ mul-Finite-Ring R x y
  mul-neg-Finite-Ring =
    mul-neg-Ring (ring-Finite-Ring R)
```

### Scalar multiplication of ring elements by a natural number

```agda
module _
  {l : Level} (R : Finite-Ring l)
  where

  mul-nat-scalar-Finite-Ring : ℕ → type-Finite-Ring R → type-Finite-Ring R
  mul-nat-scalar-Finite-Ring = mul-nat-scalar-Ring (ring-Finite-Ring R)

  ap-mul-nat-scalar-Finite-Ring :
    {m n : ℕ} {x y : type-Finite-Ring R} →
    (m ＝ n) → (x ＝ y) → mul-nat-scalar-Finite-Ring m x ＝ mul-nat-scalar-Finite-Ring n y
  ap-mul-nat-scalar-Finite-Ring = ap-mul-nat-scalar-Ring (ring-Finite-Ring R)

  left-zero-law-mul-nat-scalar-Finite-Ring :
    (x : type-Finite-Ring R) → mul-nat-scalar-Finite-Ring 0 x ＝ zero-Finite-Ring R
  left-zero-law-mul-nat-scalar-Finite-Ring =
    left-zero-law-mul-nat-scalar-Ring (ring-Finite-Ring R)

  right-zero-law-mul-nat-scalar-Finite-Ring :
    (n : ℕ) → mul-nat-scalar-Finite-Ring n (zero-Finite-Ring R) ＝ zero-Finite-Ring R
  right-zero-law-mul-nat-scalar-Finite-Ring =
    right-zero-law-mul-nat-scalar-Ring (ring-Finite-Ring R)

  left-unit-law-mul-nat-scalar-Finite-Ring :
    (x : type-Finite-Ring R) → mul-nat-scalar-Finite-Ring 1 x ＝ x
  left-unit-law-mul-nat-scalar-Finite-Ring =
    left-unit-law-mul-nat-scalar-Ring (ring-Finite-Ring R)

  left-nat-scalar-law-mul-Finite-Ring :
    (n : ℕ) (x y : type-Finite-Ring R) →
    mul-Finite-Ring R (mul-nat-scalar-Finite-Ring n x) y ＝
    mul-nat-scalar-Finite-Ring n (mul-Finite-Ring R x y)
  left-nat-scalar-law-mul-Finite-Ring =
    left-nat-scalar-law-mul-Ring (ring-Finite-Ring R)

  right-nat-scalar-law-mul-Finite-Ring :
    (n : ℕ) (x y : type-Finite-Ring R) →
    mul-Finite-Ring R x (mul-nat-scalar-Finite-Ring n y) ＝
    mul-nat-scalar-Finite-Ring n (mul-Finite-Ring R x y)
  right-nat-scalar-law-mul-Finite-Ring =
    right-nat-scalar-law-mul-Ring (ring-Finite-Ring R)

  left-distributive-mul-nat-scalar-add-Finite-Ring :
    (n : ℕ) (x y : type-Finite-Ring R) →
    mul-nat-scalar-Finite-Ring n (add-Finite-Ring R x y) ＝
    add-Finite-Ring R (mul-nat-scalar-Finite-Ring n x) (mul-nat-scalar-Finite-Ring n y)
  left-distributive-mul-nat-scalar-add-Finite-Ring =
    left-distributive-mul-nat-scalar-add-Ring (ring-Finite-Ring R)

  right-distributive-mul-nat-scalar-add-Finite-Ring :
    (m n : ℕ) (x : type-Finite-Ring R) →
    mul-nat-scalar-Finite-Ring (m +ℕ n) x ＝
    add-Finite-Ring R (mul-nat-scalar-Finite-Ring m x) (mul-nat-scalar-Finite-Ring n x)
  right-distributive-mul-nat-scalar-add-Finite-Ring =
    right-distributive-mul-nat-scalar-add-Ring (ring-Finite-Ring R)
```

### Addition of a list of elements in an abelian group

```agda
module _
  {l : Level} (R : Finite-Ring l)
  where

  add-list-Finite-Ring : list (type-Finite-Ring R) → type-Finite-Ring R
  add-list-Finite-Ring = add-list-Ring (ring-Finite-Ring R)

  preserves-concat-add-list-Finite-Ring :
    (l1 l2 : list (type-Finite-Ring R)) →
    Id
      ( add-list-Finite-Ring (concat-list l1 l2))
      ( add-Finite-Ring R (add-list-Finite-Ring l1) (add-list-Finite-Ring l2))
  preserves-concat-add-list-Finite-Ring =
    preserves-concat-add-list-Ring (ring-Finite-Ring R)
```

## Properties

### There is a finite number of ways to equip a finite type with the structure of a ring

```agda
module _
  {l : Level}
  (X : 𝔽 l)
  where

  structure-ring-𝔽 : UU l
  structure-ring-𝔽 =
    Σ ( structure-abelian-group-𝔽 X)
      ( λ m → has-mul-Finite-Ab (finite-abelian-group-structure-abelian-group-𝔽 X m))

  finite-ring-structure-ring-𝔽 :
    structure-ring-𝔽 → Finite-Ring l
  pr1 (finite-ring-structure-ring-𝔽 (m , c)) =
    finite-abelian-group-structure-abelian-group-𝔽 X m
  pr2 (finite-ring-structure-ring-𝔽 (m , c)) = c

  is-finite-structure-ring-𝔽 :
    is-finite structure-ring-𝔽
  is-finite-structure-ring-𝔽 =
    is-finite-Σ
      ( is-finite-structure-abelian-group-𝔽 X)
      ( λ a →
        is-finite-Σ
          ( is-finite-Σ
            ( is-finite-Π
              ( is-finite-type-𝔽 X)
              ( λ _ →
                is-finite-Π
                  ( is-finite-type-𝔽 X)
                  ( λ _ → is-finite-type-𝔽 X)))
            ( λ m →
              is-finite-Π
                ( is-finite-type-𝔽 X)
                ( λ x →
                  is-finite-Π
                    ( is-finite-type-𝔽 X)
                    ( λ y →
                      is-finite-Π
                        ( is-finite-type-𝔽 X)
                        ( λ z → is-finite-eq-𝔽 X)))))
          ( λ a →
            is-finite-product
              ( is-finite-is-unital-Finite-Semigroup (X , a))
              ( is-finite-product
                ( is-finite-Π
                  ( is-finite-type-𝔽 X)
                  ( λ _ →
                    is-finite-Π
                      ( is-finite-type-𝔽 X)
                      ( λ _ →
                        is-finite-Π
                          ( is-finite-type-𝔽 X)
                          ( λ _ → is-finite-eq-𝔽 X))))
                ( is-finite-Π
                  ( is-finite-type-𝔽 X)
                  ( λ _ →
                    is-finite-Π
                      ( is-finite-type-𝔽 X)
                      ( λ _ →
                        is-finite-Π
                          ( is-finite-type-𝔽 X)
                          ( λ _ → is-finite-eq-𝔽 X)))))))
```
