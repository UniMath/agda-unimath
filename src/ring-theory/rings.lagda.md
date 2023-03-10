# Rings

```agda
module ring-theory.rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import ring-theory.semirings

open import univalent-combinatorics.lists
```

</details>

## Idea

The concept of ring vastly generalizes the arithmetical structure on the integers. A ring consists of a set equipped with addition and multiplication, where the addition operation gives the ring the structure of an abelian group, and the multiplication is associative, unital, and distributive over addition.

## Definitions

### Rings

```agda
has-mul-Ab : {l1 : Level} (A : Ab l1) → UU l1
has-mul-Ab A =
  Σ ( has-associative-mul-Set (set-Ab A))
    ( λ μ →
      ( is-unital (pr1 μ)) ×
      ( ( (a b c : type-Ab A) →
          Id (pr1 μ a (add-Ab A b c)) (add-Ab A (pr1 μ a b) (pr1 μ a c))) ×
        ( (a b c : type-Ab A) →
          Id (pr1 μ (add-Ab A a b) c) (add-Ab A (pr1 μ a c) (pr1 μ b c)))))

Ring : (l1 : Level) → UU (lsuc l1)
Ring l1 = Σ (Ab l1) has-mul-Ab

module _
  {l : Level} (R : Ring l)
  where

  ab-Ring : Ab l
  ab-Ring = pr1 R

  group-Ring : Group l
  group-Ring = group-Ab ab-Ring

  set-Ring : Set l
  set-Ring = set-Ab ab-Ring

  type-Ring : UU l
  type-Ring = type-Ab ab-Ring

  is-set-type-Ring : is-set type-Ring
  is-set-type-Ring = is-set-type-Ab ab-Ring
```

### Addition in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-associative-add-Ring : has-associative-mul-Set (set-Ring R)
  has-associative-add-Ring = has-associative-add-Ab (ab-Ring R)

  add-Ring : type-Ring R → type-Ring R → type-Ring R
  add-Ring = add-Ab (ab-Ring R)

  add-Ring' : type-Ring R → type-Ring R → type-Ring R
  add-Ring' = add-Ab' (ab-Ring R)

  ap-add-Ring :
    {x y x' y' : type-Ring R} →
    Id x x' → Id y y' → Id (add-Ring x y) (add-Ring x' y')
  ap-add-Ring = ap-add-Ab (ab-Ring R)

  associative-add-Ring :
    (x y z : type-Ring R) →
    Id (add-Ring (add-Ring x y) z) (add-Ring x (add-Ring y z))
  associative-add-Ring = associative-add-Ab (ab-Ring R)

  additive-semigroup-Ring : Semigroup l
  additive-semigroup-Ring = semigroup-Ab (ab-Ring R)

  is-group-additive-semigroup-Ring : is-group additive-semigroup-Ring
  is-group-additive-semigroup-Ring = is-group-Ab (ab-Ring R)

  commutative-add-Ring : (x y : type-Ring R) → Id (add-Ring x y) (add-Ring y x)
  commutative-add-Ring = commutative-add-Ab (ab-Ring R)

  interchange-add-add-Ring :
    (x y x' y' : type-Ring R) →
    ( add-Ring (add-Ring x y) (add-Ring x' y')) ＝
    ( add-Ring (add-Ring x x') (add-Ring y y'))
  interchange-add-add-Ring =
    interchange-add-add-Ab (ab-Ring R)

  right-swap-add-Ring :
    (x y z : type-Ring R) →
    add-Ring (add-Ring x y) z ＝ add-Ring (add-Ring x z) y
  right-swap-add-Ring = right-swap-add-Ab (ab-Ring R)

  left-swap-add-Ring :
    (x y z : type-Ring R) →
    add-Ring x (add-Ring y z) ＝ add-Ring y (add-Ring x z)
  left-swap-add-Ring = left-swap-add-Ab (ab-Ring R)

  is-equiv-add-Ring : (x : type-Ring R) → is-equiv (add-Ring x)
  is-equiv-add-Ring = is-equiv-add-Ab (ab-Ring R)

  is-equiv-add-Ring' : (x : type-Ring R) → is-equiv (add-Ring' x)
  is-equiv-add-Ring' = is-equiv-add-Ab' (ab-Ring R)

  is-binary-equiv-add-Ring : is-binary-equiv add-Ring
  pr1 is-binary-equiv-add-Ring = is-equiv-add-Ring'
  pr2 is-binary-equiv-add-Ring = is-equiv-add-Ring

  is-binary-emb-add-Ring : is-binary-emb add-Ring
  is-binary-emb-add-Ring = is-binary-emb-add-Ab (ab-Ring R)

  is-emb-add-Ring : (x : type-Ring R) → is-emb (add-Ring x)
  is-emb-add-Ring = is-emb-add-Ab (ab-Ring R)

  is-emb-add-Ring' : (x : type-Ring R) → is-emb (add-Ring' x)
  is-emb-add-Ring' = is-emb-add-Ab' (ab-Ring R)

  is-injective-add-Ring : (x : type-Ring R) → is-injective (add-Ring x)
  is-injective-add-Ring = is-injective-add-Ab (ab-Ring R)

  is-injective-add-Ring' : (x : type-Ring R) → is-injective (add-Ring' x)
  is-injective-add-Ring' = is-injective-add-Ab' (ab-Ring R)
```

### The zero element of a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-zero-Ring : is-unital (add-Ring R)
  has-zero-Ring = has-zero-Ab (ab-Ring R)

  zero-Ring : type-Ring R
  zero-Ring = zero-Ab (ab-Ring R)

  is-zero-Ring : type-Ring R → UU l
  is-zero-Ring x = Id x zero-Ring

  is-nonzero-Ring : type-Ring R → UU l
  is-nonzero-Ring x = ¬ (is-zero-Ring x)

  is-zero-ring-Prop : type-Ring R → Prop l
  is-zero-ring-Prop x = Id-Prop (set-Ring R) x zero-Ring

  left-unit-law-add-Ring : (x : type-Ring R) → Id (add-Ring R zero-Ring x) x
  left-unit-law-add-Ring = left-unit-law-add-Ab (ab-Ring R)

  right-unit-law-add-Ring : (x : type-Ring R) → Id (add-Ring R x zero-Ring) x
  right-unit-law-add-Ring = right-unit-law-add-Ab (ab-Ring R)
```

### Additive inverses in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-negatives-Ring : is-group' (additive-semigroup-Ring R) (has-zero-Ring R)
  has-negatives-Ring = has-negatives-Ab (ab-Ring R)

  neg-Ring : type-Ring R → type-Ring R
  neg-Ring = neg-Ab (ab-Ring R)

  left-inverse-law-add-Ring :
    (x : type-Ring R) → Id (add-Ring R (neg-Ring x) x) (zero-Ring R)
  left-inverse-law-add-Ring = left-inverse-law-add-Ab (ab-Ring R)

  right-inverse-law-add-Ring :
    (x : type-Ring R) → Id (add-Ring R x (neg-Ring x)) (zero-Ring R)
  right-inverse-law-add-Ring = right-inverse-law-add-Ab (ab-Ring R)
```

### Multiplication in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-associative-mul-Ring : has-associative-mul-Set (set-Ring R)
  has-associative-mul-Ring = pr1 (pr2 R)

  mul-Ring : type-Ring R → type-Ring R → type-Ring R
  mul-Ring = pr1 has-associative-mul-Ring

  mul-Ring' : type-Ring R → type-Ring R → type-Ring R
  mul-Ring' x y = mul-Ring y x

  ap-mul-Ring :
    {x x' y y' : type-Ring R} (p : Id x x') (q : Id y y') →
    Id (mul-Ring x y) (mul-Ring x' y')
  ap-mul-Ring p q = ap-binary mul-Ring p q

  associative-mul-Ring :
    (x y z : type-Ring R) →
    Id (mul-Ring (mul-Ring x y) z) (mul-Ring x (mul-Ring y z))
  associative-mul-Ring = pr2 has-associative-mul-Ring

  multiplicative-semigroup-Ring : Semigroup l
  pr1 multiplicative-semigroup-Ring = set-Ring R
  pr2 multiplicative-semigroup-Ring = has-associative-mul-Ring

  left-distributive-mul-add-Ring :
    (x y z : type-Ring R) →
    Id (mul-Ring x (add-Ring R y z)) (add-Ring R (mul-Ring x y) (mul-Ring x z))
  left-distributive-mul-add-Ring =
    pr1 (pr2 (pr2 (pr2 R)))

  right-distributive-mul-add-Ring :
    (x y z : type-Ring R) →
    Id ( mul-Ring (add-Ring R x y) z)
      ( add-Ring R (mul-Ring x z) (mul-Ring y z))
  right-distributive-mul-add-Ring =
    pr2 (pr2 (pr2 (pr2 R)))
```

### Multiplicative units in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-unital-Ring : is-unital (mul-Ring R)
  is-unital-Ring = pr1 (pr2 (pr2 R))

  multiplicative-monoid-Ring : Monoid l
  pr1 multiplicative-monoid-Ring = multiplicative-semigroup-Ring R
  pr2 multiplicative-monoid-Ring = is-unital-Ring

  one-Ring : type-Ring R
  one-Ring = unit-Monoid multiplicative-monoid-Ring

  left-unit-law-mul-Ring : (x : type-Ring R) → Id (mul-Ring R one-Ring x) x
  left-unit-law-mul-Ring = left-unit-law-mul-Monoid multiplicative-monoid-Ring

  right-unit-law-mul-Ring : (x : type-Ring R) → Id (mul-Ring R x one-Ring) x
  right-unit-law-mul-Ring = right-unit-law-mul-Monoid multiplicative-monoid-Ring
```

### The zero laws for multiplication of a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-zero-law-mul-Ring :
    (x : type-Ring R) → Id (mul-Ring R (zero-Ring R) x) (zero-Ring R)
  left-zero-law-mul-Ring x =
    is-zero-is-idempotent-Ab
      ( ab-Ring R)
      ( ( inv
          ( right-distributive-mul-add-Ring R (zero-Ring R) (zero-Ring R) x)) ∙
        ( ap (mul-Ring' R x) (left-unit-law-add-Ring R (zero-Ring R))))

  right-zero-law-mul-Ring :
    (x : type-Ring R) → Id (mul-Ring R x (zero-Ring R)) (zero-Ring R)
  right-zero-law-mul-Ring x =
    is-zero-is-idempotent-Ab
      ( ab-Ring R)
      ( ( inv
          ( left-distributive-mul-add-Ring R x (zero-Ring R) (zero-Ring R))) ∙
        ( ap (mul-Ring R x) (left-unit-law-add-Ring R (zero-Ring R))))
```

### Rings are semirings

```agda
module _
  {l : Level} (R : Ring l)
  where

  commutative-monoid-Ring : Commutative-Monoid l
  commutative-monoid-Ring = commutative-monoid-Ab (ab-Ring R)

  has-mul-Ring : has-mul-Commutative-Monoid commutative-monoid-Ring
  pr1 has-mul-Ring = has-associative-mul-Ring R
  pr1 (pr2 has-mul-Ring) = is-unital-Ring R
  pr1 (pr2 (pr2 has-mul-Ring)) = left-distributive-mul-add-Ring R
  pr2 (pr2 (pr2 has-mul-Ring)) = right-distributive-mul-add-Ring R

  zero-laws-mul-Ring :
    zero-laws-Commutative-Monoid commutative-monoid-Ring has-mul-Ring
  pr1 zero-laws-mul-Ring = left-zero-law-mul-Ring R
  pr2 zero-laws-mul-Ring = right-zero-law-mul-Ring R

  semiring-Ring : Semiring l
  pr1 semiring-Ring = commutative-monoid-Ring
  pr1 (pr2 semiring-Ring) = has-mul-Ring
  pr2 (pr2 semiring-Ring) = zero-laws-mul-Ring
```

### Computing multiplication with minus one in a ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  neg-one-Ring : type-Ring R
  neg-one-Ring = neg-Ring R (one-Ring R)

  mul-neg-one-Ring :
    (x : type-Ring R) → Id (mul-Ring R neg-one-Ring x) (neg-Ring R x)
  mul-neg-one-Ring x =
    is-injective-add-Ring R x
      ( ( ap
          ( add-Ring' R (mul-Ring R neg-one-Ring x))
          ( inv (left-unit-law-mul-Ring R x)) ∙
        ( ( inv
            ( right-distributive-mul-add-Ring R (one-Ring R) neg-one-Ring x)) ∙
          ( ( ap (mul-Ring' R x) (right-inverse-law-add-Ring R (one-Ring R))) ∙
            ( left-zero-law-mul-Ring R x)))) ∙
        ( inv (right-inverse-law-add-Ring R x)))
```

### Scalar multiplication of ring elements by a natural number

```agda
module _
  {l : Level} (R : Ring l)
  where

  mul-nat-scalar-Ring : ℕ → type-Ring R → type-Ring R
  mul-nat-scalar-Ring = mul-nat-scalar-Semiring (semiring-Ring R)

  ap-mul-nat-scalar-Ring :
    {m n : ℕ} {x y : type-Ring R} →
    (m ＝ n) → (x ＝ y) → mul-nat-scalar-Ring m x ＝ mul-nat-scalar-Ring n y
  ap-mul-nat-scalar-Ring = ap-mul-nat-scalar-Semiring (semiring-Ring R)

  left-unit-law-mul-nat-scalar-Ring :
    (x : type-Ring R) →  mul-nat-scalar-Ring 1 x ＝ x
  left-unit-law-mul-nat-scalar-Ring =
    left-unit-law-mul-nat-scalar-Semiring (semiring-Ring R)

  left-nat-scalar-law-mul-Ring :
    (n : ℕ) (x y : type-Ring R) →
    mul-Ring R (mul-nat-scalar-Ring n x) y ＝
    mul-nat-scalar-Ring n (mul-Ring R x y)
  left-nat-scalar-law-mul-Ring =
    left-nat-scalar-law-mul-Semiring (semiring-Ring R)

  right-nat-scalar-law-mul-Ring :
    (n : ℕ) (x y : type-Ring R) →
    mul-Ring R x (mul-nat-scalar-Ring n y) ＝
    mul-nat-scalar-Ring n (mul-Ring R x y)
  right-nat-scalar-law-mul-Ring =
    right-nat-scalar-law-mul-Semiring (semiring-Ring R)

  left-distributive-mul-nat-scalar-add-Ring :
    (n : ℕ) (x y : type-Ring R) →
    mul-nat-scalar-Ring n (add-Ring R x y) ＝
    add-Ring R (mul-nat-scalar-Ring n x) (mul-nat-scalar-Ring n y)
  left-distributive-mul-nat-scalar-add-Ring =
    left-distributive-mul-nat-scalar-add-Semiring (semiring-Ring R)

  right-distributive-mul-nat-scalar-add-Ring :
    (m n : ℕ) (x : type-Ring R) →
    mul-nat-scalar-Ring (add-ℕ m n) x ＝
    add-Ring R (mul-nat-scalar-Ring m x) (mul-nat-scalar-Ring n x)
  right-distributive-mul-nat-scalar-add-Ring =
    right-distributive-mul-nat-scalar-add-Semiring (semiring-Ring R)
```

### Addition of a list of elements in an abelian group

```agda
module _
  {l : Level} (R : Ring l)
  where

  add-list-Ring : list (type-Ring R) → type-Ring R
  add-list-Ring = add-list-Ab (ab-Ring R)

  preserves-concat-add-list-Ring :
    (l1 l2 : list (type-Ring R)) →
    Id ( add-list-Ring (concat-list l1 l2))
       ( add-Ring R (add-list-Ring l1) (add-list-Ring l2))
  preserves-concat-add-list-Ring = preserves-concat-add-list-Ab (ab-Ring R)
```
