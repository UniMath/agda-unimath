# Integral domains

```agda
module commutative-algebra.integral-domains where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.commutative-semirings
open import commutative-algebra.trivial-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
open import foundation.involutions
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

open import lists.concatenation-lists
open import lists.lists

open import ring-theory.rings
open import ring-theory.semirings
```

</details>

## Idea

An **integral domain** is a nonzero commutative ring `R` such that the product
of any two nonzero elements in `R` is nonzero. Equivalently, a commutative ring
`R` is an integral domain if and only if multiplication by any nonzero element
`a` satisfies the cancellation property: `ax = ay ⇒ x = y`.

## Definition

### The cancellation property for a commutative ring

```agda
cancellation-property-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → UU l
cancellation-property-Commutative-Ring R =
  (x : type-Commutative-Ring R) → is-nonzero-Commutative-Ring R x →
  is-injective (mul-Commutative-Ring R x)
```

### Integral domains

```agda
Integral-Domain : (l : Level) → UU (lsuc l)
Integral-Domain l =
  Σ ( Commutative-Ring l)
    ( λ R →
      cancellation-property-Commutative-Ring R ×
      is-nontrivial-Commutative-Ring R)

module _
  {l : Level} (R : Integral-Domain l)
  where

  commutative-ring-Integral-Domain : Commutative-Ring l
  commutative-ring-Integral-Domain = pr1 R

  has-cancellation-property-Integral-Domain :
    cancellation-property-Commutative-Ring commutative-ring-Integral-Domain
  has-cancellation-property-Integral-Domain = pr1 (pr2 R)

  is-nontrivial-Integral-Domain :
    is-nontrivial-Commutative-Ring commutative-ring-Integral-Domain
  is-nontrivial-Integral-Domain = pr2 (pr2 R)

  ab-Integral-Domain : Ab l
  ab-Integral-Domain = ab-Commutative-Ring commutative-ring-Integral-Domain

  ring-Integral-Domain : Ring l
  ring-Integral-Domain = ring-Commutative-Ring commutative-ring-Integral-Domain

  set-Integral-Domain : Set l
  set-Integral-Domain = set-Ring ring-Integral-Domain

  type-Integral-Domain : UU l
  type-Integral-Domain = type-Ring ring-Integral-Domain

  is-set-type-Integral-Domain : is-set type-Integral-Domain
  is-set-type-Integral-Domain = is-set-type-Ring ring-Integral-Domain
```

### Addition in an integral domain

```agda
  has-associative-add-Integral-Domain :
    has-associative-mul-Set set-Integral-Domain
  has-associative-add-Integral-Domain =
    has-associative-add-Commutative-Ring commutative-ring-Integral-Domain

  add-Integral-Domain :
    type-Integral-Domain → type-Integral-Domain → type-Integral-Domain
  add-Integral-Domain = add-Commutative-Ring commutative-ring-Integral-Domain

  add-Integral-Domain' :
    type-Integral-Domain → type-Integral-Domain → type-Integral-Domain
  add-Integral-Domain' = add-Commutative-Ring' commutative-ring-Integral-Domain

  ap-add-Integral-Domain :
    {x x' y y' : type-Integral-Domain} →
    (x ＝ x') → (y ＝ y') →
    add-Integral-Domain x y ＝ add-Integral-Domain x' y'
  ap-add-Integral-Domain =
    ap-add-Commutative-Ring commutative-ring-Integral-Domain

  associative-add-Integral-Domain :
    (x y z : type-Integral-Domain) →
    ( add-Integral-Domain (add-Integral-Domain x y) z) ＝
    ( add-Integral-Domain x (add-Integral-Domain y z))
  associative-add-Integral-Domain =
    associative-add-Commutative-Ring commutative-ring-Integral-Domain

  additive-semigroup-Integral-Domain : Semigroup l
  additive-semigroup-Integral-Domain = semigroup-Ab ab-Integral-Domain

  is-group-additive-semigroup-Integral-Domain :
    is-group-Semigroup additive-semigroup-Integral-Domain
  is-group-additive-semigroup-Integral-Domain =
    is-group-Ab ab-Integral-Domain

  commutative-add-Integral-Domain :
    (x y : type-Integral-Domain) →
    add-Integral-Domain x y ＝ add-Integral-Domain y x
  commutative-add-Integral-Domain = commutative-add-Ab ab-Integral-Domain

  interchange-add-add-Integral-Domain :
    (x y x' y' : type-Integral-Domain) →
    ( add-Integral-Domain
      ( add-Integral-Domain x y)
      ( add-Integral-Domain x' y')) ＝
    ( add-Integral-Domain
      ( add-Integral-Domain x x')
      ( add-Integral-Domain y y'))
  interchange-add-add-Integral-Domain =
    interchange-add-add-Commutative-Ring commutative-ring-Integral-Domain

  right-swap-add-Integral-Domain :
    (x y z : type-Integral-Domain) →
    ( add-Integral-Domain (add-Integral-Domain x y) z) ＝
    ( add-Integral-Domain (add-Integral-Domain x z) y)
  right-swap-add-Integral-Domain =
    right-swap-add-Commutative-Ring commutative-ring-Integral-Domain

  left-swap-add-Integral-Domain :
    (x y z : type-Integral-Domain) →
    ( add-Integral-Domain x (add-Integral-Domain y z)) ＝
    ( add-Integral-Domain y (add-Integral-Domain x z))
  left-swap-add-Integral-Domain =
    left-swap-add-Commutative-Ring commutative-ring-Integral-Domain

  is-equiv-add-Integral-Domain :
    (x : type-Integral-Domain) → is-equiv (add-Integral-Domain x)
  is-equiv-add-Integral-Domain = is-equiv-add-Ab ab-Integral-Domain

  is-equiv-add-Integral-Domain' :
    (x : type-Integral-Domain) → is-equiv (add-Integral-Domain' x)
  is-equiv-add-Integral-Domain' = is-equiv-add-Ab' ab-Integral-Domain

  is-binary-equiv-add-Integral-Domain : is-binary-equiv add-Integral-Domain
  pr1 is-binary-equiv-add-Integral-Domain = is-equiv-add-Integral-Domain'
  pr2 is-binary-equiv-add-Integral-Domain = is-equiv-add-Integral-Domain

  is-binary-emb-add-Integral-Domain : is-binary-emb add-Integral-Domain
  is-binary-emb-add-Integral-Domain = is-binary-emb-add-Ab ab-Integral-Domain

  is-emb-add-Integral-Domain :
    (x : type-Integral-Domain) → is-emb (add-Integral-Domain x)
  is-emb-add-Integral-Domain = is-emb-add-Ab ab-Integral-Domain

  is-emb-add-Integral-Domain' :
    (x : type-Integral-Domain) → is-emb (add-Integral-Domain' x)
  is-emb-add-Integral-Domain' = is-emb-add-Ab' ab-Integral-Domain

  is-injective-add-Integral-Domain :
    (x : type-Integral-Domain) → is-injective (add-Integral-Domain x)
  is-injective-add-Integral-Domain = is-injective-add-Ab ab-Integral-Domain

  is-injective-add-Integral-Domain' :
    (x : type-Integral-Domain) → is-injective (add-Integral-Domain' x)
  is-injective-add-Integral-Domain' = is-injective-add-Ab' ab-Integral-Domain
```

### The zero element of an integral domain

```agda
  has-zero-Integral-Domain : is-unital add-Integral-Domain
  has-zero-Integral-Domain =
    has-zero-Commutative-Ring commutative-ring-Integral-Domain

  zero-Integral-Domain : type-Integral-Domain
  zero-Integral-Domain =
    zero-Commutative-Ring commutative-ring-Integral-Domain

  is-zero-Integral-Domain : type-Integral-Domain → UU l
  is-zero-Integral-Domain =
    is-zero-Commutative-Ring commutative-ring-Integral-Domain

  is-nonzero-Integral-Domain : type-Integral-Domain → UU l
  is-nonzero-Integral-Domain =
    is-nonzero-Commutative-Ring commutative-ring-Integral-Domain

  is-zero-integral-domain-Prop : type-Integral-Domain → Prop l
  is-zero-integral-domain-Prop x =
    Id-Prop set-Integral-Domain x zero-Integral-Domain

  is-nonzero-integral-domain-Prop : type-Integral-Domain → Prop l
  is-nonzero-integral-domain-Prop x =
    neg-Prop (is-zero-integral-domain-Prop x)

  left-unit-law-add-Integral-Domain :
    (x : type-Integral-Domain) →
    add-Integral-Domain zero-Integral-Domain x ＝ x
  left-unit-law-add-Integral-Domain =
    left-unit-law-add-Commutative-Ring commutative-ring-Integral-Domain

  right-unit-law-add-Integral-Domain :
    (x : type-Integral-Domain) →
    add-Integral-Domain x zero-Integral-Domain ＝ x
  right-unit-law-add-Integral-Domain =
    right-unit-law-add-Commutative-Ring commutative-ring-Integral-Domain
```

### Additive inverses in an integral domain

```agda
  has-negatives-Integral-Domain :
    is-group-is-unital-Semigroup
      ( additive-semigroup-Integral-Domain)
      ( has-zero-Integral-Domain)
  has-negatives-Integral-Domain = has-negatives-Ab ab-Integral-Domain

  neg-Integral-Domain : type-Integral-Domain → type-Integral-Domain
  neg-Integral-Domain = neg-Commutative-Ring commutative-ring-Integral-Domain

  left-inverse-law-add-Integral-Domain :
    (x : type-Integral-Domain) →
    add-Integral-Domain (neg-Integral-Domain x) x ＝ zero-Integral-Domain
  left-inverse-law-add-Integral-Domain =
    left-inverse-law-add-Commutative-Ring commutative-ring-Integral-Domain

  right-inverse-law-add-Integral-Domain :
    (x : type-Integral-Domain) →
    add-Integral-Domain x (neg-Integral-Domain x) ＝ zero-Integral-Domain
  right-inverse-law-add-Integral-Domain =
    right-inverse-law-add-Commutative-Ring commutative-ring-Integral-Domain

  neg-neg-Integral-Domain :
    (x : type-Integral-Domain) →
    neg-Integral-Domain (neg-Integral-Domain x) ＝ x
  neg-neg-Integral-Domain = neg-neg-Ab ab-Integral-Domain

  distributive-neg-add-Integral-Domain :
    (x y : type-Integral-Domain) →
    neg-Integral-Domain (add-Integral-Domain x y) ＝
    add-Integral-Domain (neg-Integral-Domain x) (neg-Integral-Domain y)
  distributive-neg-add-Integral-Domain =
    distributive-neg-add-Ab ab-Integral-Domain
```

### Multiplication in an integral domain

```agda
  has-associative-mul-Integral-Domain :
    has-associative-mul-Set set-Integral-Domain
  has-associative-mul-Integral-Domain =
    has-associative-mul-Commutative-Ring commutative-ring-Integral-Domain

  mul-Integral-Domain :
    (x y : type-Integral-Domain) → type-Integral-Domain
  mul-Integral-Domain =
    mul-Commutative-Ring commutative-ring-Integral-Domain

  mul-Integral-Domain' :
    (x y : type-Integral-Domain) → type-Integral-Domain
  mul-Integral-Domain' =
    mul-Commutative-Ring' commutative-ring-Integral-Domain

  ap-mul-Integral-Domain :
    {x x' y y' : type-Integral-Domain} (p : x ＝ x') (q : y ＝ y') →
    mul-Integral-Domain x y ＝ mul-Integral-Domain x' y'
  ap-mul-Integral-Domain p q = ap-binary mul-Integral-Domain p q

  associative-mul-Integral-Domain :
    (x y z : type-Integral-Domain) →
    mul-Integral-Domain (mul-Integral-Domain x y) z ＝
    mul-Integral-Domain x (mul-Integral-Domain y z)
  associative-mul-Integral-Domain =
    associative-mul-Commutative-Ring commutative-ring-Integral-Domain

  multiplicative-semigroup-Integral-Domain : Semigroup l
  multiplicative-semigroup-Integral-Domain =
    multiplicative-semigroup-Commutative-Ring
      commutative-ring-Integral-Domain

  left-distributive-mul-add-Integral-Domain :
    (x y z : type-Integral-Domain) →
    ( mul-Integral-Domain x (add-Integral-Domain y z)) ＝
    ( add-Integral-Domain
      ( mul-Integral-Domain x y)
      ( mul-Integral-Domain x z))
  left-distributive-mul-add-Integral-Domain =
    left-distributive-mul-add-Commutative-Ring
      commutative-ring-Integral-Domain

  right-distributive-mul-add-Integral-Domain :
    (x y z : type-Integral-Domain) →
    ( mul-Integral-Domain (add-Integral-Domain x y) z) ＝
    ( add-Integral-Domain
      ( mul-Integral-Domain x z)
      ( mul-Integral-Domain y z))
  right-distributive-mul-add-Integral-Domain =
    right-distributive-mul-add-Commutative-Ring
      commutative-ring-Integral-Domain

  commutative-mul-Integral-Domain :
    (x y : type-Integral-Domain) →
    mul-Integral-Domain x y ＝ mul-Integral-Domain y x
  commutative-mul-Integral-Domain =
    commutative-mul-Commutative-Ring
      commutative-ring-Integral-Domain
```

### Multiplicative units in an integral domain

```agda
  is-unital-Integral-Domain : is-unital mul-Integral-Domain
  is-unital-Integral-Domain =
    is-unital-Commutative-Ring
      commutative-ring-Integral-Domain

  multiplicative-monoid-Integral-Domain : Monoid l
  multiplicative-monoid-Integral-Domain =
    multiplicative-monoid-Commutative-Ring
      commutative-ring-Integral-Domain

  one-Integral-Domain : type-Integral-Domain
  one-Integral-Domain =
    one-Commutative-Ring
      commutative-ring-Integral-Domain

  left-unit-law-mul-Integral-Domain :
    (x : type-Integral-Domain) →
    mul-Integral-Domain one-Integral-Domain x ＝ x
  left-unit-law-mul-Integral-Domain =
    left-unit-law-mul-Commutative-Ring
      commutative-ring-Integral-Domain

  right-unit-law-mul-Integral-Domain :
    (x : type-Integral-Domain) →
    mul-Integral-Domain x one-Integral-Domain ＝ x
  right-unit-law-mul-Integral-Domain =
    right-unit-law-mul-Commutative-Ring
      commutative-ring-Integral-Domain

  right-swap-mul-Integral-Domain :
    (x y z : type-Integral-Domain) →
    mul-Integral-Domain (mul-Integral-Domain x y) z ＝
    mul-Integral-Domain (mul-Integral-Domain x z) y
  right-swap-mul-Integral-Domain x y z =
    ( associative-mul-Integral-Domain x y z) ∙
    ( ( ap
        ( mul-Integral-Domain x)
        ( commutative-mul-Integral-Domain y z)) ∙
      ( inv (associative-mul-Integral-Domain x z y)))

  left-swap-mul-Integral-Domain :
    (x y z : type-Integral-Domain) →
    mul-Integral-Domain x (mul-Integral-Domain y z) ＝
    mul-Integral-Domain y (mul-Integral-Domain x z)
  left-swap-mul-Integral-Domain x y z =
    ( inv (associative-mul-Integral-Domain x y z)) ∙
    ( ( ap
        ( mul-Integral-Domain' z)
        ( commutative-mul-Integral-Domain x y)) ∙
      ( associative-mul-Integral-Domain y x z))

  interchange-mul-mul-Integral-Domain :
    (x y z w : type-Integral-Domain) →
    mul-Integral-Domain
      ( mul-Integral-Domain x y)
      ( mul-Integral-Domain z w) ＝
    mul-Integral-Domain
      ( mul-Integral-Domain x z)
      ( mul-Integral-Domain y w)
  interchange-mul-mul-Integral-Domain =
    interchange-law-commutative-and-associative
      mul-Integral-Domain
      commutative-mul-Integral-Domain
      associative-mul-Integral-Domain
```

### The zero laws for multiplication of a integral domains

```agda
  left-zero-law-mul-Integral-Domain :
    (x : type-Integral-Domain) →
    mul-Integral-Domain zero-Integral-Domain x ＝
    zero-Integral-Domain
  left-zero-law-mul-Integral-Domain =
    left-zero-law-mul-Commutative-Ring commutative-ring-Integral-Domain

  right-zero-law-mul-Integral-Domain :
    (x : type-Integral-Domain) →
    mul-Integral-Domain x zero-Integral-Domain ＝
    zero-Integral-Domain
  right-zero-law-mul-Integral-Domain =
    right-zero-law-mul-Commutative-Ring commutative-ring-Integral-Domain
```

### Integral domains are commutative semirings

```agda
  multiplicative-commutative-monoid-Integral-Domain : Commutative-Monoid l
  multiplicative-commutative-monoid-Integral-Domain =
    multiplicative-commutative-monoid-Commutative-Ring
      commutative-ring-Integral-Domain

  semiring-Integral-Domain : Semiring l
  semiring-Integral-Domain =
    semiring-Commutative-Ring commutative-ring-Integral-Domain

  commutative-semiring-Integral-Domain : Commutative-Semiring l
  commutative-semiring-Integral-Domain =
    commutative-semiring-Commutative-Ring
      commutative-ring-Integral-Domain
```

### Computing multiplication with minus one in an integral domain

```agda
  neg-one-Integral-Domain : type-Integral-Domain
  neg-one-Integral-Domain =
    neg-one-Commutative-Ring
      commutative-ring-Integral-Domain

  mul-neg-one-Integral-Domain :
    (x : type-Integral-Domain) →
    mul-Integral-Domain neg-one-Integral-Domain x ＝
    neg-Integral-Domain x
  mul-neg-one-Integral-Domain =
    mul-neg-one-Commutative-Ring
      commutative-ring-Integral-Domain

  mul-neg-one-Integral-Domain' :
    (x : type-Integral-Domain) →
    mul-Integral-Domain x neg-one-Integral-Domain ＝
    neg-Integral-Domain x
  mul-neg-one-Integral-Domain' =
    mul-neg-one-Commutative-Ring'
      commutative-ring-Integral-Domain

  is-involution-mul-neg-one-Integral-Domain :
    is-involution (mul-Integral-Domain neg-one-Integral-Domain)
  is-involution-mul-neg-one-Integral-Domain =
    is-involution-mul-neg-one-Commutative-Ring
      commutative-ring-Integral-Domain

  is-involution-mul-neg-one-Integral-Domain' :
    is-involution (mul-Integral-Domain' neg-one-Integral-Domain)
  is-involution-mul-neg-one-Integral-Domain' =
    is-involution-mul-neg-one-Commutative-Ring'
      commutative-ring-Integral-Domain
```

### Left and right negative laws for multiplication

```agda
  left-negative-law-mul-Integral-Domain :
    (x y : type-Integral-Domain) →
    mul-Integral-Domain (neg-Integral-Domain x) y ＝
    neg-Integral-Domain (mul-Integral-Domain x y)
  left-negative-law-mul-Integral-Domain =
    left-negative-law-mul-Commutative-Ring
      commutative-ring-Integral-Domain

  right-negative-law-mul-Integral-Domain :
    (x y : type-Integral-Domain) →
    mul-Integral-Domain x (neg-Integral-Domain y) ＝
    neg-Integral-Domain (mul-Integral-Domain x y)
  right-negative-law-mul-Integral-Domain =
    right-negative-law-mul-Commutative-Ring
      commutative-ring-Integral-Domain

  mul-neg-Integral-Domain :
    (x y : type-Integral-Domain) →
    mul-Integral-Domain (neg-Integral-Domain x) (neg-Integral-Domain y) ＝
    mul-Integral-Domain x y
  mul-neg-Integral-Domain =
    mul-neg-Commutative-Ring
      commutative-ring-Integral-Domain
```

### Scalar multiplication of elements of a integral domain by natural numbers

```agda
  mul-nat-scalar-Integral-Domain :
    ℕ → type-Integral-Domain → type-Integral-Domain
  mul-nat-scalar-Integral-Domain =
    mul-nat-scalar-Commutative-Ring
      commutative-ring-Integral-Domain

  ap-mul-nat-scalar-Integral-Domain :
    {m n : ℕ} {x y : type-Integral-Domain} →
    (m ＝ n) → (x ＝ y) →
    mul-nat-scalar-Integral-Domain m x ＝
    mul-nat-scalar-Integral-Domain n y
  ap-mul-nat-scalar-Integral-Domain =
    ap-mul-nat-scalar-Commutative-Ring
      commutative-ring-Integral-Domain

  left-zero-law-mul-nat-scalar-Integral-Domain :
    (x : type-Integral-Domain) →
    mul-nat-scalar-Integral-Domain 0 x ＝ zero-Integral-Domain
  left-zero-law-mul-nat-scalar-Integral-Domain =
    left-zero-law-mul-nat-scalar-Commutative-Ring
      commutative-ring-Integral-Domain

  right-zero-law-mul-nat-scalar-Integral-Domain :
    (n : ℕ) →
    mul-nat-scalar-Integral-Domain n zero-Integral-Domain ＝
    zero-Integral-Domain
  right-zero-law-mul-nat-scalar-Integral-Domain =
    right-zero-law-mul-nat-scalar-Commutative-Ring
      commutative-ring-Integral-Domain

  left-unit-law-mul-nat-scalar-Integral-Domain :
    (x : type-Integral-Domain) →
    mul-nat-scalar-Integral-Domain 1 x ＝ x
  left-unit-law-mul-nat-scalar-Integral-Domain =
    left-unit-law-mul-nat-scalar-Commutative-Ring
      commutative-ring-Integral-Domain

  left-nat-scalar-law-mul-Integral-Domain :
    (n : ℕ) (x y : type-Integral-Domain) →
    mul-Integral-Domain (mul-nat-scalar-Integral-Domain n x) y ＝
    mul-nat-scalar-Integral-Domain n (mul-Integral-Domain x y)
  left-nat-scalar-law-mul-Integral-Domain =
    left-nat-scalar-law-mul-Commutative-Ring
      commutative-ring-Integral-Domain

  right-nat-scalar-law-mul-Integral-Domain :
    (n : ℕ) (x y : type-Integral-Domain) →
    mul-Integral-Domain x (mul-nat-scalar-Integral-Domain n y) ＝
    mul-nat-scalar-Integral-Domain n (mul-Integral-Domain x y)
  right-nat-scalar-law-mul-Integral-Domain =
    right-nat-scalar-law-mul-Commutative-Ring
      commutative-ring-Integral-Domain

  left-distributive-mul-nat-scalar-add-Integral-Domain :
    (n : ℕ) (x y : type-Integral-Domain) →
    mul-nat-scalar-Integral-Domain n (add-Integral-Domain x y) ＝
    add-Integral-Domain
      ( mul-nat-scalar-Integral-Domain n x)
      ( mul-nat-scalar-Integral-Domain n y)
  left-distributive-mul-nat-scalar-add-Integral-Domain =
    left-distributive-mul-nat-scalar-add-Commutative-Ring
      commutative-ring-Integral-Domain

  right-distributive-mul-nat-scalar-add-Integral-Domain :
    (m n : ℕ) (x : type-Integral-Domain) →
    mul-nat-scalar-Integral-Domain (m +ℕ n) x ＝
    add-Integral-Domain
      ( mul-nat-scalar-Integral-Domain m x)
      ( mul-nat-scalar-Integral-Domain n x)
  right-distributive-mul-nat-scalar-add-Integral-Domain =
    right-distributive-mul-nat-scalar-add-Commutative-Ring
      commutative-ring-Integral-Domain
```

### Addition of a list of elements in an integral domain

```agda
  add-list-Integral-Domain :
    list type-Integral-Domain → type-Integral-Domain
  add-list-Integral-Domain =
    add-list-Commutative-Ring commutative-ring-Integral-Domain

  preserves-concat-add-list-Integral-Domain :
    (l1 l2 : list type-Integral-Domain) →
    add-list-Integral-Domain (concat-list l1 l2) ＝
    add-Integral-Domain
      ( add-list-Integral-Domain l1)
      ( add-list-Integral-Domain l2)
  preserves-concat-add-list-Integral-Domain =
    preserves-concat-add-list-Commutative-Ring
      commutative-ring-Integral-Domain
```
