# Euclidean domains

```agda
module commutative-algebra.euclidean-domains where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.commutative-semirings
open import commutative-algebra.integral-domains
open import commutative-algebra.trivial-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.cartesian-product-types
open import foundation.coproduct-types
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

A
{{#concept "Euclidean domain" Agda=Euclidean-Domain WDID=Q867345 WD="Euclidean domain"}}
is an [integral domain](commutative-algebra.integral-domains.md) `R` that has a
**Euclidean valuation**, i.e., a function `v : R → ℕ` such that for every
`x y : R`, if `y` is nonzero then there are `q r : R` with `x = q y + r` and
`v r < v y`.

## Definition

### The condition of being a Euclidean valuation

```agda
is-euclidean-valuation :
  { l : Level} (R : Integral-Domain l) →
  ( type-Integral-Domain R → ℕ) →
  UU l
is-euclidean-valuation R v =
  ( x y : type-Integral-Domain R) →
  ( is-nonzero-Integral-Domain R y) →
  Σ ( type-Integral-Domain R × type-Integral-Domain R)
    ( λ (q , r) →
      ( x ＝ add-Integral-Domain R (mul-Integral-Domain R q y) r) ×
        ( is-zero-Integral-Domain R r +
        ( v r <-ℕ v y)))
```

### The condition of being a Euclidean domain

```agda
is-euclidean-domain-Integral-Domain :
  { l : Level} (R : Integral-Domain l) → UU l
is-euclidean-domain-Integral-Domain R =
  Σ (type-Integral-Domain R → ℕ) (is-euclidean-valuation R)
```

### Euclidean domains

```agda
Euclidean-Domain : (l : Level) → UU (lsuc l)
Euclidean-Domain l =
  Σ (Integral-Domain l) is-euclidean-domain-Integral-Domain

module _
  {l : Level} (R : Euclidean-Domain l)
  where

  integral-domain-Euclidean-Domain : Integral-Domain l
  integral-domain-Euclidean-Domain = pr1 R

  is-euclidean-domain-Euclidean-Domain :
    is-euclidean-domain-Integral-Domain integral-domain-Euclidean-Domain
  is-euclidean-domain-Euclidean-Domain = pr2 R

  commutative-ring-Euclidean-Domain : Commutative-Ring l
  commutative-ring-Euclidean-Domain =
    commutative-ring-Integral-Domain integral-domain-Euclidean-Domain

  has-cancellation-property-Euclidean-Domain :
    cancellation-property-Commutative-Ring commutative-ring-Euclidean-Domain
  has-cancellation-property-Euclidean-Domain =
    has-cancellation-property-Integral-Domain
      integral-domain-Euclidean-Domain

  is-nontrivial-Euclidean-Domain :
    is-nontrivial-Commutative-Ring commutative-ring-Euclidean-Domain
  is-nontrivial-Euclidean-Domain =
    is-nontrivial-Integral-Domain
      integral-domain-Euclidean-Domain

  ab-Euclidean-Domain : Ab l
  ab-Euclidean-Domain =
    ab-Commutative-Ring commutative-ring-Euclidean-Domain

  ring-Euclidean-Domain : Ring l
  ring-Euclidean-Domain =
    ring-Integral-Domain integral-domain-Euclidean-Domain

  set-Euclidean-Domain : Set l
  set-Euclidean-Domain = set-Ring ring-Euclidean-Domain

  type-Euclidean-Domain : UU l
  type-Euclidean-Domain = type-Ring ring-Euclidean-Domain

  is-set-type-Euclidean-Domain : is-set type-Euclidean-Domain
  is-set-type-Euclidean-Domain = is-set-type-Ring ring-Euclidean-Domain
```

### Addition in a Euclidean domain

```agda
  has-associative-add-Euclidean-Domain :
    has-associative-mul-Set set-Euclidean-Domain
  has-associative-add-Euclidean-Domain =
    has-associative-add-Integral-Domain integral-domain-Euclidean-Domain

  add-Euclidean-Domain :
    type-Euclidean-Domain → type-Euclidean-Domain → type-Euclidean-Domain
  add-Euclidean-Domain = add-Integral-Domain integral-domain-Euclidean-Domain

  add-Euclidean-Domain' :
    type-Euclidean-Domain → type-Euclidean-Domain → type-Euclidean-Domain
  add-Euclidean-Domain' = add-Integral-Domain' integral-domain-Euclidean-Domain

  ap-add-Euclidean-Domain :
    {x x' y y' : type-Euclidean-Domain} →
    (x ＝ x') → (y ＝ y') →
    add-Euclidean-Domain x y ＝ add-Euclidean-Domain x' y'
  ap-add-Euclidean-Domain =
    ap-add-Integral-Domain integral-domain-Euclidean-Domain

  associative-add-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    ( add-Euclidean-Domain (add-Euclidean-Domain x y) z) ＝
    ( add-Euclidean-Domain x (add-Euclidean-Domain y z))
  associative-add-Euclidean-Domain =
    associative-add-Integral-Domain integral-domain-Euclidean-Domain

  additive-semigroup-Euclidean-Domain : Semigroup l
  additive-semigroup-Euclidean-Domain = semigroup-Ab ab-Euclidean-Domain

  is-group-additive-semigroup-Euclidean-Domain :
    is-group-Semigroup additive-semigroup-Euclidean-Domain
  is-group-additive-semigroup-Euclidean-Domain =
    is-group-Ab ab-Euclidean-Domain

  commutative-add-Euclidean-Domain :
    (x y : type-Euclidean-Domain) →
    add-Euclidean-Domain x y ＝ add-Euclidean-Domain y x
  commutative-add-Euclidean-Domain = commutative-add-Ab ab-Euclidean-Domain

  interchange-add-add-Euclidean-Domain :
    (x y x' y' : type-Euclidean-Domain) →
    ( add-Euclidean-Domain
      ( add-Euclidean-Domain x y)
      ( add-Euclidean-Domain x' y')) ＝
    ( add-Euclidean-Domain
      ( add-Euclidean-Domain x x')
      ( add-Euclidean-Domain y y'))
  interchange-add-add-Euclidean-Domain =
    interchange-add-add-Integral-Domain integral-domain-Euclidean-Domain

  right-swap-add-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    ( add-Euclidean-Domain (add-Euclidean-Domain x y) z) ＝
    ( add-Euclidean-Domain (add-Euclidean-Domain x z) y)
  right-swap-add-Euclidean-Domain =
    right-swap-add-Integral-Domain integral-domain-Euclidean-Domain

  left-swap-add-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    ( add-Euclidean-Domain x (add-Euclidean-Domain y z)) ＝
    ( add-Euclidean-Domain y (add-Euclidean-Domain x z))
  left-swap-add-Euclidean-Domain =
    left-swap-add-Integral-Domain integral-domain-Euclidean-Domain

  is-equiv-add-Euclidean-Domain :
    (x : type-Euclidean-Domain) → is-equiv (add-Euclidean-Domain x)
  is-equiv-add-Euclidean-Domain = is-equiv-add-Ab ab-Euclidean-Domain

  is-equiv-add-Euclidean-Domain' :
    (x : type-Euclidean-Domain) → is-equiv (add-Euclidean-Domain' x)
  is-equiv-add-Euclidean-Domain' = is-equiv-add-Ab' ab-Euclidean-Domain

  is-binary-equiv-add-Euclidean-Domain : is-binary-equiv add-Euclidean-Domain
  pr1 is-binary-equiv-add-Euclidean-Domain = is-equiv-add-Euclidean-Domain'
  pr2 is-binary-equiv-add-Euclidean-Domain = is-equiv-add-Euclidean-Domain

  is-binary-emb-add-Euclidean-Domain : is-binary-emb add-Euclidean-Domain
  is-binary-emb-add-Euclidean-Domain = is-binary-emb-add-Ab ab-Euclidean-Domain

  is-emb-add-Euclidean-Domain :
    (x : type-Euclidean-Domain) → is-emb (add-Euclidean-Domain x)
  is-emb-add-Euclidean-Domain = is-emb-add-Ab ab-Euclidean-Domain

  is-emb-add-Euclidean-Domain' :
    (x : type-Euclidean-Domain) → is-emb (add-Euclidean-Domain' x)
  is-emb-add-Euclidean-Domain' = is-emb-add-Ab' ab-Euclidean-Domain

  is-injective-add-Euclidean-Domain :
    (x : type-Euclidean-Domain) → is-injective (add-Euclidean-Domain x)
  is-injective-add-Euclidean-Domain = is-injective-add-Ab ab-Euclidean-Domain

  is-injective-add-Euclidean-Domain' :
    (x : type-Euclidean-Domain) → is-injective (add-Euclidean-Domain' x)
  is-injective-add-Euclidean-Domain' = is-injective-add-Ab' ab-Euclidean-Domain
```

### The zero element of a Euclidean domain

```agda
  has-zero-Euclidean-Domain : is-unital add-Euclidean-Domain
  has-zero-Euclidean-Domain =
    has-zero-Integral-Domain integral-domain-Euclidean-Domain

  zero-Euclidean-Domain : type-Euclidean-Domain
  zero-Euclidean-Domain =
    zero-Integral-Domain integral-domain-Euclidean-Domain

  is-zero-Euclidean-Domain : type-Euclidean-Domain → UU l
  is-zero-Euclidean-Domain =
    is-zero-Integral-Domain integral-domain-Euclidean-Domain

  is-nonzero-Euclidean-Domain : type-Euclidean-Domain → UU l
  is-nonzero-Euclidean-Domain =
    is-nonzero-Integral-Domain integral-domain-Euclidean-Domain

  is-zero-euclidean-domain-Prop : type-Euclidean-Domain → Prop l
  is-zero-euclidean-domain-Prop x =
    Id-Prop set-Euclidean-Domain x zero-Euclidean-Domain

  is-nonzero-euclidean-domain-Prop : type-Euclidean-Domain → Prop l
  is-nonzero-euclidean-domain-Prop x =
    neg-Prop (is-zero-euclidean-domain-Prop x)

  left-unit-law-add-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    add-Euclidean-Domain zero-Euclidean-Domain x ＝ x
  left-unit-law-add-Euclidean-Domain =
    left-unit-law-add-Integral-Domain integral-domain-Euclidean-Domain

  right-unit-law-add-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    add-Euclidean-Domain x zero-Euclidean-Domain ＝ x
  right-unit-law-add-Euclidean-Domain =
    right-unit-law-add-Integral-Domain integral-domain-Euclidean-Domain
```

### Additive inverses in a Euclidean domain

```agda
  has-negatives-Euclidean-Domain :
    is-group-is-unital-Semigroup
      ( additive-semigroup-Euclidean-Domain)
      ( has-zero-Euclidean-Domain)
  has-negatives-Euclidean-Domain = has-negatives-Ab ab-Euclidean-Domain

  neg-Euclidean-Domain : type-Euclidean-Domain → type-Euclidean-Domain
  neg-Euclidean-Domain = neg-Integral-Domain integral-domain-Euclidean-Domain

  left-inverse-law-add-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    add-Euclidean-Domain (neg-Euclidean-Domain x) x ＝ zero-Euclidean-Domain
  left-inverse-law-add-Euclidean-Domain =
    left-inverse-law-add-Integral-Domain integral-domain-Euclidean-Domain

  right-inverse-law-add-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    add-Euclidean-Domain x (neg-Euclidean-Domain x) ＝ zero-Euclidean-Domain
  right-inverse-law-add-Euclidean-Domain =
    right-inverse-law-add-Integral-Domain integral-domain-Euclidean-Domain

  neg-neg-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    neg-Euclidean-Domain (neg-Euclidean-Domain x) ＝ x
  neg-neg-Euclidean-Domain = neg-neg-Ab ab-Euclidean-Domain

  distributive-neg-add-Euclidean-Domain :
    (x y : type-Euclidean-Domain) →
    neg-Euclidean-Domain (add-Euclidean-Domain x y) ＝
    add-Euclidean-Domain (neg-Euclidean-Domain x) (neg-Euclidean-Domain y)
  distributive-neg-add-Euclidean-Domain =
    distributive-neg-add-Ab ab-Euclidean-Domain
```

### Multiplication in a Euclidean domain

```agda
  has-associative-mul-Euclidean-Domain :
    has-associative-mul-Set set-Euclidean-Domain
  has-associative-mul-Euclidean-Domain =
    has-associative-mul-Integral-Domain integral-domain-Euclidean-Domain

  mul-Euclidean-Domain :
    (x y : type-Euclidean-Domain) → type-Euclidean-Domain
  mul-Euclidean-Domain =
    mul-Integral-Domain integral-domain-Euclidean-Domain

  mul-Euclidean-Domain' :
    (x y : type-Euclidean-Domain) → type-Euclidean-Domain
  mul-Euclidean-Domain' =
    mul-Integral-Domain' integral-domain-Euclidean-Domain

  ap-mul-Euclidean-Domain :
    {x x' y y' : type-Euclidean-Domain} (p : x ＝ x') (q : y ＝ y') →
    mul-Euclidean-Domain x y ＝ mul-Euclidean-Domain x' y'
  ap-mul-Euclidean-Domain p q = ap-binary mul-Euclidean-Domain p q

  associative-mul-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    mul-Euclidean-Domain (mul-Euclidean-Domain x y) z ＝
    mul-Euclidean-Domain x (mul-Euclidean-Domain y z)
  associative-mul-Euclidean-Domain =
    associative-mul-Integral-Domain integral-domain-Euclidean-Domain

  multiplicative-semigroup-Euclidean-Domain : Semigroup l
  multiplicative-semigroup-Euclidean-Domain =
    multiplicative-semigroup-Integral-Domain
      integral-domain-Euclidean-Domain

  left-distributive-mul-add-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    mul-Euclidean-Domain x (add-Euclidean-Domain y z) ＝
    add-Euclidean-Domain (mul-Euclidean-Domain x y) (mul-Euclidean-Domain x z)
  left-distributive-mul-add-Euclidean-Domain =
    left-distributive-mul-add-Integral-Domain
      integral-domain-Euclidean-Domain

  right-distributive-mul-add-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    mul-Euclidean-Domain (add-Euclidean-Domain x y) z ＝
    add-Euclidean-Domain (mul-Euclidean-Domain x z) (mul-Euclidean-Domain y z)
  right-distributive-mul-add-Euclidean-Domain =
    right-distributive-mul-add-Integral-Domain
      integral-domain-Euclidean-Domain

  commutative-mul-Euclidean-Domain :
    (x y : type-Euclidean-Domain) →
    mul-Euclidean-Domain x y ＝ mul-Euclidean-Domain y x
  commutative-mul-Euclidean-Domain =
    commutative-mul-Integral-Domain
      integral-domain-Euclidean-Domain
```

### Multiplicative units in a Euclidean domain

```agda
  is-unital-Euclidean-Domain : is-unital mul-Euclidean-Domain
  is-unital-Euclidean-Domain =
    is-unital-Integral-Domain
      integral-domain-Euclidean-Domain

  multiplicative-monoid-Euclidean-Domain : Monoid l
  multiplicative-monoid-Euclidean-Domain =
    multiplicative-monoid-Integral-Domain
      integral-domain-Euclidean-Domain

  one-Euclidean-Domain : type-Euclidean-Domain
  one-Euclidean-Domain =
    one-Integral-Domain
      integral-domain-Euclidean-Domain

  left-unit-law-mul-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    mul-Euclidean-Domain one-Euclidean-Domain x ＝ x
  left-unit-law-mul-Euclidean-Domain =
    left-unit-law-mul-Integral-Domain
      integral-domain-Euclidean-Domain

  right-unit-law-mul-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    mul-Euclidean-Domain x one-Euclidean-Domain ＝ x
  right-unit-law-mul-Euclidean-Domain =
    right-unit-law-mul-Integral-Domain
      integral-domain-Euclidean-Domain

  right-swap-mul-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    mul-Euclidean-Domain (mul-Euclidean-Domain x y) z ＝
    mul-Euclidean-Domain (mul-Euclidean-Domain x z) y
  right-swap-mul-Euclidean-Domain x y z =
    ( associative-mul-Euclidean-Domain x y z) ∙
    ( ( ap
        ( mul-Euclidean-Domain x)
        ( commutative-mul-Euclidean-Domain y z)) ∙
      ( inv (associative-mul-Euclidean-Domain x z y)))

  left-swap-mul-Euclidean-Domain :
    (x y z : type-Euclidean-Domain) →
    mul-Euclidean-Domain x (mul-Euclidean-Domain y z) ＝
    mul-Euclidean-Domain y (mul-Euclidean-Domain x z)
  left-swap-mul-Euclidean-Domain x y z =
    ( inv (associative-mul-Euclidean-Domain x y z)) ∙
    ( ( ap
        ( mul-Euclidean-Domain' z)
        ( commutative-mul-Euclidean-Domain x y)) ∙
      ( associative-mul-Euclidean-Domain y x z))

  interchange-mul-mul-Euclidean-Domain :
    (x y z w : type-Euclidean-Domain) →
    mul-Euclidean-Domain
      ( mul-Euclidean-Domain x y)
      ( mul-Euclidean-Domain z w) ＝
    mul-Euclidean-Domain
      ( mul-Euclidean-Domain x z)
      ( mul-Euclidean-Domain y w)
  interchange-mul-mul-Euclidean-Domain =
    interchange-law-commutative-and-associative
      mul-Euclidean-Domain
      commutative-mul-Euclidean-Domain
      associative-mul-Euclidean-Domain
```

### The zero laws for multiplication of a Euclidean domain

```agda
  left-zero-law-mul-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    mul-Euclidean-Domain zero-Euclidean-Domain x ＝
    zero-Euclidean-Domain
  left-zero-law-mul-Euclidean-Domain =
    left-zero-law-mul-Integral-Domain integral-domain-Euclidean-Domain

  right-zero-law-mul-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    mul-Euclidean-Domain x zero-Euclidean-Domain ＝
    zero-Euclidean-Domain
  right-zero-law-mul-Euclidean-Domain =
    right-zero-law-mul-Integral-Domain integral-domain-Euclidean-Domain
```

### Euclidean domains are commutative semirings

```agda
  multiplicative-commutative-monoid-Euclidean-Domain : Commutative-Monoid l
  multiplicative-commutative-monoid-Euclidean-Domain =
    multiplicative-commutative-monoid-Integral-Domain
      integral-domain-Euclidean-Domain

  semiring-Euclidean-Domain : Semiring l
  semiring-Euclidean-Domain =
    semiring-Integral-Domain integral-domain-Euclidean-Domain

  commutative-semiring-Euclidean-Domain : Commutative-Semiring l
  commutative-semiring-Euclidean-Domain =
    commutative-semiring-Integral-Domain
      integral-domain-Euclidean-Domain
```

### Computing multiplication with minus one in a Euclidean domain

```agda
  neg-one-Euclidean-Domain : type-Euclidean-Domain
  neg-one-Euclidean-Domain =
    neg-one-Integral-Domain
      integral-domain-Euclidean-Domain

  mul-neg-one-Euclidean-Domain :
    (x : type-Euclidean-Domain) →
    mul-Euclidean-Domain neg-one-Euclidean-Domain x ＝
    neg-Euclidean-Domain x
  mul-neg-one-Euclidean-Domain =
    mul-neg-one-Integral-Domain
      integral-domain-Euclidean-Domain

  mul-neg-one-Euclidean-Domain' :
    (x : type-Euclidean-Domain) →
    mul-Euclidean-Domain x neg-one-Euclidean-Domain ＝
    neg-Euclidean-Domain x
  mul-neg-one-Euclidean-Domain' =
    mul-neg-one-Integral-Domain'
      integral-domain-Euclidean-Domain

  is-involution-mul-neg-one-Euclidean-Domain :
    is-involution (mul-Euclidean-Domain neg-one-Euclidean-Domain)
  is-involution-mul-neg-one-Euclidean-Domain =
    is-involution-mul-neg-one-Integral-Domain
      integral-domain-Euclidean-Domain

  is-involution-mul-neg-one-Euclidean-Domain' :
    is-involution (mul-Euclidean-Domain' neg-one-Euclidean-Domain)
  is-involution-mul-neg-one-Euclidean-Domain' =
    is-involution-mul-neg-one-Integral-Domain'
      integral-domain-Euclidean-Domain
```

### Left and right negative laws for multiplication

```agda
  left-negative-law-mul-Euclidean-Domain :
    (x y : type-Euclidean-Domain) →
    mul-Euclidean-Domain (neg-Euclidean-Domain x) y ＝
    neg-Euclidean-Domain (mul-Euclidean-Domain x y)
  left-negative-law-mul-Euclidean-Domain =
    left-negative-law-mul-Integral-Domain
      integral-domain-Euclidean-Domain

  right-negative-law-mul-Euclidean-Domain :
    (x y : type-Euclidean-Domain) →
    mul-Euclidean-Domain x (neg-Euclidean-Domain y) ＝
    neg-Euclidean-Domain (mul-Euclidean-Domain x y)
  right-negative-law-mul-Euclidean-Domain =
    right-negative-law-mul-Integral-Domain
      integral-domain-Euclidean-Domain

  mul-neg-Euclidean-Domain :
    (x y : type-Euclidean-Domain) →
    mul-Euclidean-Domain (neg-Euclidean-Domain x) (neg-Euclidean-Domain y) ＝
    mul-Euclidean-Domain x y
  mul-neg-Euclidean-Domain =
    mul-neg-Integral-Domain
      integral-domain-Euclidean-Domain
```

### Addition of a list of elements in a Euclidean domain

```agda
  add-list-Euclidean-Domain :
    list type-Euclidean-Domain → type-Euclidean-Domain
  add-list-Euclidean-Domain =
    add-list-Integral-Domain integral-domain-Euclidean-Domain

  preserves-concat-add-list-Euclidean-Domain :
    (l1 l2 : list type-Euclidean-Domain) →
    add-list-Euclidean-Domain (concat-list l1 l2) ＝
    add-Euclidean-Domain
      ( add-list-Euclidean-Domain l1)
      ( add-list-Euclidean-Domain l2)
  preserves-concat-add-list-Euclidean-Domain =
    preserves-concat-add-list-Integral-Domain
      integral-domain-Euclidean-Domain
```

### Euclidean division in a Euclidean domain

```agda
  euclidean-valuation-Euclidean-Domain :
    type-Euclidean-Domain → ℕ
  euclidean-valuation-Euclidean-Domain =
    pr1 is-euclidean-domain-Euclidean-Domain

  euclidean-division-Euclidean-Domain :
    ( x y : type-Euclidean-Domain) →
    ( is-nonzero-Euclidean-Domain y) →
    type-Euclidean-Domain × type-Euclidean-Domain
  euclidean-division-Euclidean-Domain x y p =
    pr1 (pr2 is-euclidean-domain-Euclidean-Domain x y p)

  quotient-euclidean-division-Euclidean-Domain :
    ( x y : type-Euclidean-Domain) →
    ( is-nonzero-Euclidean-Domain y) →
    type-Euclidean-Domain
  quotient-euclidean-division-Euclidean-Domain x y p =
    pr1 (euclidean-division-Euclidean-Domain x y p)

  remainder-euclidean-division-Euclidean-Domain :
    ( x y : type-Euclidean-Domain) →
    ( is-nonzero-Euclidean-Domain y) →
    type-Euclidean-Domain
  remainder-euclidean-division-Euclidean-Domain x y p =
    pr2 (euclidean-division-Euclidean-Domain x y p)

  equation-euclidean-division-Euclidean-Domain :
    ( x y : type-Euclidean-Domain) →
    ( p : is-nonzero-Euclidean-Domain y) →
    x ＝
    add-Euclidean-Domain
      ( mul-Euclidean-Domain
        ( quotient-euclidean-division-Euclidean-Domain x y p)
        ( y))
      ( remainder-euclidean-division-Euclidean-Domain x y p)
  equation-euclidean-division-Euclidean-Domain x y p =
    pr1 (pr2 (pr2 is-euclidean-domain-Euclidean-Domain x y p))

  remainder-condition-euclidean-division-Euclidean-Domain :
    ( x y : type-Euclidean-Domain) →
    ( p : is-nonzero-Integral-Domain integral-domain-Euclidean-Domain y) →
    ( is-zero-Euclidean-Domain
      ( remainder-euclidean-division-Euclidean-Domain x y p)) +
    ( euclidean-valuation-Euclidean-Domain
      ( remainder-euclidean-division-Euclidean-Domain x y p) <-ℕ
    ( euclidean-valuation-Euclidean-Domain y))
  remainder-condition-euclidean-division-Euclidean-Domain x y p =
    pr2 (pr2 (pr2 is-euclidean-domain-Euclidean-Domain x y p))
```
