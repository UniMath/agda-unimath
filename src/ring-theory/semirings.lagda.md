#  Semirings

```agda
module ring-theory.semirings where

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

open import univalent-combinatorics.lists
```

## Idea

The concept of ring vastly generalizes the arithmetical structure on the integers. A ring consists of a set equipped with additian and multiplication, where the addition operation gives the ring the structure of an abelian group, and the multiplication is associative, unital, and distributive over addition.

## Definitions

### Rings

```agda
has-mul-Commutative-Monoid :
  {l1 : Level} → Commutative-Monoid l1 → UU l1
has-mul-Commutative-Monoid M =
  Σ ( has-associative-mul-Set (set-Commutative-Monoid M))
    ( λ μ →
      ( is-unital (pr1 μ)) ×
      ( ( (a b c : type-Commutative-Monoid M) →
          pr1 μ a (mul-Commutative-Monoid M b c) ＝
          mul-Commutative-Monoid M (pr1 μ a b) (pr1 μ a c)) ×
        ( (a b c : type-Commutative-Monoid M) →
          pr1 μ (mul-Commutative-Monoid M a b) c ＝
          mul-Commutative-Monoid M (pr1 μ a c) (pr1 μ b c))))

Semiring : (l1 : Level) → UU (lsuc l1)
Semiring l1 = Σ (Commutative-Monoid l1) has-mul-Commutative-Monoid

module _
  {l : Level} (R : Semiring l)
  where

  commutative-monoid-Semiring : Commutative-Monoid l
  commutative-monoid-Semiring = pr1 R

  monoid-Semiring : Monoid l
  monoid-Semiring = monoid-Commutative-Monoid commutative-monoid-Semiring

  semigroup-Semiring : Semigroup l
  semigroup-Semiring =
    semigroup-Commutative-Monoid commutative-monoid-Semiring

  set-Semiring : Set l
  set-Semiring = set-Commutative-Monoid commutative-monoid-Semiring

  type-Semiring : UU l
  type-Semiring = type-Commutative-Monoid commutative-monoid-Semiring

  is-set-type-Semiring : is-set type-Semiring
  is-set-type-Semiring =
    is-set-type-Commutative-Monoid commutative-monoid-Semiring
```

### Addition in a ring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  has-associative-add-Semiring : has-associative-mul-Set (set-Semiring R)
  has-associative-add-Semiring =
    has-associative-mul-Commutative-Monoid (commutative-monoid-Semiring R)

  add-Semiring : type-Semiring R → type-Semiring R → type-Semiring R
  add-Semiring = mul-Commutative-Monoid (commutative-monoid-Semiring R)

  add-Semiring' : type-Semiring R → type-Semiring R → type-Semiring R
  add-Semiring' = mul-Commutative-Monoid' (commutative-monoid-Semiring R)

  ap-add-Semiring :
    {x y x' y' : type-Semiring R} →
    x ＝ x' → y ＝ y' → add-Semiring x y ＝ add-Semiring x' y'
  ap-add-Semiring = ap-mul-Commutative-Monoid (commutative-monoid-Semiring R)

  associative-add-Semiring :
    (x y z : type-Semiring R) →
    add-Semiring (add-Semiring x y) z ＝ add-Semiring x (add-Semiring y z)
  associative-add-Semiring =
    associative-mul-Commutative-Monoid (commutative-monoid-Semiring R)

  additive-semigroup-Semiring : Semigroup l
  additive-semigroup-Semiring =
    semigroup-Commutative-Monoid (commutative-monoid-Semiring R)

  commutative-add-Semiring :
    (x y : type-Semiring R) → add-Semiring x y ＝ add-Semiring y x
  commutative-add-Semiring =
    commutative-mul-Commutative-Monoid (commutative-monoid-Semiring R)

  interchange-add-add-Semiring :
    (x y x' y' : type-Semiring R) →
    ( add-Semiring (add-Semiring x y) (add-Semiring x' y')) ＝
    ( add-Semiring (add-Semiring x x') (add-Semiring y y'))
  interchange-add-add-Semiring =
    interchange-mul-mul-Commutative-Monoid (commutative-monoid-Semiring R)

  right-swap-add-Semiring :
    (x y z : type-Semiring R) →
    add-Semiring (add-Semiring x y) z ＝ add-Semiring (add-Semiring x z) y
  right-swap-add-Semiring =
    right-swap-mul-Commutative-Monoid (commutative-monoid-Semiring R)

  left-swap-add-Semiring :
    (x y z : type-Semiring R) →
    add-Semiring x (add-Semiring y z) ＝ add-Semiring y (add-Semiring x z)
  left-swap-add-Semiring =
    left-swap-mul-Commutative-Monoid (commutative-monoid-Semiring R)
```

### The zero element of a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  has-zero-Semiring : is-unital (add-Semiring R)
  has-zero-Semiring =
    has-unit-Commutative-Monoid (commutative-monoid-Semiring R)

  zero-Semiring : type-Semiring R
  zero-Semiring = unit-Commutative-Monoid (commutative-monoid-Semiring R)

  is-zero-Semiring : type-Semiring R → UU l
  is-zero-Semiring x = Id x zero-Semiring

  is-nonzero-Semiring : type-Semiring R → UU l
  is-nonzero-Semiring x = ¬ (is-zero-Semiring x)

  is-zero-semiring-Prop : type-Semiring R → Prop l
  is-zero-semiring-Prop x = Id-Prop (set-Semiring R) x zero-Semiring

  left-unit-law-add-Semiring :
    (x : type-Semiring R) → Id (add-Semiring R zero-Semiring x) x
  left-unit-law-add-Semiring =
    left-unit-law-mul-Commutative-Monoid (commutative-monoid-Semiring R)

  right-unit-law-add-Semiring :
    (x : type-Semiring R) → Id (add-Semiring R x zero-Semiring) x
  right-unit-law-add-Semiring =
    right-unit-law-mul-Commutative-Monoid (commutative-monoid-Semiring R)
```

### Multiplication in a semiring

```
module _
  {l : Level} (R : Semiring l)
  where
  
  has-associative-mul-Semiring : has-associative-mul-Set (set-Semiring R)
  has-associative-mul-Semiring = pr1 (pr2 R)

  mul-Semiring : type-Semiring R → type-Semiring R → type-Semiring R
  mul-Semiring = pr1 has-associative-mul-Semiring

  mul-Semiring' : type-Semiring R → type-Semiring R → type-Semiring R
  mul-Semiring' x y = mul-Semiring y x

  ap-mul-Semiring :
    {x x' y y' : type-Semiring R} (p : Id x x') (q : Id y y') →
    Id (mul-Semiring x y) (mul-Semiring x' y')
  ap-mul-Semiring p q = ap-binary mul-Semiring p q

  associative-mul-Semiring :
    (x y z : type-Semiring R) →
    Id (mul-Semiring (mul-Semiring x y) z) (mul-Semiring x (mul-Semiring y z))
  associative-mul-Semiring = pr2 has-associative-mul-Semiring
  
  multiplicative-semigroup-Semiring : Semigroup l
  pr1 multiplicative-semigroup-Semiring = set-Semiring R
  pr2 multiplicative-semigroup-Semiring = has-associative-mul-Semiring

  left-distributive-mul-add-Semiring :
    (x y z : type-Semiring R) →
    mul-Semiring x (add-Semiring R y z) ＝
    add-Semiring R (mul-Semiring x y) (mul-Semiring x z)
  left-distributive-mul-add-Semiring =
    pr1 (pr2 (pr2 (pr2 R)))

  right-distributive-mul-add-Semiring :
    (x y z : type-Semiring R) →
    Id ( mul-Semiring (add-Semiring R x y) z)
      ( add-Semiring R (mul-Semiring x z) (mul-Semiring y z))
  right-distributive-mul-add-Semiring =
    pr2 (pr2 (pr2 (pr2 R)))
```

### Multiplicative units in a ring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  is-unital-Semiring : is-unital (mul-Semiring R)
  is-unital-Semiring = pr1 (pr2 (pr2 R))

  multiplicative-monoid-Semiring : Monoid l
  pr1 multiplicative-monoid-Semiring = multiplicative-semigroup-Semiring R
  pr2 multiplicative-monoid-Semiring = is-unital-Semiring

  one-Semiring : type-Semiring R
  one-Semiring = unit-Monoid multiplicative-monoid-Semiring

  left-unit-law-mul-Semiring :
    (x : type-Semiring R) → Id (mul-Semiring R one-Semiring x) x
  left-unit-law-mul-Semiring =
    left-unit-law-mul-Monoid multiplicative-monoid-Semiring

  right-unit-law-mul-Semiring :
    (x : type-Semiring R) → Id (mul-Semiring R x one-Semiring) x
  right-unit-law-mul-Semiring =
    right-unit-law-mul-Monoid multiplicative-monoid-Semiring
```
