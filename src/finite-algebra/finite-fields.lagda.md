# Finite fields

```agda
module finite-algebra.finite-fields where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-algebra.commutative-finite-rings
open import finite-algebra.finite-rings

open import foundation.action-on-identifications-binary-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
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

open import ring-theory.division-rings
open import ring-theory.rings
open import ring-theory.semirings
```

</details>

## Idea

A **discrete field** is a commutative division ring. They are called discrete,
because only nonzero elements are assumed to be invertible.

## Definition

```agda
is-finite-field-Finite-Commutative-Ring :
  {l : Level} → Finite-Commutative-Ring l → UU l
is-finite-field-Finite-Commutative-Ring A =
  is-division-Ring (ring-Finite-Commutative-Ring A)

Finite-Field : (l : Level) → UU (lsuc l)
Finite-Field l =
  Σ ( Finite-Commutative-Ring l)
    ( λ A → is-finite-field-Finite-Commutative-Ring A)

module _
  {l : Level} (A : Finite-Field l)
  where

  commutative-finite-ring-Finite-Field : Finite-Commutative-Ring l
  commutative-finite-ring-Finite-Field = pr1 A

  commutative-ring-Finite-Field : Commutative-Ring l
  commutative-ring-Finite-Field =
    commutative-ring-Finite-Commutative-Ring
      commutative-finite-ring-Finite-Field

  finite-ring-Finite-Field : Finite-Ring l
  finite-ring-Finite-Field =
    finite-ring-Finite-Commutative-Ring commutative-finite-ring-Finite-Field

  ring-Finite-Field : Ring l
  ring-Finite-Field = ring-Finite-Ring (finite-ring-Finite-Field)

  ab-Finite-Field : Ab l
  ab-Finite-Field = ab-Finite-Ring finite-ring-Finite-Field

  set-Finite-Field : Set l
  set-Finite-Field = set-Finite-Ring finite-ring-Finite-Field

  type-Finite-Field : UU l
  type-Finite-Field = type-Finite-Ring finite-ring-Finite-Field

  is-set-type-Finite-Field : is-set type-Finite-Field
  is-set-type-Finite-Field = is-set-type-Finite-Ring finite-ring-Finite-Field
```

### Addition in a finite field

```agda
  has-associative-add-Finite-Field :
    has-associative-mul-Set set-Finite-Field
  has-associative-add-Finite-Field =
    has-associative-add-Finite-Ring finite-ring-Finite-Field

  add-Finite-Field :
    type-Finite-Field → type-Finite-Field → type-Finite-Field
  add-Finite-Field = add-Finite-Ring finite-ring-Finite-Field

  add-Finite-Field' :
    type-Finite-Field → type-Finite-Field → type-Finite-Field
  add-Finite-Field' = add-Finite-Ring' finite-ring-Finite-Field

  ap-add-Finite-Field :
    {x x' y y' : type-Finite-Field} →
    (x ＝ x') → (y ＝ y') →
    add-Finite-Field x y ＝ add-Finite-Field x' y'
  ap-add-Finite-Field = ap-add-Finite-Ring finite-ring-Finite-Field

  associative-add-Finite-Field :
    (x y z : type-Finite-Field) →
    ( add-Finite-Field (add-Finite-Field x y) z) ＝
    ( add-Finite-Field x (add-Finite-Field y z))
  associative-add-Finite-Field =
    associative-add-Finite-Ring finite-ring-Finite-Field

  additive-semigroup-Finite-Field : Semigroup l
  additive-semigroup-Finite-Field = semigroup-Ab ab-Finite-Field

  is-group-additive-semigroup-Finite-Field :
    is-group-Semigroup additive-semigroup-Finite-Field
  is-group-additive-semigroup-Finite-Field =
    is-group-Ab ab-Finite-Field

  commutative-add-Finite-Field :
    (x y : type-Finite-Field) →
    Id (add-Finite-Field x y) (add-Finite-Field y x)
  commutative-add-Finite-Field = commutative-add-Ab ab-Finite-Field

  interchange-add-add-Finite-Field :
    (x y x' y' : type-Finite-Field) →
    ( add-Finite-Field
      ( add-Finite-Field x y)
      ( add-Finite-Field x' y')) ＝
    ( add-Finite-Field
      ( add-Finite-Field x x')
      ( add-Finite-Field y y'))
  interchange-add-add-Finite-Field =
    interchange-add-add-Finite-Ring finite-ring-Finite-Field

  right-swap-add-Finite-Field :
    (x y z : type-Finite-Field) →
    ( add-Finite-Field (add-Finite-Field x y) z) ＝
    ( add-Finite-Field (add-Finite-Field x z) y)
  right-swap-add-Finite-Field =
    right-swap-add-Finite-Ring finite-ring-Finite-Field

  left-swap-add-Finite-Field :
    (x y z : type-Finite-Field) →
    ( add-Finite-Field x (add-Finite-Field y z)) ＝
    ( add-Finite-Field y (add-Finite-Field x z))
  left-swap-add-Finite-Field =
    left-swap-add-Finite-Ring finite-ring-Finite-Field

  is-equiv-add-Finite-Field :
    (x : type-Finite-Field) → is-equiv (add-Finite-Field x)
  is-equiv-add-Finite-Field = is-equiv-add-Ab ab-Finite-Field

  is-equiv-add-Finite-Field' :
    (x : type-Finite-Field) → is-equiv (add-Finite-Field' x)
  is-equiv-add-Finite-Field' = is-equiv-add-Ab' ab-Finite-Field

  is-binary-equiv-add-Finite-Field : is-binary-equiv add-Finite-Field
  pr1 is-binary-equiv-add-Finite-Field = is-equiv-add-Finite-Field'
  pr2 is-binary-equiv-add-Finite-Field = is-equiv-add-Finite-Field

  is-binary-emb-add-Finite-Field : is-binary-emb add-Finite-Field
  is-binary-emb-add-Finite-Field = is-binary-emb-add-Ab ab-Finite-Field

  is-emb-add-Finite-Field :
    (x : type-Finite-Field) → is-emb (add-Finite-Field x)
  is-emb-add-Finite-Field = is-emb-add-Ab ab-Finite-Field

  is-emb-add-Finite-Field' :
    (x : type-Finite-Field) → is-emb (add-Finite-Field' x)
  is-emb-add-Finite-Field' = is-emb-add-Ab' ab-Finite-Field

  is-injective-add-Finite-Field :
    (x : type-Finite-Field) → is-injective (add-Finite-Field x)
  is-injective-add-Finite-Field = is-injective-add-Ab ab-Finite-Field

  is-injective-add-Finite-Field' :
    (x : type-Finite-Field) → is-injective (add-Finite-Field' x)
  is-injective-add-Finite-Field' = is-injective-add-Ab' ab-Finite-Field
```

### The zero element of a finite field

```agda
  has-zero-Finite-Field : is-unital add-Finite-Field
  has-zero-Finite-Field = has-zero-Finite-Ring finite-ring-Finite-Field

  zero-Finite-Field : type-Finite-Field
  zero-Finite-Field = zero-Finite-Ring finite-ring-Finite-Field

  is-zero-Finite-Field : type-Finite-Field → UU l
  is-zero-Finite-Field = is-zero-Finite-Ring finite-ring-Finite-Field

  is-nonzero-Finite-Field : type-Finite-Field → UU l
  is-nonzero-Finite-Field = is-nonzero-Finite-Ring finite-ring-Finite-Field

  is-zero-field-finite-Prop : type-Finite-Field → Prop l
  is-zero-field-finite-Prop = is-zero-finite-ring-Prop finite-ring-Finite-Field

  is-nonzero-field-finite-Prop : type-Finite-Field → Prop l
  is-nonzero-field-finite-Prop =
    is-nonzero-finite-ring-Prop finite-ring-Finite-Field

  left-unit-law-add-Finite-Field :
    (x : type-Finite-Field) →
    add-Finite-Field zero-Finite-Field x ＝ x
  left-unit-law-add-Finite-Field =
    left-unit-law-add-Finite-Ring finite-ring-Finite-Field

  right-unit-law-add-Finite-Field :
    (x : type-Finite-Field) →
    add-Finite-Field x zero-Finite-Field ＝ x
  right-unit-law-add-Finite-Field =
    right-unit-law-add-Finite-Ring finite-ring-Finite-Field
```

### Additive inverses in a finite fields

```agda
  has-negatives-Finite-Field :
    is-group-is-unital-Semigroup
      additive-semigroup-Finite-Field
      has-zero-Finite-Field
  has-negatives-Finite-Field = has-negatives-Ab ab-Finite-Field

  neg-Finite-Field : type-Finite-Field → type-Finite-Field
  neg-Finite-Field = neg-Finite-Ring finite-ring-Finite-Field

  left-inverse-law-add-Finite-Field :
    (x : type-Finite-Field) →
    add-Finite-Field (neg-Finite-Field x) x ＝ zero-Finite-Field
  left-inverse-law-add-Finite-Field =
    left-inverse-law-add-Finite-Ring finite-ring-Finite-Field

  right-inverse-law-add-Finite-Field :
    (x : type-Finite-Field) →
    add-Finite-Field x (neg-Finite-Field x) ＝ zero-Finite-Field
  right-inverse-law-add-Finite-Field =
    right-inverse-law-add-Finite-Ring finite-ring-Finite-Field

  neg-neg-Finite-Field :
    (x : type-Finite-Field) →
    neg-Finite-Field (neg-Finite-Field x) ＝ x
  neg-neg-Finite-Field = neg-neg-Ab ab-Finite-Field

  distributive-neg-add-Finite-Field :
    (x y : type-Finite-Field) →
    neg-Finite-Field (add-Finite-Field x y) ＝
    add-Finite-Field (neg-Finite-Field x) (neg-Finite-Field y)
  distributive-neg-add-Finite-Field =
    distributive-neg-add-Ab ab-Finite-Field
```

### Multiplication in a finite fields

```agda
  has-associative-mul-Finite-Field :
    has-associative-mul-Set set-Finite-Field
  has-associative-mul-Finite-Field =
    has-associative-mul-Finite-Ring finite-ring-Finite-Field

  mul-Finite-Field : (x y : type-Finite-Field) → type-Finite-Field
  mul-Finite-Field = mul-Finite-Ring finite-ring-Finite-Field

  mul-Finite-Field' : (x y : type-Finite-Field) → type-Finite-Field
  mul-Finite-Field' = mul-Finite-Ring' finite-ring-Finite-Field

  ap-mul-Finite-Field :
    {x x' y y' : type-Finite-Field} (p : x ＝ x') (q : y ＝ y') →
    Id (mul-Finite-Field x y) (mul-Finite-Field x' y')
  ap-mul-Finite-Field p q = ap-binary mul-Finite-Field p q

  associative-mul-Finite-Field :
    (x y z : type-Finite-Field) →
    mul-Finite-Field (mul-Finite-Field x y) z ＝
    mul-Finite-Field x (mul-Finite-Field y z)
  associative-mul-Finite-Field =
    associative-mul-Finite-Ring finite-ring-Finite-Field

  multiplicative-semigroup-Finite-Field : Semigroup l
  pr1 multiplicative-semigroup-Finite-Field = set-Finite-Field
  pr2 multiplicative-semigroup-Finite-Field =
    has-associative-mul-Finite-Field

  left-distributive-mul-add-Finite-Field :
    (x y z : type-Finite-Field) →
    ( mul-Finite-Field x (add-Finite-Field y z)) ＝
    ( add-Finite-Field
      ( mul-Finite-Field x y)
      ( mul-Finite-Field x z))
  left-distributive-mul-add-Finite-Field =
    left-distributive-mul-add-Finite-Ring finite-ring-Finite-Field

  right-distributive-mul-add-Finite-Field :
    (x y z : type-Finite-Field) →
    ( mul-Finite-Field (add-Finite-Field x y) z) ＝
    ( add-Finite-Field
      ( mul-Finite-Field x z)
      ( mul-Finite-Field y z))
  right-distributive-mul-add-Finite-Field =
    right-distributive-mul-add-Finite-Ring finite-ring-Finite-Field

  commutative-mul-Finite-Field :
    (x y : type-Finite-Field) →
    mul-Finite-Field x y ＝ mul-Finite-Field y x
  commutative-mul-Finite-Field =
    commutative-mul-Finite-Commutative-Ring commutative-finite-ring-Finite-Field
```

### Multiplicative units in a finite fields

```agda
  is-unital-Finite-Field : is-unital mul-Finite-Field
  is-unital-Finite-Field = is-unital-Finite-Ring finite-ring-Finite-Field

  multiplicative-monoid-Finite-Field : Monoid l
  multiplicative-monoid-Finite-Field =
    multiplicative-monoid-Finite-Ring finite-ring-Finite-Field

  one-Finite-Field : type-Finite-Field
  one-Finite-Field = one-Finite-Ring finite-ring-Finite-Field

  left-unit-law-mul-Finite-Field :
    (x : type-Finite-Field) →
    mul-Finite-Field one-Finite-Field x ＝ x
  left-unit-law-mul-Finite-Field =
    left-unit-law-mul-Finite-Ring finite-ring-Finite-Field

  right-unit-law-mul-Finite-Field :
    (x : type-Finite-Field) →
    mul-Finite-Field x one-Finite-Field ＝ x
  right-unit-law-mul-Finite-Field =
    right-unit-law-mul-Finite-Ring finite-ring-Finite-Field

  right-swap-mul-Finite-Field :
    (x y z : type-Finite-Field) →
    mul-Finite-Field (mul-Finite-Field x y) z ＝
    mul-Finite-Field (mul-Finite-Field x z) y
  right-swap-mul-Finite-Field =
    right-swap-mul-Finite-Commutative-Ring commutative-finite-ring-Finite-Field

  left-swap-mul-Finite-Field :
    (x y z : type-Finite-Field) →
    mul-Finite-Field x (mul-Finite-Field y z) ＝
    mul-Finite-Field y (mul-Finite-Field x z)
  left-swap-mul-Finite-Field =
    left-swap-mul-Finite-Commutative-Ring commutative-finite-ring-Finite-Field

  interchange-mul-mul-Finite-Field :
    (x y z w : type-Finite-Field) →
    mul-Finite-Field
      ( mul-Finite-Field x y)
      ( mul-Finite-Field z w) ＝
    mul-Finite-Field
      ( mul-Finite-Field x z)
      ( mul-Finite-Field y w)
  interchange-mul-mul-Finite-Field =
    interchange-mul-mul-Finite-Commutative-Ring
      commutative-finite-ring-Finite-Field
```

### The zero laws for multiplication of a finite field

```agda
  left-zero-law-mul-Finite-Field :
    (x : type-Finite-Field) →
    mul-Finite-Field zero-Finite-Field x ＝
    zero-Finite-Field
  left-zero-law-mul-Finite-Field =
    left-zero-law-mul-Finite-Ring finite-ring-Finite-Field

  right-zero-law-mul-Finite-Field :
    (x : type-Finite-Field) →
    mul-Finite-Field x zero-Finite-Field ＝
    zero-Finite-Field
  right-zero-law-mul-Finite-Field =
    right-zero-law-mul-Finite-Ring finite-ring-Finite-Field
```

### Finite fields are commutative finite semirings

```agda
  multiplicative-commutative-monoid-Finite-Field : Commutative-Monoid l
  multiplicative-commutative-monoid-Finite-Field =
    multiplicative-commutative-monoid-Finite-Commutative-Ring
      commutative-finite-ring-Finite-Field

  semifinite-ring-Finite-Field : Semiring l
  semifinite-ring-Finite-Field = semiring-Finite-Ring finite-ring-Finite-Field

  commutative-semiring-Finite-Field : Commutative-Semiring l
  commutative-semiring-Finite-Field =
    commutative-semiring-Finite-Commutative-Ring
      commutative-finite-ring-Finite-Field
```

### Computing multiplication with minus one in a finite field

```agda
  neg-one-Finite-Field : type-Finite-Field
  neg-one-Finite-Field = neg-one-Finite-Ring finite-ring-Finite-Field

  mul-neg-one-Finite-Field :
    (x : type-Finite-Field) →
    mul-Finite-Field neg-one-Finite-Field x ＝
    neg-Finite-Field x
  mul-neg-one-Finite-Field = mul-neg-one-Finite-Ring finite-ring-Finite-Field

  mul-neg-one-Finite-Field' :
    (x : type-Finite-Field) →
    mul-Finite-Field x neg-one-Finite-Field ＝
    neg-Finite-Field x
  mul-neg-one-Finite-Field' = mul-neg-one-Finite-Ring' finite-ring-Finite-Field

  is-involution-mul-neg-one-Finite-Field :
    is-involution (mul-Finite-Field neg-one-Finite-Field)
  is-involution-mul-neg-one-Finite-Field =
    is-involution-mul-neg-one-Finite-Ring finite-ring-Finite-Field

  is-involution-mul-neg-one-Finite-Field' :
    is-involution (mul-Finite-Field' neg-one-Finite-Field)
  is-involution-mul-neg-one-Finite-Field' =
    is-involution-mul-neg-one-Finite-Ring' finite-ring-Finite-Field
```

### Left and right negative laws for multiplication

```agda
  left-negative-law-mul-Finite-Field :
    (x y : type-Finite-Field) →
    mul-Finite-Field (neg-Finite-Field x) y ＝
    neg-Finite-Field (mul-Finite-Field x y)
  left-negative-law-mul-Finite-Field =
    left-negative-law-mul-Finite-Ring finite-ring-Finite-Field

  right-negative-law-mul-Finite-Field :
    (x y : type-Finite-Field) →
    mul-Finite-Field x (neg-Finite-Field y) ＝
    neg-Finite-Field (mul-Finite-Field x y)
  right-negative-law-mul-Finite-Field =
    right-negative-law-mul-Finite-Ring finite-ring-Finite-Field

  mul-neg-Finite-Field :
    (x y : type-Finite-Field) →
    mul-Finite-Field (neg-Finite-Field x) (neg-Finite-Field y) ＝
    mul-Finite-Field x y
  mul-neg-Finite-Field = mul-neg-Finite-Ring finite-ring-Finite-Field
```

### Scalar multiplication of elements of a commutative finite ring by natural numbers

```agda
  mul-nat-scalar-Finite-Field :
    ℕ → type-Finite-Field → type-Finite-Field
  mul-nat-scalar-Finite-Field =
    mul-nat-scalar-Finite-Ring finite-ring-Finite-Field

  ap-mul-nat-scalar-Finite-Field :
    {m n : ℕ} {x y : type-Finite-Field} →
    (m ＝ n) → (x ＝ y) →
    mul-nat-scalar-Finite-Field m x ＝
    mul-nat-scalar-Finite-Field n y
  ap-mul-nat-scalar-Finite-Field =
    ap-mul-nat-scalar-Finite-Ring finite-ring-Finite-Field

  left-zero-law-mul-nat-scalar-Finite-Field :
    (x : type-Finite-Field) →
    mul-nat-scalar-Finite-Field 0 x ＝ zero-Finite-Field
  left-zero-law-mul-nat-scalar-Finite-Field =
    left-zero-law-mul-nat-scalar-Finite-Ring finite-ring-Finite-Field

  right-zero-law-mul-nat-scalar-Finite-Field :
    (n : ℕ) →
    mul-nat-scalar-Finite-Field n zero-Finite-Field ＝
    zero-Finite-Field
  right-zero-law-mul-nat-scalar-Finite-Field =
    right-zero-law-mul-nat-scalar-Finite-Ring finite-ring-Finite-Field

  left-unit-law-mul-nat-scalar-Finite-Field :
    (x : type-Finite-Field) →
    mul-nat-scalar-Finite-Field 1 x ＝ x
  left-unit-law-mul-nat-scalar-Finite-Field =
    left-unit-law-mul-nat-scalar-Finite-Ring finite-ring-Finite-Field

  left-nat-scalar-law-mul-Finite-Field :
    (n : ℕ) (x y : type-Finite-Field) →
    mul-Finite-Field (mul-nat-scalar-Finite-Field n x) y ＝
    mul-nat-scalar-Finite-Field n (mul-Finite-Field x y)
  left-nat-scalar-law-mul-Finite-Field =
    left-nat-scalar-law-mul-Finite-Ring finite-ring-Finite-Field

  right-nat-scalar-law-mul-Finite-Field :
    (n : ℕ) (x y : type-Finite-Field) →
    mul-Finite-Field x (mul-nat-scalar-Finite-Field n y) ＝
    mul-nat-scalar-Finite-Field n (mul-Finite-Field x y)
  right-nat-scalar-law-mul-Finite-Field =
    right-nat-scalar-law-mul-Finite-Ring finite-ring-Finite-Field

  left-distributive-mul-nat-scalar-add-Finite-Field :
    (n : ℕ) (x y : type-Finite-Field) →
    mul-nat-scalar-Finite-Field n (add-Finite-Field x y) ＝
    add-Finite-Field
      ( mul-nat-scalar-Finite-Field n x)
      ( mul-nat-scalar-Finite-Field n y)
  left-distributive-mul-nat-scalar-add-Finite-Field =
    left-distributive-mul-nat-scalar-add-Finite-Ring finite-ring-Finite-Field

  right-distributive-mul-nat-scalar-add-Finite-Field :
    (m n : ℕ) (x : type-Finite-Field) →
    mul-nat-scalar-Finite-Field (m +ℕ n) x ＝
    add-Finite-Field
      ( mul-nat-scalar-Finite-Field m x)
      ( mul-nat-scalar-Finite-Field n x)
  right-distributive-mul-nat-scalar-add-Finite-Field =
    right-distributive-mul-nat-scalar-add-Finite-Ring finite-ring-Finite-Field
```

### Addition of a list of elements in a finite field

```agda
  add-list-Finite-Field : list type-Finite-Field → type-Finite-Field
  add-list-Finite-Field = add-list-Finite-Ring finite-ring-Finite-Field

  preserves-concat-add-list-Finite-Field :
    (l1 l2 : list type-Finite-Field) →
    Id
      ( add-list-Finite-Field (concat-list l1 l2))
      ( add-Finite-Field
        ( add-list-Finite-Field l1)
        ( add-list-Finite-Field l2))
  preserves-concat-add-list-Finite-Field =
    preserves-concat-add-list-Finite-Ring finite-ring-Finite-Field
```
