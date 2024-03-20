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
is-finite-field-Commutative-Ring-𝔽 : {l : Level} → Commutative-Ring-𝔽 l → UU l
is-finite-field-Commutative-Ring-𝔽 A =
  is-division-Ring (ring-Commutative-Ring-𝔽 A)

Field-𝔽 : (l : Level) → UU (lsuc l)
Field-𝔽 l =
  Σ (Commutative-Ring-𝔽 l) (λ A → is-finite-field-Commutative-Ring-𝔽 A)

module _
  {l : Level} (A : Field-𝔽 l)
  where

  commutative-finite-ring-Field-𝔽 : Commutative-Ring-𝔽 l
  commutative-finite-ring-Field-𝔽 = pr1 A

  commutative-ring-Field-𝔽 : Commutative-Ring l
  commutative-ring-Field-𝔽 =
    commutative-ring-Commutative-Ring-𝔽 commutative-finite-ring-Field-𝔽

  finite-ring-Field-𝔽 : Ring-𝔽 l
  finite-ring-Field-𝔽 =
    finite-ring-Commutative-Ring-𝔽 commutative-finite-ring-Field-𝔽

  ring-Field-𝔽 : Ring l
  ring-Field-𝔽 = ring-Ring-𝔽 (finite-ring-Field-𝔽)

  ab-Field-𝔽 : Ab l
  ab-Field-𝔽 = ab-Ring-𝔽 finite-ring-Field-𝔽

  set-Field-𝔽 : Set l
  set-Field-𝔽 = set-Ring-𝔽 finite-ring-Field-𝔽

  type-Field-𝔽 : UU l
  type-Field-𝔽 = type-Ring-𝔽 finite-ring-Field-𝔽

  is-set-type-Field-𝔽 : is-set type-Field-𝔽
  is-set-type-Field-𝔽 = is-set-type-Ring-𝔽 finite-ring-Field-𝔽
```

### Addition in a finite field

```agda
  has-associative-add-Field-𝔽 :
    has-associative-mul-Set set-Field-𝔽
  has-associative-add-Field-𝔽 =
    has-associative-add-Ring-𝔽 finite-ring-Field-𝔽

  add-Field-𝔽 :
    type-Field-𝔽 → type-Field-𝔽 → type-Field-𝔽
  add-Field-𝔽 = add-Ring-𝔽 finite-ring-Field-𝔽

  add-Field-𝔽' :
    type-Field-𝔽 → type-Field-𝔽 → type-Field-𝔽
  add-Field-𝔽' = add-Ring-𝔽' finite-ring-Field-𝔽

  ap-add-Field-𝔽 :
    {x x' y y' : type-Field-𝔽} →
    (x ＝ x') → (y ＝ y') →
    add-Field-𝔽 x y ＝ add-Field-𝔽 x' y'
  ap-add-Field-𝔽 = ap-add-Ring-𝔽 finite-ring-Field-𝔽

  associative-add-Field-𝔽 :
    (x y z : type-Field-𝔽) →
    ( add-Field-𝔽 (add-Field-𝔽 x y) z) ＝
    ( add-Field-𝔽 x (add-Field-𝔽 y z))
  associative-add-Field-𝔽 =
    associative-add-Ring-𝔽 finite-ring-Field-𝔽

  additive-semigroup-Field-𝔽 : Semigroup l
  additive-semigroup-Field-𝔽 = semigroup-Ab ab-Field-𝔽

  is-group-additive-semigroup-Field-𝔽 :
    is-group-Semigroup additive-semigroup-Field-𝔽
  is-group-additive-semigroup-Field-𝔽 =
    is-group-Ab ab-Field-𝔽

  commutative-add-Field-𝔽 :
    (x y : type-Field-𝔽) →
    Id (add-Field-𝔽 x y) (add-Field-𝔽 y x)
  commutative-add-Field-𝔽 = commutative-add-Ab ab-Field-𝔽

  interchange-add-add-Field-𝔽 :
    (x y x' y' : type-Field-𝔽) →
    ( add-Field-𝔽
      ( add-Field-𝔽 x y)
      ( add-Field-𝔽 x' y')) ＝
    ( add-Field-𝔽
      ( add-Field-𝔽 x x')
      ( add-Field-𝔽 y y'))
  interchange-add-add-Field-𝔽 =
    interchange-add-add-Ring-𝔽 finite-ring-Field-𝔽

  right-swap-add-Field-𝔽 :
    (x y z : type-Field-𝔽) →
    ( add-Field-𝔽 (add-Field-𝔽 x y) z) ＝
    ( add-Field-𝔽 (add-Field-𝔽 x z) y)
  right-swap-add-Field-𝔽 =
    right-swap-add-Ring-𝔽 finite-ring-Field-𝔽

  left-swap-add-Field-𝔽 :
    (x y z : type-Field-𝔽) →
    ( add-Field-𝔽 x (add-Field-𝔽 y z)) ＝
    ( add-Field-𝔽 y (add-Field-𝔽 x z))
  left-swap-add-Field-𝔽 =
    left-swap-add-Ring-𝔽 finite-ring-Field-𝔽

  is-equiv-add-Field-𝔽 :
    (x : type-Field-𝔽) → is-equiv (add-Field-𝔽 x)
  is-equiv-add-Field-𝔽 = is-equiv-add-Ab ab-Field-𝔽

  is-equiv-add-Field-𝔽' :
    (x : type-Field-𝔽) → is-equiv (add-Field-𝔽' x)
  is-equiv-add-Field-𝔽' = is-equiv-add-Ab' ab-Field-𝔽

  is-binary-equiv-add-Field-𝔽 : is-binary-equiv add-Field-𝔽
  pr1 is-binary-equiv-add-Field-𝔽 = is-equiv-add-Field-𝔽'
  pr2 is-binary-equiv-add-Field-𝔽 = is-equiv-add-Field-𝔽

  is-binary-emb-add-Field-𝔽 : is-binary-emb add-Field-𝔽
  is-binary-emb-add-Field-𝔽 = is-binary-emb-add-Ab ab-Field-𝔽

  is-emb-add-Field-𝔽 :
    (x : type-Field-𝔽) → is-emb (add-Field-𝔽 x)
  is-emb-add-Field-𝔽 = is-emb-add-Ab ab-Field-𝔽

  is-emb-add-Field-𝔽' :
    (x : type-Field-𝔽) → is-emb (add-Field-𝔽' x)
  is-emb-add-Field-𝔽' = is-emb-add-Ab' ab-Field-𝔽

  is-injective-add-Field-𝔽 :
    (x : type-Field-𝔽) → is-injective (add-Field-𝔽 x)
  is-injective-add-Field-𝔽 = is-injective-add-Ab ab-Field-𝔽

  is-injective-add-Field-𝔽' :
    (x : type-Field-𝔽) → is-injective (add-Field-𝔽' x)
  is-injective-add-Field-𝔽' = is-injective-add-Ab' ab-Field-𝔽
```

### The zero element of a finite field

```agda
  has-zero-Field-𝔽 : is-unital add-Field-𝔽
  has-zero-Field-𝔽 = has-zero-Ring-𝔽 finite-ring-Field-𝔽

  zero-Field-𝔽 : type-Field-𝔽
  zero-Field-𝔽 = zero-Ring-𝔽 finite-ring-Field-𝔽

  is-zero-Field-𝔽 : type-Field-𝔽 → UU l
  is-zero-Field-𝔽 = is-zero-Ring-𝔽 finite-ring-Field-𝔽

  is-nonzero-Field-𝔽 : type-Field-𝔽 → UU l
  is-nonzero-Field-𝔽 = is-nonzero-Ring-𝔽 finite-ring-Field-𝔽

  is-zero-field-finite-Prop : type-Field-𝔽 → Prop l
  is-zero-field-finite-Prop = is-zero-finite-ring-Prop finite-ring-Field-𝔽

  is-nonzero-field-finite-Prop : type-Field-𝔽 → Prop l
  is-nonzero-field-finite-Prop = is-nonzero-finite-ring-Prop finite-ring-Field-𝔽

  left-unit-law-add-Field-𝔽 :
    (x : type-Field-𝔽) →
    add-Field-𝔽 zero-Field-𝔽 x ＝ x
  left-unit-law-add-Field-𝔽 =
    left-unit-law-add-Ring-𝔽 finite-ring-Field-𝔽

  right-unit-law-add-Field-𝔽 :
    (x : type-Field-𝔽) →
    add-Field-𝔽 x zero-Field-𝔽 ＝ x
  right-unit-law-add-Field-𝔽 =
    right-unit-law-add-Ring-𝔽 finite-ring-Field-𝔽
```

### Additive inverses in a finite fields

```agda
  has-negatives-Field-𝔽 :
    is-group-is-unital-Semigroup additive-semigroup-Field-𝔽 has-zero-Field-𝔽
  has-negatives-Field-𝔽 = has-negatives-Ab ab-Field-𝔽

  neg-Field-𝔽 : type-Field-𝔽 → type-Field-𝔽
  neg-Field-𝔽 = neg-Ring-𝔽 finite-ring-Field-𝔽

  left-inverse-law-add-Field-𝔽 :
    (x : type-Field-𝔽) →
    add-Field-𝔽 (neg-Field-𝔽 x) x ＝ zero-Field-𝔽
  left-inverse-law-add-Field-𝔽 =
    left-inverse-law-add-Ring-𝔽 finite-ring-Field-𝔽

  right-inverse-law-add-Field-𝔽 :
    (x : type-Field-𝔽) →
    add-Field-𝔽 x (neg-Field-𝔽 x) ＝ zero-Field-𝔽
  right-inverse-law-add-Field-𝔽 =
    right-inverse-law-add-Ring-𝔽 finite-ring-Field-𝔽

  neg-neg-Field-𝔽 :
    (x : type-Field-𝔽) →
    neg-Field-𝔽 (neg-Field-𝔽 x) ＝ x
  neg-neg-Field-𝔽 = neg-neg-Ab ab-Field-𝔽

  distributive-neg-add-Field-𝔽 :
    (x y : type-Field-𝔽) →
    neg-Field-𝔽 (add-Field-𝔽 x y) ＝
    add-Field-𝔽 (neg-Field-𝔽 x) (neg-Field-𝔽 y)
  distributive-neg-add-Field-𝔽 =
    distributive-neg-add-Ab ab-Field-𝔽
```

### Multiplication in a finite fields

```agda
  has-associative-mul-Field-𝔽 :
    has-associative-mul-Set set-Field-𝔽
  has-associative-mul-Field-𝔽 =
    has-associative-mul-Ring-𝔽 finite-ring-Field-𝔽

  mul-Field-𝔽 : (x y : type-Field-𝔽) → type-Field-𝔽
  mul-Field-𝔽 = mul-Ring-𝔽 finite-ring-Field-𝔽

  mul-Field-𝔽' : (x y : type-Field-𝔽) → type-Field-𝔽
  mul-Field-𝔽' = mul-Ring-𝔽' finite-ring-Field-𝔽

  ap-mul-Field-𝔽 :
    {x x' y y' : type-Field-𝔽} (p : Id x x') (q : Id y y') →
    Id (mul-Field-𝔽 x y) (mul-Field-𝔽 x' y')
  ap-mul-Field-𝔽 p q = ap-binary mul-Field-𝔽 p q

  associative-mul-Field-𝔽 :
    (x y z : type-Field-𝔽) →
    mul-Field-𝔽 (mul-Field-𝔽 x y) z ＝
    mul-Field-𝔽 x (mul-Field-𝔽 y z)
  associative-mul-Field-𝔽 =
    associative-mul-Ring-𝔽 finite-ring-Field-𝔽

  multiplicative-semigroup-Field-𝔽 : Semigroup l
  pr1 multiplicative-semigroup-Field-𝔽 = set-Field-𝔽
  pr2 multiplicative-semigroup-Field-𝔽 =
    has-associative-mul-Field-𝔽

  left-distributive-mul-add-Field-𝔽 :
    (x y z : type-Field-𝔽) →
    ( mul-Field-𝔽 x (add-Field-𝔽 y z)) ＝
    ( add-Field-𝔽
      ( mul-Field-𝔽 x y)
      ( mul-Field-𝔽 x z))
  left-distributive-mul-add-Field-𝔽 =
    left-distributive-mul-add-Ring-𝔽 finite-ring-Field-𝔽

  right-distributive-mul-add-Field-𝔽 :
    (x y z : type-Field-𝔽) →
    ( mul-Field-𝔽 (add-Field-𝔽 x y) z) ＝
    ( add-Field-𝔽
      ( mul-Field-𝔽 x z)
      ( mul-Field-𝔽 y z))
  right-distributive-mul-add-Field-𝔽 =
    right-distributive-mul-add-Ring-𝔽 finite-ring-Field-𝔽

  commutative-mul-Field-𝔽 :
    (x y : type-Field-𝔽) →
    mul-Field-𝔽 x y ＝ mul-Field-𝔽 y x
  commutative-mul-Field-𝔽 =
    commutative-mul-Commutative-Ring-𝔽 commutative-finite-ring-Field-𝔽
```

### Multiplicative units in a finite fields

```agda
  is-unital-Field-𝔽 : is-unital mul-Field-𝔽
  is-unital-Field-𝔽 = is-unital-Ring-𝔽 finite-ring-Field-𝔽

  multiplicative-monoid-Field-𝔽 : Monoid l
  multiplicative-monoid-Field-𝔽 =
    multiplicative-monoid-Ring-𝔽 finite-ring-Field-𝔽

  one-Field-𝔽 : type-Field-𝔽
  one-Field-𝔽 = one-Ring-𝔽 finite-ring-Field-𝔽

  left-unit-law-mul-Field-𝔽 :
    (x : type-Field-𝔽) →
    mul-Field-𝔽 one-Field-𝔽 x ＝ x
  left-unit-law-mul-Field-𝔽 =
    left-unit-law-mul-Ring-𝔽 finite-ring-Field-𝔽

  right-unit-law-mul-Field-𝔽 :
    (x : type-Field-𝔽) →
    mul-Field-𝔽 x one-Field-𝔽 ＝ x
  right-unit-law-mul-Field-𝔽 =
    right-unit-law-mul-Ring-𝔽 finite-ring-Field-𝔽

  right-swap-mul-Field-𝔽 :
    (x y z : type-Field-𝔽) →
    mul-Field-𝔽 (mul-Field-𝔽 x y) z ＝
    mul-Field-𝔽 (mul-Field-𝔽 x z) y
  right-swap-mul-Field-𝔽 =
    right-swap-mul-Commutative-Ring-𝔽 commutative-finite-ring-Field-𝔽

  left-swap-mul-Field-𝔽 :
    (x y z : type-Field-𝔽) →
    mul-Field-𝔽 x (mul-Field-𝔽 y z) ＝
    mul-Field-𝔽 y (mul-Field-𝔽 x z)
  left-swap-mul-Field-𝔽 =
    left-swap-mul-Commutative-Ring-𝔽 commutative-finite-ring-Field-𝔽

  interchange-mul-mul-Field-𝔽 :
    (x y z w : type-Field-𝔽) →
    mul-Field-𝔽
      ( mul-Field-𝔽 x y)
      ( mul-Field-𝔽 z w) ＝
    mul-Field-𝔽
      ( mul-Field-𝔽 x z)
      ( mul-Field-𝔽 y w)
  interchange-mul-mul-Field-𝔽 =
    interchange-mul-mul-Commutative-Ring-𝔽 commutative-finite-ring-Field-𝔽
```

### The zero laws for multiplication of a finite field

```agda
  left-zero-law-mul-Field-𝔽 :
    (x : type-Field-𝔽) →
    mul-Field-𝔽 zero-Field-𝔽 x ＝
    zero-Field-𝔽
  left-zero-law-mul-Field-𝔽 =
    left-zero-law-mul-Ring-𝔽 finite-ring-Field-𝔽

  right-zero-law-mul-Field-𝔽 :
    (x : type-Field-𝔽) →
    mul-Field-𝔽 x zero-Field-𝔽 ＝
    zero-Field-𝔽
  right-zero-law-mul-Field-𝔽 =
    right-zero-law-mul-Ring-𝔽 finite-ring-Field-𝔽
```

### Finite fields are commutative finite semirings

```agda
  multiplicative-commutative-monoid-Field-𝔽 : Commutative-Monoid l
  multiplicative-commutative-monoid-Field-𝔽 =
    multiplicative-commutative-monoid-Commutative-Ring-𝔽
      commutative-finite-ring-Field-𝔽

  semifinite-ring-Field-𝔽 : Semiring l
  semifinite-ring-Field-𝔽 = semiring-Ring-𝔽 finite-ring-Field-𝔽

  commutative-semiring-Field-𝔽 : Commutative-Semiring l
  commutative-semiring-Field-𝔽 =
    commutative-semiring-Commutative-Ring-𝔽 commutative-finite-ring-Field-𝔽
```

### Computing multiplication with minus one in a finite field

```agda
  neg-one-Field-𝔽 : type-Field-𝔽
  neg-one-Field-𝔽 = neg-one-Ring-𝔽 finite-ring-Field-𝔽

  mul-neg-one-Field-𝔽 :
    (x : type-Field-𝔽) →
    mul-Field-𝔽 neg-one-Field-𝔽 x ＝
    neg-Field-𝔽 x
  mul-neg-one-Field-𝔽 = mul-neg-one-Ring-𝔽 finite-ring-Field-𝔽

  mul-neg-one-Field-𝔽' :
    (x : type-Field-𝔽) →
    mul-Field-𝔽 x neg-one-Field-𝔽 ＝
    neg-Field-𝔽 x
  mul-neg-one-Field-𝔽' = mul-neg-one-Ring-𝔽' finite-ring-Field-𝔽

  is-involution-mul-neg-one-Field-𝔽 :
    is-involution (mul-Field-𝔽 neg-one-Field-𝔽)
  is-involution-mul-neg-one-Field-𝔽 =
    is-involution-mul-neg-one-Ring-𝔽 finite-ring-Field-𝔽

  is-involution-mul-neg-one-Field-𝔽' :
    is-involution (mul-Field-𝔽' neg-one-Field-𝔽)
  is-involution-mul-neg-one-Field-𝔽' =
    is-involution-mul-neg-one-Ring-𝔽' finite-ring-Field-𝔽
```

### Left and right negative laws for multiplication

```agda
  left-negative-law-mul-Field-𝔽 :
    (x y : type-Field-𝔽) →
    mul-Field-𝔽 (neg-Field-𝔽 x) y ＝
    neg-Field-𝔽 (mul-Field-𝔽 x y)
  left-negative-law-mul-Field-𝔽 =
    left-negative-law-mul-Ring-𝔽 finite-ring-Field-𝔽

  right-negative-law-mul-Field-𝔽 :
    (x y : type-Field-𝔽) →
    mul-Field-𝔽 x (neg-Field-𝔽 y) ＝
    neg-Field-𝔽 (mul-Field-𝔽 x y)
  right-negative-law-mul-Field-𝔽 =
    right-negative-law-mul-Ring-𝔽 finite-ring-Field-𝔽

  mul-neg-Field-𝔽 :
    (x y : type-Field-𝔽) →
    mul-Field-𝔽 (neg-Field-𝔽 x) (neg-Field-𝔽 y) ＝
    mul-Field-𝔽 x y
  mul-neg-Field-𝔽 = mul-neg-Ring-𝔽 finite-ring-Field-𝔽
```

### Scalar multiplication of elements of a commutative finite ring by natural numbers

```agda
  mul-nat-scalar-Field-𝔽 :
    ℕ → type-Field-𝔽 → type-Field-𝔽
  mul-nat-scalar-Field-𝔽 =
    mul-nat-scalar-Ring-𝔽 finite-ring-Field-𝔽

  ap-mul-nat-scalar-Field-𝔽 :
    {m n : ℕ} {x y : type-Field-𝔽} →
    (m ＝ n) → (x ＝ y) →
    mul-nat-scalar-Field-𝔽 m x ＝
    mul-nat-scalar-Field-𝔽 n y
  ap-mul-nat-scalar-Field-𝔽 =
    ap-mul-nat-scalar-Ring-𝔽 finite-ring-Field-𝔽

  left-zero-law-mul-nat-scalar-Field-𝔽 :
    (x : type-Field-𝔽) →
    mul-nat-scalar-Field-𝔽 0 x ＝ zero-Field-𝔽
  left-zero-law-mul-nat-scalar-Field-𝔽 =
    left-zero-law-mul-nat-scalar-Ring-𝔽 finite-ring-Field-𝔽

  right-zero-law-mul-nat-scalar-Field-𝔽 :
    (n : ℕ) →
    mul-nat-scalar-Field-𝔽 n zero-Field-𝔽 ＝
    zero-Field-𝔽
  right-zero-law-mul-nat-scalar-Field-𝔽 =
    right-zero-law-mul-nat-scalar-Ring-𝔽 finite-ring-Field-𝔽

  left-unit-law-mul-nat-scalar-Field-𝔽 :
    (x : type-Field-𝔽) →
    mul-nat-scalar-Field-𝔽 1 x ＝ x
  left-unit-law-mul-nat-scalar-Field-𝔽 =
    left-unit-law-mul-nat-scalar-Ring-𝔽 finite-ring-Field-𝔽

  left-nat-scalar-law-mul-Field-𝔽 :
    (n : ℕ) (x y : type-Field-𝔽) →
    mul-Field-𝔽 (mul-nat-scalar-Field-𝔽 n x) y ＝
    mul-nat-scalar-Field-𝔽 n (mul-Field-𝔽 x y)
  left-nat-scalar-law-mul-Field-𝔽 =
    left-nat-scalar-law-mul-Ring-𝔽 finite-ring-Field-𝔽

  right-nat-scalar-law-mul-Field-𝔽 :
    (n : ℕ) (x y : type-Field-𝔽) →
    mul-Field-𝔽 x (mul-nat-scalar-Field-𝔽 n y) ＝
    mul-nat-scalar-Field-𝔽 n (mul-Field-𝔽 x y)
  right-nat-scalar-law-mul-Field-𝔽 =
    right-nat-scalar-law-mul-Ring-𝔽 finite-ring-Field-𝔽

  left-distributive-mul-nat-scalar-add-Field-𝔽 :
    (n : ℕ) (x y : type-Field-𝔽) →
    mul-nat-scalar-Field-𝔽 n (add-Field-𝔽 x y) ＝
    add-Field-𝔽
      ( mul-nat-scalar-Field-𝔽 n x)
      ( mul-nat-scalar-Field-𝔽 n y)
  left-distributive-mul-nat-scalar-add-Field-𝔽 =
    left-distributive-mul-nat-scalar-add-Ring-𝔽 finite-ring-Field-𝔽

  right-distributive-mul-nat-scalar-add-Field-𝔽 :
    (m n : ℕ) (x : type-Field-𝔽) →
    mul-nat-scalar-Field-𝔽 (m +ℕ n) x ＝
    add-Field-𝔽
      ( mul-nat-scalar-Field-𝔽 m x)
      ( mul-nat-scalar-Field-𝔽 n x)
  right-distributive-mul-nat-scalar-add-Field-𝔽 =
    right-distributive-mul-nat-scalar-add-Ring-𝔽 finite-ring-Field-𝔽
```

### Addition of a list of elements in a finite field

```agda
  add-list-Field-𝔽 : list type-Field-𝔽 → type-Field-𝔽
  add-list-Field-𝔽 = add-list-Ring-𝔽 finite-ring-Field-𝔽

  preserves-concat-add-list-Field-𝔽 :
    (l1 l2 : list type-Field-𝔽) →
    Id
      ( add-list-Field-𝔽 (concat-list l1 l2))
      ( add-Field-𝔽
        ( add-list-Field-𝔽 l1)
        ( add-list-Field-𝔽 l2))
  preserves-concat-add-list-Field-𝔽 =
    preserves-concat-add-list-Ring-𝔽 finite-ring-Field-𝔽
```
