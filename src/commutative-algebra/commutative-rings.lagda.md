# Commutative rings

```agda
module commutative-algebra.commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
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

A ring `A` is said to be **commutative** if its multiplicative operation is
commutative, i.e., if `xy = yx` for all `x, y ∈ A`.

## Definition

### The predicate on rings of being commutative

```agda
module _
  {l : Level} (A : Ring l)
  where

  is-commutative-Ring : UU l
  is-commutative-Ring =
    (x y : type-Ring A) → mul-Ring A x y ＝ mul-Ring A y x

  is-prop-is-commutative-Ring : is-prop is-commutative-Ring
  is-prop-is-commutative-Ring =
    is-prop-Π
      ( λ x →
        is-prop-Π
        ( λ y →
          is-set-type-Ring A (mul-Ring A x y) (mul-Ring A y x)))

  is-commutative-prop-Ring : Prop l
  is-commutative-prop-Ring = is-commutative-Ring , is-prop-is-commutative-Ring
```

### Commutative rings

```agda
Commutative-Ring :
  ( l : Level) → UU (lsuc l)
Commutative-Ring l = Σ (Ring l) is-commutative-Ring

module _
  {l : Level} (A : Commutative-Ring l)
  where

  ring-Commutative-Ring : Ring l
  ring-Commutative-Ring = pr1 A

  ab-Commutative-Ring : Ab l
  ab-Commutative-Ring = ab-Ring ring-Commutative-Ring

  set-Commutative-Ring : Set l
  set-Commutative-Ring = set-Ring ring-Commutative-Ring

  type-Commutative-Ring : UU l
  type-Commutative-Ring = type-Ring ring-Commutative-Ring

  is-set-type-Commutative-Ring : is-set type-Commutative-Ring
  is-set-type-Commutative-Ring = is-set-type-Ring ring-Commutative-Ring
```

### Addition in a commutative ring

```agda
  has-associative-add-Commutative-Ring :
    has-associative-mul-Set set-Commutative-Ring
  has-associative-add-Commutative-Ring =
    has-associative-add-Ring ring-Commutative-Ring

  add-Commutative-Ring :
    type-Commutative-Ring → type-Commutative-Ring → type-Commutative-Ring
  add-Commutative-Ring = add-Ring ring-Commutative-Ring

  add-Commutative-Ring' :
    type-Commutative-Ring → type-Commutative-Ring → type-Commutative-Ring
  add-Commutative-Ring' = add-Ring' ring-Commutative-Ring

  ap-add-Commutative-Ring :
    {x x' y y' : type-Commutative-Ring} →
    (x ＝ x') → (y ＝ y') →
    add-Commutative-Ring x y ＝ add-Commutative-Ring x' y'
  ap-add-Commutative-Ring = ap-add-Ring ring-Commutative-Ring

  associative-add-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    ( add-Commutative-Ring (add-Commutative-Ring x y) z) ＝
    ( add-Commutative-Ring x (add-Commutative-Ring y z))
  associative-add-Commutative-Ring =
    associative-add-Ring ring-Commutative-Ring

  additive-semigroup-Commutative-Ring : Semigroup l
  additive-semigroup-Commutative-Ring = semigroup-Ab ab-Commutative-Ring

  is-group-additive-semigroup-Commutative-Ring :
    is-group-Semigroup additive-semigroup-Commutative-Ring
  is-group-additive-semigroup-Commutative-Ring =
    is-group-Ab ab-Commutative-Ring

  commutative-add-Commutative-Ring :
    (x y : type-Commutative-Ring) →
    add-Commutative-Ring x y ＝ add-Commutative-Ring y x
  commutative-add-Commutative-Ring = commutative-add-Ab ab-Commutative-Ring

  interchange-add-add-Commutative-Ring :
    (x y x' y' : type-Commutative-Ring) →
    ( add-Commutative-Ring
      ( add-Commutative-Ring x y)
      ( add-Commutative-Ring x' y')) ＝
    ( add-Commutative-Ring
      ( add-Commutative-Ring x x')
      ( add-Commutative-Ring y y'))
  interchange-add-add-Commutative-Ring =
    interchange-add-add-Ring ring-Commutative-Ring

  right-swap-add-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    ( add-Commutative-Ring (add-Commutative-Ring x y) z) ＝
    ( add-Commutative-Ring (add-Commutative-Ring x z) y)
  right-swap-add-Commutative-Ring =
    right-swap-add-Ring ring-Commutative-Ring

  left-swap-add-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    ( add-Commutative-Ring x (add-Commutative-Ring y z)) ＝
    ( add-Commutative-Ring y (add-Commutative-Ring x z))
  left-swap-add-Commutative-Ring =
    left-swap-add-Ring ring-Commutative-Ring

  left-subtraction-Commutative-Ring :
    type-Commutative-Ring → type-Commutative-Ring → type-Commutative-Ring
  left-subtraction-Commutative-Ring =
    left-subtraction-Ring ring-Commutative-Ring

  is-section-left-subtraction-Commutative-Ring :
    (x : type-Commutative-Ring) →
    (add-Commutative-Ring x ∘ left-subtraction-Commutative-Ring x) ~ id
  is-section-left-subtraction-Commutative-Ring =
    is-section-left-subtraction-Ring ring-Commutative-Ring

  is-retraction-left-subtraction-Commutative-Ring :
    (x : type-Commutative-Ring) →
    (left-subtraction-Commutative-Ring x ∘ add-Commutative-Ring x) ~ id
  is-retraction-left-subtraction-Commutative-Ring =
    is-retraction-left-subtraction-Ring ring-Commutative-Ring

  is-equiv-add-Commutative-Ring :
    (x : type-Commutative-Ring) → is-equiv (add-Commutative-Ring x)
  is-equiv-add-Commutative-Ring = is-equiv-add-Ab ab-Commutative-Ring

  equiv-add-Commutative-Ring :
    type-Commutative-Ring → (type-Commutative-Ring ≃ type-Commutative-Ring)
  equiv-add-Commutative-Ring = equiv-add-Ring ring-Commutative-Ring

  right-subtraction-Commutative-Ring :
    type-Commutative-Ring → type-Commutative-Ring → type-Commutative-Ring
  right-subtraction-Commutative-Ring =
    right-subtraction-Ring ring-Commutative-Ring

  ap-right-subtraction-Commutative-Ring :
    {x x' y y' : type-Commutative-Ring} → x ＝ x' → y ＝ y' →
    right-subtraction-Commutative-Ring x y ＝
    right-subtraction-Commutative-Ring x' y'
  ap-right-subtraction-Commutative-Ring =
    ap-right-subtraction-Ring ring-Commutative-Ring

  is-section-right-subtraction-Commutative-Ring :
    (x : type-Commutative-Ring) →
    ( add-Commutative-Ring' x ∘
      (λ y → right-subtraction-Commutative-Ring y x)) ~ id
  is-section-right-subtraction-Commutative-Ring =
    is-section-right-subtraction-Ring ring-Commutative-Ring

  is-retraction-right-subtraction-Commutative-Ring :
    (x : type-Commutative-Ring) →
    ( ( λ y → right-subtraction-Commutative-Ring y x) ∘
      add-Commutative-Ring' x) ~ id
  is-retraction-right-subtraction-Commutative-Ring =
    is-retraction-right-subtraction-Ring ring-Commutative-Ring

  is-equiv-add-Commutative-Ring' :
    (x : type-Commutative-Ring) → is-equiv (add-Commutative-Ring' x)
  is-equiv-add-Commutative-Ring' = is-equiv-add-Ab' ab-Commutative-Ring

  equiv-add-Commutative-Ring' :
    type-Commutative-Ring → (type-Commutative-Ring ≃ type-Commutative-Ring)
  equiv-add-Commutative-Ring' =
    equiv-add-Ring' ring-Commutative-Ring

  is-binary-equiv-add-Commutative-Ring : is-binary-equiv add-Commutative-Ring
  pr1 is-binary-equiv-add-Commutative-Ring = is-equiv-add-Commutative-Ring'
  pr2 is-binary-equiv-add-Commutative-Ring = is-equiv-add-Commutative-Ring

  is-binary-emb-add-Commutative-Ring : is-binary-emb add-Commutative-Ring
  is-binary-emb-add-Commutative-Ring = is-binary-emb-add-Ab ab-Commutative-Ring

  is-emb-add-Commutative-Ring :
    (x : type-Commutative-Ring) → is-emb (add-Commutative-Ring x)
  is-emb-add-Commutative-Ring = is-emb-add-Ab ab-Commutative-Ring

  is-emb-add-Commutative-Ring' :
    (x : type-Commutative-Ring) → is-emb (add-Commutative-Ring' x)
  is-emb-add-Commutative-Ring' = is-emb-add-Ab' ab-Commutative-Ring

  is-injective-add-Commutative-Ring :
    (x : type-Commutative-Ring) → is-injective (add-Commutative-Ring x)
  is-injective-add-Commutative-Ring = is-injective-add-Ab ab-Commutative-Ring

  is-injective-add-Commutative-Ring' :
    (x : type-Commutative-Ring) → is-injective (add-Commutative-Ring' x)
  is-injective-add-Commutative-Ring' = is-injective-add-Ab' ab-Commutative-Ring
```

### The zero element of a commutative ring

```agda
  has-zero-Commutative-Ring : is-unital add-Commutative-Ring
  has-zero-Commutative-Ring = has-zero-Ring ring-Commutative-Ring

  zero-Commutative-Ring : type-Commutative-Ring
  zero-Commutative-Ring = zero-Ring ring-Commutative-Ring

  is-zero-Commutative-Ring : type-Commutative-Ring → UU l
  is-zero-Commutative-Ring = is-zero-Ring ring-Commutative-Ring

  is-nonzero-Commutative-Ring : type-Commutative-Ring → UU l
  is-nonzero-Commutative-Ring = is-nonzero-Ring ring-Commutative-Ring

  is-zero-commutative-ring-Prop : type-Commutative-Ring → Prop l
  is-zero-commutative-ring-Prop x =
    Id-Prop set-Commutative-Ring x zero-Commutative-Ring

  is-nonzero-commutative-ring-Prop : type-Commutative-Ring → Prop l
  is-nonzero-commutative-ring-Prop x =
    neg-Prop (is-zero-commutative-ring-Prop x)

  left-unit-law-add-Commutative-Ring :
    (x : type-Commutative-Ring) →
    add-Commutative-Ring zero-Commutative-Ring x ＝ x
  left-unit-law-add-Commutative-Ring =
    left-unit-law-add-Ring ring-Commutative-Ring

  right-unit-law-add-Commutative-Ring :
    (x : type-Commutative-Ring) →
    add-Commutative-Ring x zero-Commutative-Ring ＝ x
  right-unit-law-add-Commutative-Ring =
    right-unit-law-add-Ring ring-Commutative-Ring
```

### Additive inverses in a commutative ring

```agda
  has-negatives-Commutative-Ring :
    is-group-is-unital-Semigroup
      ( additive-semigroup-Commutative-Ring)
      ( has-zero-Commutative-Ring)
  has-negatives-Commutative-Ring = has-negatives-Ab ab-Commutative-Ring

  neg-Commutative-Ring : type-Commutative-Ring → type-Commutative-Ring
  neg-Commutative-Ring = neg-Ring ring-Commutative-Ring

  left-inverse-law-add-Commutative-Ring :
    (x : type-Commutative-Ring) →
    add-Commutative-Ring (neg-Commutative-Ring x) x ＝ zero-Commutative-Ring
  left-inverse-law-add-Commutative-Ring =
    left-inverse-law-add-Ring ring-Commutative-Ring

  right-inverse-law-add-Commutative-Ring :
    (x : type-Commutative-Ring) →
    add-Commutative-Ring x (neg-Commutative-Ring x) ＝ zero-Commutative-Ring
  right-inverse-law-add-Commutative-Ring =
    right-inverse-law-add-Ring ring-Commutative-Ring

  neg-neg-Commutative-Ring :
    (x : type-Commutative-Ring) →
    neg-Commutative-Ring (neg-Commutative-Ring x) ＝ x
  neg-neg-Commutative-Ring = neg-neg-Ab ab-Commutative-Ring

  distributive-neg-add-Commutative-Ring :
    (x y : type-Commutative-Ring) →
    neg-Commutative-Ring (add-Commutative-Ring x y) ＝
    add-Commutative-Ring (neg-Commutative-Ring x) (neg-Commutative-Ring y)
  distributive-neg-add-Commutative-Ring =
    distributive-neg-add-Ab ab-Commutative-Ring
```

### Multiplication in a commutative ring

```agda
  has-associative-mul-Commutative-Ring :
    has-associative-mul-Set set-Commutative-Ring
  has-associative-mul-Commutative-Ring =
    has-associative-mul-Ring ring-Commutative-Ring

  mul-Commutative-Ring : (x y : type-Commutative-Ring) → type-Commutative-Ring
  mul-Commutative-Ring = mul-Ring ring-Commutative-Ring

  mul-Commutative-Ring' : (x y : type-Commutative-Ring) → type-Commutative-Ring
  mul-Commutative-Ring' = mul-Ring' ring-Commutative-Ring

  ap-mul-Commutative-Ring :
    {x x' y y' : type-Commutative-Ring} (p : x ＝ x') (q : y ＝ y') →
    mul-Commutative-Ring x y ＝ mul-Commutative-Ring x' y'
  ap-mul-Commutative-Ring p q = ap-binary mul-Commutative-Ring p q

  associative-mul-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    mul-Commutative-Ring (mul-Commutative-Ring x y) z ＝
    mul-Commutative-Ring x (mul-Commutative-Ring y z)
  associative-mul-Commutative-Ring =
    associative-mul-Ring ring-Commutative-Ring

  multiplicative-semigroup-Commutative-Ring : Semigroup l
  pr1 multiplicative-semigroup-Commutative-Ring = set-Commutative-Ring
  pr2 multiplicative-semigroup-Commutative-Ring =
    has-associative-mul-Commutative-Ring

  left-distributive-mul-add-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    mul-Commutative-Ring x (add-Commutative-Ring y z) ＝
    add-Commutative-Ring (mul-Commutative-Ring x y) (mul-Commutative-Ring x z)
  left-distributive-mul-add-Commutative-Ring =
    left-distributive-mul-add-Ring ring-Commutative-Ring

  right-distributive-mul-add-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    mul-Commutative-Ring (add-Commutative-Ring x y) z ＝
    add-Commutative-Ring (mul-Commutative-Ring x z) (mul-Commutative-Ring y z)
  right-distributive-mul-add-Commutative-Ring =
    right-distributive-mul-add-Ring ring-Commutative-Ring

  bidistributive-mul-add-Commutative-Ring :
    (u v x y : type-Commutative-Ring) →
    mul-Commutative-Ring
      ( add-Commutative-Ring u v)
      ( add-Commutative-Ring x y) ＝
    add-Commutative-Ring
      ( add-Commutative-Ring
        ( mul-Commutative-Ring u x)
        ( mul-Commutative-Ring u y))
      ( add-Commutative-Ring
        ( mul-Commutative-Ring v x)
        ( mul-Commutative-Ring v y))
  bidistributive-mul-add-Commutative-Ring =
    bidistributive-mul-add-Ring ring-Commutative-Ring

  commutative-mul-Commutative-Ring :
    (x y : type-Commutative-Ring) →
    mul-Commutative-Ring x y ＝ mul-Commutative-Ring y x
  commutative-mul-Commutative-Ring = pr2 A
```

### Multiplicative units in a commutative ring

```agda
  is-unital-Commutative-Ring : is-unital mul-Commutative-Ring
  is-unital-Commutative-Ring = is-unital-Ring ring-Commutative-Ring

  multiplicative-monoid-Commutative-Ring : Monoid l
  multiplicative-monoid-Commutative-Ring =
    multiplicative-monoid-Ring ring-Commutative-Ring

  one-Commutative-Ring : type-Commutative-Ring
  one-Commutative-Ring = one-Ring ring-Commutative-Ring

  left-unit-law-mul-Commutative-Ring :
    (x : type-Commutative-Ring) →
    mul-Commutative-Ring one-Commutative-Ring x ＝ x
  left-unit-law-mul-Commutative-Ring =
    left-unit-law-mul-Ring ring-Commutative-Ring

  right-unit-law-mul-Commutative-Ring :
    (x : type-Commutative-Ring) →
    mul-Commutative-Ring x one-Commutative-Ring ＝ x
  right-unit-law-mul-Commutative-Ring =
    right-unit-law-mul-Ring ring-Commutative-Ring

  right-swap-mul-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    mul-Commutative-Ring (mul-Commutative-Ring x y) z ＝
    mul-Commutative-Ring (mul-Commutative-Ring x z) y
  right-swap-mul-Commutative-Ring x y z =
    ( associative-mul-Commutative-Ring x y z) ∙
    ( ( ap
        ( mul-Commutative-Ring x)
        ( commutative-mul-Commutative-Ring y z)) ∙
      ( inv (associative-mul-Commutative-Ring x z y)))

  left-swap-mul-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    mul-Commutative-Ring x (mul-Commutative-Ring y z) ＝
    mul-Commutative-Ring y (mul-Commutative-Ring x z)
  left-swap-mul-Commutative-Ring x y z =
    ( inv (associative-mul-Commutative-Ring x y z)) ∙
    ( ( ap
        ( mul-Commutative-Ring' z)
        ( commutative-mul-Commutative-Ring x y)) ∙
      ( associative-mul-Commutative-Ring y x z))

  interchange-mul-mul-Commutative-Ring :
    (x y z w : type-Commutative-Ring) →
    mul-Commutative-Ring
      ( mul-Commutative-Ring x y)
      ( mul-Commutative-Ring z w) ＝
    mul-Commutative-Ring
      ( mul-Commutative-Ring x z)
      ( mul-Commutative-Ring y w)
  interchange-mul-mul-Commutative-Ring =
    interchange-law-commutative-and-associative
      mul-Commutative-Ring
      commutative-mul-Commutative-Ring
      associative-mul-Commutative-Ring
```

### The zero laws for multiplication of a commutative ring

```agda
  left-zero-law-mul-Commutative-Ring :
    (x : type-Commutative-Ring) →
    mul-Commutative-Ring zero-Commutative-Ring x ＝
    zero-Commutative-Ring
  left-zero-law-mul-Commutative-Ring =
    left-zero-law-mul-Ring ring-Commutative-Ring

  right-zero-law-mul-Commutative-Ring :
    (x : type-Commutative-Ring) →
    mul-Commutative-Ring x zero-Commutative-Ring ＝
    zero-Commutative-Ring
  right-zero-law-mul-Commutative-Ring =
    right-zero-law-mul-Ring ring-Commutative-Ring
```

### Commutative rings are commutative semirings

```agda
  multiplicative-commutative-monoid-Commutative-Ring : Commutative-Monoid l
  pr1 multiplicative-commutative-monoid-Commutative-Ring =
    multiplicative-monoid-Ring ring-Commutative-Ring
  pr2 multiplicative-commutative-monoid-Commutative-Ring =
    commutative-mul-Commutative-Ring

  semiring-Commutative-Ring : Semiring l
  semiring-Commutative-Ring = semiring-Ring ring-Commutative-Ring

  commutative-semiring-Commutative-Ring : Commutative-Semiring l
  pr1 commutative-semiring-Commutative-Ring = semiring-Commutative-Ring
  pr2 commutative-semiring-Commutative-Ring = commutative-mul-Commutative-Ring
```

### Computing multiplication with minus one in a ring

```agda
  neg-one-Commutative-Ring : type-Commutative-Ring
  neg-one-Commutative-Ring = neg-one-Ring ring-Commutative-Ring

  mul-neg-one-Commutative-Ring :
    (x : type-Commutative-Ring) →
    mul-Commutative-Ring neg-one-Commutative-Ring x ＝
    neg-Commutative-Ring x
  mul-neg-one-Commutative-Ring = mul-neg-one-Ring ring-Commutative-Ring

  mul-neg-one-Commutative-Ring' :
    (x : type-Commutative-Ring) →
    mul-Commutative-Ring x neg-one-Commutative-Ring ＝
    neg-Commutative-Ring x
  mul-neg-one-Commutative-Ring' = mul-neg-one-Ring' ring-Commutative-Ring

  is-involution-mul-neg-one-Commutative-Ring :
    is-involution (mul-Commutative-Ring neg-one-Commutative-Ring)
  is-involution-mul-neg-one-Commutative-Ring =
    is-involution-mul-neg-one-Ring ring-Commutative-Ring

  is-involution-mul-neg-one-Commutative-Ring' :
    is-involution (mul-Commutative-Ring' neg-one-Commutative-Ring)
  is-involution-mul-neg-one-Commutative-Ring' =
    is-involution-mul-neg-one-Ring' ring-Commutative-Ring
```

### Left and right negative laws for multiplication

```agda
  left-negative-law-mul-Commutative-Ring :
    (x y : type-Commutative-Ring) →
    mul-Commutative-Ring (neg-Commutative-Ring x) y ＝
    neg-Commutative-Ring (mul-Commutative-Ring x y)
  left-negative-law-mul-Commutative-Ring =
    left-negative-law-mul-Ring ring-Commutative-Ring

  right-negative-law-mul-Commutative-Ring :
    (x y : type-Commutative-Ring) →
    mul-Commutative-Ring x (neg-Commutative-Ring y) ＝
    neg-Commutative-Ring (mul-Commutative-Ring x y)
  right-negative-law-mul-Commutative-Ring =
    right-negative-law-mul-Ring ring-Commutative-Ring

  mul-neg-Commutative-Ring :
    (x y : type-Commutative-Ring) →
    mul-Commutative-Ring (neg-Commutative-Ring x) (neg-Commutative-Ring y) ＝
    mul-Commutative-Ring x y
  mul-neg-Commutative-Ring = mul-neg-Ring ring-Commutative-Ring
```

### Distributivity of multiplication over subtraction

```agda
  left-distributive-mul-left-subtraction-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    mul-Commutative-Ring x (left-subtraction-Commutative-Ring y z) ＝
    left-subtraction-Commutative-Ring
      ( mul-Commutative-Ring x y)
      ( mul-Commutative-Ring x z)
  left-distributive-mul-left-subtraction-Commutative-Ring =
    left-distributive-mul-left-subtraction-Ring ring-Commutative-Ring

  right-distributive-mul-left-subtraction-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    mul-Commutative-Ring (left-subtraction-Commutative-Ring x y) z ＝
    left-subtraction-Commutative-Ring
      ( mul-Commutative-Ring x z)
      ( mul-Commutative-Ring y z)
  right-distributive-mul-left-subtraction-Commutative-Ring =
    right-distributive-mul-left-subtraction-Ring ring-Commutative-Ring

  left-distributive-mul-right-subtraction-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    mul-Commutative-Ring x (right-subtraction-Commutative-Ring y z) ＝
    right-subtraction-Commutative-Ring
      ( mul-Commutative-Ring x y)
      ( mul-Commutative-Ring x z)
  left-distributive-mul-right-subtraction-Commutative-Ring =
    left-distributive-mul-right-subtraction-Ring ring-Commutative-Ring

  right-distributive-mul-right-subtraction-Commutative-Ring :
    (x y z : type-Commutative-Ring) →
    mul-Commutative-Ring (right-subtraction-Commutative-Ring x y) z ＝
    right-subtraction-Commutative-Ring
      ( mul-Commutative-Ring x z)
      ( mul-Commutative-Ring y z)
  right-distributive-mul-right-subtraction-Commutative-Ring =
    right-distributive-mul-right-subtraction-Ring ring-Commutative-Ring
```

### Addition of a list of elements in a commutative ring

```agda
  add-list-Commutative-Ring : list type-Commutative-Ring → type-Commutative-Ring
  add-list-Commutative-Ring = add-list-Ring ring-Commutative-Ring

  preserves-concat-add-list-Commutative-Ring :
    (l1 l2 : list type-Commutative-Ring) →
    add-list-Commutative-Ring (concat-list l1 l2) ＝
    add-Commutative-Ring
      ( add-list-Commutative-Ring l1)
      ( add-list-Commutative-Ring l2)
  preserves-concat-add-list-Commutative-Ring =
    preserves-concat-add-list-Ring ring-Commutative-Ring
```

### The sum of `x - y` and `y - z` is `x - z`

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  add-right-subtraction-Commutative-Ring :
    (x y z : type-Commutative-Ring R) →
    add-Commutative-Ring R
      ( right-subtraction-Commutative-Ring R x y)
      ( right-subtraction-Commutative-Ring R y z) ＝
    right-subtraction-Commutative-Ring R x z
  add-right-subtraction-Commutative-Ring =
    add-right-subtraction-Ab (ab-Commutative-Ring R)
```
