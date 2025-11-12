# Commutative finite rings

```agda
module finite-algebra.commutative-finite-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-algebra.finite-rings

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.interchange-law
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

open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A [finite ring](finite-algebra.finite-rings.md) `A` is said to be
{{#concept "commutative" Disambiguation="finite ring" Agda=is-commutative-Finite-Ring Agda=Finite-Commutative-Ring}}
if its multiplicative operation is commutative, i.e., if `xy = yx` for all
`x, y ∈ A`.

## Definition

### Commutative finite rings

```agda
is-commutative-Finite-Ring :
  { l : Level} → Finite-Ring l → UU l
is-commutative-Finite-Ring A =
  is-commutative-Ring (ring-Finite-Ring A)

is-prop-is-commutative-Finite-Ring :
  { l : Level} (A : Finite-Ring l) → is-prop (is-commutative-Finite-Ring A)
is-prop-is-commutative-Finite-Ring A =
  is-prop-Π
    ( λ x →
      is-prop-Π
      ( λ y →
        is-set-type-Finite-Ring A
          ( mul-Finite-Ring A x y)
          ( mul-Finite-Ring A y x)))

Finite-Commutative-Ring :
  ( l : Level) → UU (lsuc l)
Finite-Commutative-Ring l = Σ (Finite-Ring l) is-commutative-Finite-Ring

module _
  {l : Level} (A : Finite-Commutative-Ring l)
  where

  finite-ring-Finite-Commutative-Ring : Finite-Ring l
  finite-ring-Finite-Commutative-Ring = pr1 A

  ring-Finite-Commutative-Ring : Ring l
  ring-Finite-Commutative-Ring =
    ring-Finite-Ring (finite-ring-Finite-Commutative-Ring)

  commutative-ring-Finite-Commutative-Ring : Commutative-Ring l
  pr1 commutative-ring-Finite-Commutative-Ring = ring-Finite-Commutative-Ring
  pr2 commutative-ring-Finite-Commutative-Ring = pr2 A

  ab-Finite-Commutative-Ring : Ab l
  ab-Finite-Commutative-Ring =
    ab-Finite-Ring finite-ring-Finite-Commutative-Ring

  set-Finite-Commutative-Ring : Set l
  set-Finite-Commutative-Ring =
    set-Finite-Ring finite-ring-Finite-Commutative-Ring

  type-Finite-Commutative-Ring : UU l
  type-Finite-Commutative-Ring =
    type-Finite-Ring finite-ring-Finite-Commutative-Ring

  is-set-type-Finite-Commutative-Ring : is-set type-Finite-Commutative-Ring
  is-set-type-Finite-Commutative-Ring =
    is-set-type-Finite-Ring finite-ring-Finite-Commutative-Ring

  finite-type-Finite-Commutative-Ring : Finite-Type l
  finite-type-Finite-Commutative-Ring =
    finite-type-Finite-Ring finite-ring-Finite-Commutative-Ring

  is-finite-type-Finite-Commutative-Ring :
    is-finite (type-Finite-Commutative-Ring)
  is-finite-type-Finite-Commutative-Ring =
    is-finite-type-Finite-Ring finite-ring-Finite-Commutative-Ring
```

### Addition in a commutative finite ring

```agda
  has-associative-add-Finite-Commutative-Ring :
    has-associative-mul-Set set-Finite-Commutative-Ring
  has-associative-add-Finite-Commutative-Ring =
    has-associative-add-Finite-Ring finite-ring-Finite-Commutative-Ring

  add-Finite-Commutative-Ring :
    type-Finite-Commutative-Ring →
    type-Finite-Commutative-Ring →
    type-Finite-Commutative-Ring
  add-Finite-Commutative-Ring =
    add-Finite-Ring finite-ring-Finite-Commutative-Ring

  add-Finite-Commutative-Ring' :
    type-Finite-Commutative-Ring →
    type-Finite-Commutative-Ring →
    type-Finite-Commutative-Ring
  add-Finite-Commutative-Ring' =
    add-Finite-Ring' finite-ring-Finite-Commutative-Ring

  ap-add-Finite-Commutative-Ring :
    {x x' y y' : type-Finite-Commutative-Ring} →
    (x ＝ x') → (y ＝ y') →
    add-Finite-Commutative-Ring x y ＝ add-Finite-Commutative-Ring x' y'
  ap-add-Finite-Commutative-Ring =
    ap-add-Finite-Ring finite-ring-Finite-Commutative-Ring

  associative-add-Finite-Commutative-Ring :
    (x y z : type-Finite-Commutative-Ring) →
    add-Finite-Commutative-Ring (add-Finite-Commutative-Ring x y) z ＝
    add-Finite-Commutative-Ring x (add-Finite-Commutative-Ring y z)
  associative-add-Finite-Commutative-Ring =
    associative-add-Finite-Ring finite-ring-Finite-Commutative-Ring

  additive-semigroup-Finite-Commutative-Ring : Semigroup l
  additive-semigroup-Finite-Commutative-Ring =
    semigroup-Ab ab-Finite-Commutative-Ring

  is-group-additive-semigroup-Finite-Commutative-Ring :
    is-group-Semigroup additive-semigroup-Finite-Commutative-Ring
  is-group-additive-semigroup-Finite-Commutative-Ring =
    is-group-Ab ab-Finite-Commutative-Ring

  commutative-add-Finite-Commutative-Ring :
    (x y : type-Finite-Commutative-Ring) →
    add-Finite-Commutative-Ring x y ＝ add-Finite-Commutative-Ring y x
  commutative-add-Finite-Commutative-Ring =
    commutative-add-Ab ab-Finite-Commutative-Ring

  interchange-add-add-Finite-Commutative-Ring :
    (x y x' y' : type-Finite-Commutative-Ring) →
    ( add-Finite-Commutative-Ring
      ( add-Finite-Commutative-Ring x y)
      ( add-Finite-Commutative-Ring x' y')) ＝
    ( add-Finite-Commutative-Ring
      ( add-Finite-Commutative-Ring x x')
      ( add-Finite-Commutative-Ring y y'))
  interchange-add-add-Finite-Commutative-Ring =
    interchange-add-add-Finite-Ring finite-ring-Finite-Commutative-Ring

  right-swap-add-Finite-Commutative-Ring :
    (x y z : type-Finite-Commutative-Ring) →
    ( add-Finite-Commutative-Ring (add-Finite-Commutative-Ring x y) z) ＝
    ( add-Finite-Commutative-Ring (add-Finite-Commutative-Ring x z) y)
  right-swap-add-Finite-Commutative-Ring =
    right-swap-add-Finite-Ring finite-ring-Finite-Commutative-Ring

  left-swap-add-Finite-Commutative-Ring :
    (x y z : type-Finite-Commutative-Ring) →
    ( add-Finite-Commutative-Ring x (add-Finite-Commutative-Ring y z)) ＝
    ( add-Finite-Commutative-Ring y (add-Finite-Commutative-Ring x z))
  left-swap-add-Finite-Commutative-Ring =
    left-swap-add-Finite-Ring finite-ring-Finite-Commutative-Ring

  is-equiv-add-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) →
    is-equiv (add-Finite-Commutative-Ring x)
  is-equiv-add-Finite-Commutative-Ring =
    is-equiv-add-Ab ab-Finite-Commutative-Ring

  is-equiv-add-Finite-Commutative-Ring' :
    (x : type-Finite-Commutative-Ring) →
    is-equiv (add-Finite-Commutative-Ring' x)
  is-equiv-add-Finite-Commutative-Ring' =
    is-equiv-add-Ab' ab-Finite-Commutative-Ring

  is-binary-equiv-add-Finite-Commutative-Ring :
    is-binary-equiv add-Finite-Commutative-Ring
  pr1 is-binary-equiv-add-Finite-Commutative-Ring =
    is-equiv-add-Finite-Commutative-Ring'
  pr2 is-binary-equiv-add-Finite-Commutative-Ring =
    is-equiv-add-Finite-Commutative-Ring

  is-binary-emb-add-Finite-Commutative-Ring :
    is-binary-emb add-Finite-Commutative-Ring
  is-binary-emb-add-Finite-Commutative-Ring =
    is-binary-emb-add-Ab ab-Finite-Commutative-Ring

  is-emb-add-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) → is-emb (add-Finite-Commutative-Ring x)
  is-emb-add-Finite-Commutative-Ring = is-emb-add-Ab ab-Finite-Commutative-Ring

  is-emb-add-Finite-Commutative-Ring' :
    (x : type-Finite-Commutative-Ring) → is-emb (add-Finite-Commutative-Ring' x)
  is-emb-add-Finite-Commutative-Ring' =
    is-emb-add-Ab' ab-Finite-Commutative-Ring

  is-injective-add-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) →
    is-injective (add-Finite-Commutative-Ring x)
  is-injective-add-Finite-Commutative-Ring =
    is-injective-add-Ab ab-Finite-Commutative-Ring

  is-injective-add-Finite-Commutative-Ring' :
    (x : type-Finite-Commutative-Ring) →
    is-injective (add-Finite-Commutative-Ring' x)
  is-injective-add-Finite-Commutative-Ring' =
    is-injective-add-Ab' ab-Finite-Commutative-Ring
```

### The zero element of a commutative finite ring

```agda
  has-zero-Finite-Commutative-Ring : is-unital add-Finite-Commutative-Ring
  has-zero-Finite-Commutative-Ring =
    has-zero-Finite-Ring finite-ring-Finite-Commutative-Ring

  zero-Finite-Commutative-Ring : type-Finite-Commutative-Ring
  zero-Finite-Commutative-Ring =
    zero-Finite-Ring finite-ring-Finite-Commutative-Ring

  is-zero-Finite-Commutative-Ring : type-Finite-Commutative-Ring → UU l
  is-zero-Finite-Commutative-Ring =
    is-zero-Finite-Ring finite-ring-Finite-Commutative-Ring

  is-nonzero-Finite-Commutative-Ring : type-Finite-Commutative-Ring → UU l
  is-nonzero-Finite-Commutative-Ring =
    is-nonzero-Finite-Ring finite-ring-Finite-Commutative-Ring

  is-zero-commutative-finite-ring-Prop : type-Finite-Commutative-Ring → Prop l
  is-zero-commutative-finite-ring-Prop =
    is-zero-commutative-ring-Prop commutative-ring-Finite-Commutative-Ring

  is-nonzero-commutative-finite-ring-Prop :
    type-Finite-Commutative-Ring → Prop l
  is-nonzero-commutative-finite-ring-Prop =
    is-nonzero-commutative-ring-Prop commutative-ring-Finite-Commutative-Ring

  left-unit-law-add-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) →
    add-Finite-Commutative-Ring zero-Finite-Commutative-Ring x ＝ x
  left-unit-law-add-Finite-Commutative-Ring =
    left-unit-law-add-Finite-Ring finite-ring-Finite-Commutative-Ring

  right-unit-law-add-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) →
    add-Finite-Commutative-Ring x zero-Finite-Commutative-Ring ＝ x
  right-unit-law-add-Finite-Commutative-Ring =
    right-unit-law-add-Finite-Ring finite-ring-Finite-Commutative-Ring
```

### Additive inverses in a commutative finite ring

```agda
  has-negatives-Finite-Commutative-Ring :
    is-group-is-unital-Semigroup
      ( additive-semigroup-Finite-Commutative-Ring)
      ( has-zero-Finite-Commutative-Ring)
  has-negatives-Finite-Commutative-Ring =
    has-negatives-Ab ab-Finite-Commutative-Ring

  neg-Finite-Commutative-Ring :
    type-Finite-Commutative-Ring → type-Finite-Commutative-Ring
  neg-Finite-Commutative-Ring =
    neg-Finite-Ring finite-ring-Finite-Commutative-Ring

  left-inverse-law-add-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) →
    add-Finite-Commutative-Ring (neg-Finite-Commutative-Ring x) x ＝
    zero-Finite-Commutative-Ring
  left-inverse-law-add-Finite-Commutative-Ring =
    left-inverse-law-add-Finite-Ring finite-ring-Finite-Commutative-Ring

  right-inverse-law-add-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) →
    add-Finite-Commutative-Ring x (neg-Finite-Commutative-Ring x) ＝
    zero-Finite-Commutative-Ring
  right-inverse-law-add-Finite-Commutative-Ring =
    right-inverse-law-add-Finite-Ring finite-ring-Finite-Commutative-Ring

  neg-neg-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) →
    neg-Finite-Commutative-Ring (neg-Finite-Commutative-Ring x) ＝ x
  neg-neg-Finite-Commutative-Ring = neg-neg-Ab ab-Finite-Commutative-Ring

  distributive-neg-add-Finite-Commutative-Ring :
    (x y : type-Finite-Commutative-Ring) →
    neg-Finite-Commutative-Ring (add-Finite-Commutative-Ring x y) ＝
    add-Finite-Commutative-Ring
      ( neg-Finite-Commutative-Ring x)
      ( neg-Finite-Commutative-Ring y)
  distributive-neg-add-Finite-Commutative-Ring =
    distributive-neg-add-Ab ab-Finite-Commutative-Ring
```

### Multiplication in a commutative finite ring

```agda
  has-associative-mul-Finite-Commutative-Ring :
    has-associative-mul-Set set-Finite-Commutative-Ring
  has-associative-mul-Finite-Commutative-Ring =
    has-associative-mul-Finite-Ring finite-ring-Finite-Commutative-Ring

  mul-Finite-Commutative-Ring :
    (x y : type-Finite-Commutative-Ring) → type-Finite-Commutative-Ring
  mul-Finite-Commutative-Ring =
    mul-Finite-Ring finite-ring-Finite-Commutative-Ring

  mul-Finite-Commutative-Ring' :
    (x y : type-Finite-Commutative-Ring) → type-Finite-Commutative-Ring
  mul-Finite-Commutative-Ring' =
    mul-Finite-Ring' finite-ring-Finite-Commutative-Ring

  ap-mul-Finite-Commutative-Ring :
    {x x' y y' : type-Finite-Commutative-Ring} (p : x ＝ x') (q : y ＝ y') →
    mul-Finite-Commutative-Ring x y ＝ mul-Finite-Commutative-Ring x' y'
  ap-mul-Finite-Commutative-Ring p q = ap-binary mul-Finite-Commutative-Ring p q

  associative-mul-Finite-Commutative-Ring :
    (x y z : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring (mul-Finite-Commutative-Ring x y) z ＝
    mul-Finite-Commutative-Ring x (mul-Finite-Commutative-Ring y z)
  associative-mul-Finite-Commutative-Ring =
    associative-mul-Finite-Ring finite-ring-Finite-Commutative-Ring

  multiplicative-semigroup-Finite-Commutative-Ring : Semigroup l
  pr1 multiplicative-semigroup-Finite-Commutative-Ring =
    set-Finite-Commutative-Ring
  pr2 multiplicative-semigroup-Finite-Commutative-Ring =
    has-associative-mul-Finite-Commutative-Ring

  left-distributive-mul-add-Finite-Commutative-Ring :
    (x y z : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring x (add-Finite-Commutative-Ring y z) ＝
    add-Finite-Commutative-Ring
      ( mul-Finite-Commutative-Ring x y)
      ( mul-Finite-Commutative-Ring x z)
  left-distributive-mul-add-Finite-Commutative-Ring =
    left-distributive-mul-add-Finite-Ring finite-ring-Finite-Commutative-Ring

  right-distributive-mul-add-Finite-Commutative-Ring :
    (x y z : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring (add-Finite-Commutative-Ring x y) z ＝
    add-Finite-Commutative-Ring
      ( mul-Finite-Commutative-Ring x z)
      ( mul-Finite-Commutative-Ring y z)
  right-distributive-mul-add-Finite-Commutative-Ring =
    right-distributive-mul-add-Finite-Ring finite-ring-Finite-Commutative-Ring

  commutative-mul-Finite-Commutative-Ring :
    (x y : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring x y ＝ mul-Finite-Commutative-Ring y x
  commutative-mul-Finite-Commutative-Ring = pr2 A
```

### Multiplicative units in a commutative finite ring

```agda
  is-unital-Finite-Commutative-Ring : is-unital mul-Finite-Commutative-Ring
  is-unital-Finite-Commutative-Ring =
    is-unital-Finite-Ring finite-ring-Finite-Commutative-Ring

  multiplicative-monoid-Finite-Commutative-Ring : Monoid l
  multiplicative-monoid-Finite-Commutative-Ring =
    multiplicative-monoid-Finite-Ring finite-ring-Finite-Commutative-Ring

  one-Finite-Commutative-Ring : type-Finite-Commutative-Ring
  one-Finite-Commutative-Ring =
    one-Finite-Ring finite-ring-Finite-Commutative-Ring

  left-unit-law-mul-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring one-Finite-Commutative-Ring x ＝ x
  left-unit-law-mul-Finite-Commutative-Ring =
    left-unit-law-mul-Finite-Ring finite-ring-Finite-Commutative-Ring

  right-unit-law-mul-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring x one-Finite-Commutative-Ring ＝ x
  right-unit-law-mul-Finite-Commutative-Ring =
    right-unit-law-mul-Finite-Ring finite-ring-Finite-Commutative-Ring

  right-swap-mul-Finite-Commutative-Ring :
    (x y z : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring (mul-Finite-Commutative-Ring x y) z ＝
    mul-Finite-Commutative-Ring (mul-Finite-Commutative-Ring x z) y
  right-swap-mul-Finite-Commutative-Ring x y z =
    ( associative-mul-Finite-Commutative-Ring x y z) ∙
    ( ( ap
        ( mul-Finite-Commutative-Ring x)
        ( commutative-mul-Finite-Commutative-Ring y z)) ∙
      ( inv (associative-mul-Finite-Commutative-Ring x z y)))

  left-swap-mul-Finite-Commutative-Ring :
    (x y z : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring x (mul-Finite-Commutative-Ring y z) ＝
    mul-Finite-Commutative-Ring y (mul-Finite-Commutative-Ring x z)
  left-swap-mul-Finite-Commutative-Ring x y z =
    ( inv (associative-mul-Finite-Commutative-Ring x y z)) ∙
    ( ( ap
        ( mul-Finite-Commutative-Ring' z)
        ( commutative-mul-Finite-Commutative-Ring x y)) ∙
      ( associative-mul-Finite-Commutative-Ring y x z))

  interchange-mul-mul-Finite-Commutative-Ring :
    (x y z w : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring
      ( mul-Finite-Commutative-Ring x y)
      ( mul-Finite-Commutative-Ring z w) ＝
    mul-Finite-Commutative-Ring
      ( mul-Finite-Commutative-Ring x z)
      ( mul-Finite-Commutative-Ring y w)
  interchange-mul-mul-Finite-Commutative-Ring =
    interchange-law-commutative-and-associative
      mul-Finite-Commutative-Ring
      commutative-mul-Finite-Commutative-Ring
      associative-mul-Finite-Commutative-Ring
```

### The zero laws for multiplication of a commutative finite ring

```agda
  left-zero-law-mul-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring zero-Finite-Commutative-Ring x ＝
    zero-Finite-Commutative-Ring
  left-zero-law-mul-Finite-Commutative-Ring =
    left-zero-law-mul-Finite-Ring finite-ring-Finite-Commutative-Ring

  right-zero-law-mul-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring x zero-Finite-Commutative-Ring ＝
    zero-Finite-Commutative-Ring
  right-zero-law-mul-Finite-Commutative-Ring =
    right-zero-law-mul-Finite-Ring finite-ring-Finite-Commutative-Ring
```

### Commutative rings are commutative finite semirings

```agda
  multiplicative-commutative-monoid-Finite-Commutative-Ring :
    Commutative-Monoid l
  pr1 multiplicative-commutative-monoid-Finite-Commutative-Ring =
    multiplicative-monoid-Finite-Ring finite-ring-Finite-Commutative-Ring
  pr2 multiplicative-commutative-monoid-Finite-Commutative-Ring =
    commutative-mul-Finite-Commutative-Ring

  semifinite-ring-Finite-Commutative-Ring : Semiring l
  semifinite-ring-Finite-Commutative-Ring =
    semiring-Finite-Ring finite-ring-Finite-Commutative-Ring

  commutative-semiring-Finite-Commutative-Ring : Commutative-Semiring l
  pr1 commutative-semiring-Finite-Commutative-Ring =
    semifinite-ring-Finite-Commutative-Ring
  pr2 commutative-semiring-Finite-Commutative-Ring =
    commutative-mul-Finite-Commutative-Ring
```

### Computing multiplication with minus one in a ring

```agda
  neg-one-Finite-Commutative-Ring : type-Finite-Commutative-Ring
  neg-one-Finite-Commutative-Ring =
    neg-one-Finite-Ring finite-ring-Finite-Commutative-Ring

  mul-neg-one-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring neg-one-Finite-Commutative-Ring x ＝
    neg-Finite-Commutative-Ring x
  mul-neg-one-Finite-Commutative-Ring =
    mul-neg-one-Finite-Ring finite-ring-Finite-Commutative-Ring

  mul-neg-one-Finite-Commutative-Ring' :
    (x : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring x neg-one-Finite-Commutative-Ring ＝
    neg-Finite-Commutative-Ring x
  mul-neg-one-Finite-Commutative-Ring' =
    mul-neg-one-Finite-Ring' finite-ring-Finite-Commutative-Ring

  is-involution-mul-neg-one-Finite-Commutative-Ring :
    is-involution (mul-Finite-Commutative-Ring neg-one-Finite-Commutative-Ring)
  is-involution-mul-neg-one-Finite-Commutative-Ring =
    is-involution-mul-neg-one-Finite-Ring finite-ring-Finite-Commutative-Ring

  is-involution-mul-neg-one-Finite-Commutative-Ring' :
    is-involution (mul-Finite-Commutative-Ring' neg-one-Finite-Commutative-Ring)
  is-involution-mul-neg-one-Finite-Commutative-Ring' =
    is-involution-mul-neg-one-Finite-Ring' finite-ring-Finite-Commutative-Ring
```

### Left and right negative laws for multiplication

```agda
  left-negative-law-mul-Finite-Commutative-Ring :
    (x y : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring (neg-Finite-Commutative-Ring x) y ＝
    neg-Finite-Commutative-Ring (mul-Finite-Commutative-Ring x y)
  left-negative-law-mul-Finite-Commutative-Ring =
    left-negative-law-mul-Finite-Ring finite-ring-Finite-Commutative-Ring

  right-negative-law-mul-Finite-Commutative-Ring :
    (x y : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring x (neg-Finite-Commutative-Ring y) ＝
    neg-Finite-Commutative-Ring (mul-Finite-Commutative-Ring x y)
  right-negative-law-mul-Finite-Commutative-Ring =
    right-negative-law-mul-Finite-Ring finite-ring-Finite-Commutative-Ring

  mul-neg-Finite-Commutative-Ring :
    (x y : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring
      ( neg-Finite-Commutative-Ring x)
      ( neg-Finite-Commutative-Ring y) ＝
    mul-Finite-Commutative-Ring x y
  mul-neg-Finite-Commutative-Ring =
    mul-neg-Finite-Ring finite-ring-Finite-Commutative-Ring
```

### Scalar multiplication of elements of a commutative finite ring by natural numbers

```agda
  mul-nat-scalar-Finite-Commutative-Ring :
    ℕ → type-Finite-Commutative-Ring → type-Finite-Commutative-Ring
  mul-nat-scalar-Finite-Commutative-Ring =
    mul-nat-scalar-Finite-Ring finite-ring-Finite-Commutative-Ring

  ap-mul-nat-scalar-Finite-Commutative-Ring :
    {m n : ℕ} {x y : type-Finite-Commutative-Ring} →
    (m ＝ n) → (x ＝ y) →
    mul-nat-scalar-Finite-Commutative-Ring m x ＝
    mul-nat-scalar-Finite-Commutative-Ring n y
  ap-mul-nat-scalar-Finite-Commutative-Ring =
    ap-mul-nat-scalar-Finite-Ring finite-ring-Finite-Commutative-Ring

  left-zero-law-mul-nat-scalar-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) →
    mul-nat-scalar-Finite-Commutative-Ring 0 x ＝ zero-Finite-Commutative-Ring
  left-zero-law-mul-nat-scalar-Finite-Commutative-Ring =
    left-zero-law-mul-nat-scalar-Finite-Ring finite-ring-Finite-Commutative-Ring

  right-zero-law-mul-nat-scalar-Finite-Commutative-Ring :
    (n : ℕ) →
    mul-nat-scalar-Finite-Commutative-Ring n zero-Finite-Commutative-Ring ＝
    zero-Finite-Commutative-Ring
  right-zero-law-mul-nat-scalar-Finite-Commutative-Ring =
    right-zero-law-mul-nat-scalar-Finite-Ring
      finite-ring-Finite-Commutative-Ring

  left-unit-law-mul-nat-scalar-Finite-Commutative-Ring :
    (x : type-Finite-Commutative-Ring) →
    mul-nat-scalar-Finite-Commutative-Ring 1 x ＝ x
  left-unit-law-mul-nat-scalar-Finite-Commutative-Ring =
    left-unit-law-mul-nat-scalar-Finite-Ring
      finite-ring-Finite-Commutative-Ring

  left-mul-multiple-Finite-Commutative-Ring :
    (n : ℕ) (x y : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring (mul-nat-scalar-Finite-Commutative-Ring n x) y ＝
    mul-nat-scalar-Finite-Commutative-Ring n (mul-Finite-Commutative-Ring x y)
  left-mul-multiple-Finite-Commutative-Ring =
    left-mul-multiple-Finite-Ring finite-ring-Finite-Commutative-Ring

  right-mul-multiple-Finite-Commutative-Ring :
    (n : ℕ) (x y : type-Finite-Commutative-Ring) →
    mul-Finite-Commutative-Ring x (mul-nat-scalar-Finite-Commutative-Ring n y) ＝
    mul-nat-scalar-Finite-Commutative-Ring n (mul-Finite-Commutative-Ring x y)
  right-mul-multiple-Finite-Commutative-Ring =
    right-mul-multiple-Finite-Ring finite-ring-Finite-Commutative-Ring

  left-distributive-multiple-add-Finite-Commutative-Ring :
    (n : ℕ) {x y : type-Finite-Commutative-Ring} →
    mul-nat-scalar-Finite-Commutative-Ring n (add-Finite-Commutative-Ring x y) ＝
    add-Finite-Commutative-Ring
      ( mul-nat-scalar-Finite-Commutative-Ring n x)
      ( mul-nat-scalar-Finite-Commutative-Ring n y)
  left-distributive-multiple-add-Finite-Commutative-Ring =
    left-distributive-multiple-add-Finite-Ring
      finite-ring-Finite-Commutative-Ring

  right-distributive-multiple-add-Finite-Commutative-Ring :
    (m n : ℕ) {x : type-Finite-Commutative-Ring} →
    mul-nat-scalar-Finite-Commutative-Ring (m +ℕ n) x ＝
    add-Finite-Commutative-Ring
      ( mul-nat-scalar-Finite-Commutative-Ring m x)
      ( mul-nat-scalar-Finite-Commutative-Ring n x)
  right-distributive-multiple-add-Finite-Commutative-Ring =
    right-distributive-multiple-add-Finite-Ring
      finite-ring-Finite-Commutative-Ring
```

### Addition of a list of elements in a commutative finite ring

```agda
  add-list-Finite-Commutative-Ring :
    list type-Finite-Commutative-Ring → type-Finite-Commutative-Ring
  add-list-Finite-Commutative-Ring =
    add-list-Finite-Ring finite-ring-Finite-Commutative-Ring

  preserves-concat-add-list-Finite-Commutative-Ring :
    (l1 l2 : list type-Finite-Commutative-Ring) →
    ( add-list-Finite-Commutative-Ring (concat-list l1 l2)) ＝
    ( add-Finite-Commutative-Ring
      ( add-list-Finite-Commutative-Ring l1)
      ( add-list-Finite-Commutative-Ring l2))
  preserves-concat-add-list-Finite-Commutative-Ring =
    preserves-concat-add-list-Finite-Ring finite-ring-Finite-Commutative-Ring
```

### Equipping a finite type with the structure of a commutative finite ring

```agda
module _
  {l1 : Level}
  (X : Finite-Type l1)
  where

  structure-commutative-ring-Finite-Type :
    UU l1
  structure-commutative-ring-Finite-Type =
    Σ ( structure-ring-Finite-Type X)
      ( λ r →
        is-commutative-Finite-Ring (finite-ring-structure-ring-Finite-Type X r))

  finite-commutative-ring-structure-commutative-ring-Finite-Type :
    structure-commutative-ring-Finite-Type →
    Finite-Commutative-Ring l1
  pr1 (finite-commutative-ring-structure-commutative-ring-Finite-Type (r , c)) =
    finite-ring-structure-ring-Finite-Type X r
  pr2 (finite-commutative-ring-structure-commutative-ring-Finite-Type (r , c)) =
    c

  is-finite-structure-commutative-ring-Finite-Type :
    is-finite structure-commutative-ring-Finite-Type
  is-finite-structure-commutative-ring-Finite-Type =
    is-finite-Σ
      ( is-finite-structure-ring-Finite-Type X)
      ( λ r →
        is-finite-Π
          ( is-finite-type-Finite-Type X)
          ( λ _ →
            is-finite-Π
              ( is-finite-type-Finite-Type X)
              ( λ _ → is-finite-eq-Finite-Type X)))
```
