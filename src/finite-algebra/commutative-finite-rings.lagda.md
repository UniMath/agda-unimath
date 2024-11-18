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

A finite ring `A` is said to be **commutative** if its multiplicative operation
is commutative, i.e., if `xy = yx` for all `x, y ∈ A`.

## Definition

### Commutative finite rings

```agda
is-commutative-Ring-𝔽 :
  { l : Level} → Ring-𝔽 l → UU l
is-commutative-Ring-𝔽 A =
  is-commutative-Ring (ring-Ring-𝔽 A)

is-prop-is-commutative-Ring-𝔽 :
  { l : Level} (A : Ring-𝔽 l) → is-prop (is-commutative-Ring-𝔽 A)
is-prop-is-commutative-Ring-𝔽 A =
  is-prop-Π
    ( λ x →
      is-prop-Π
      ( λ y →
        is-set-type-Ring-𝔽 A (mul-Ring-𝔽 A x y) (mul-Ring-𝔽 A y x)))

Commutative-Ring-𝔽 :
  ( l : Level) → UU (lsuc l)
Commutative-Ring-𝔽 l = Σ (Ring-𝔽 l) is-commutative-Ring-𝔽

module _
  {l : Level} (A : Commutative-Ring-𝔽 l)
  where

  finite-ring-Commutative-Ring-𝔽 : Ring-𝔽 l
  finite-ring-Commutative-Ring-𝔽 = pr1 A

  ring-Commutative-Ring-𝔽 : Ring l
  ring-Commutative-Ring-𝔽 = ring-Ring-𝔽 (finite-ring-Commutative-Ring-𝔽)

  commutative-ring-Commutative-Ring-𝔽 : Commutative-Ring l
  pr1 commutative-ring-Commutative-Ring-𝔽 = ring-Commutative-Ring-𝔽
  pr2 commutative-ring-Commutative-Ring-𝔽 = pr2 A

  ab-Commutative-Ring-𝔽 : Ab l
  ab-Commutative-Ring-𝔽 = ab-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  set-Commutative-Ring-𝔽 : Set l
  set-Commutative-Ring-𝔽 = set-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  type-Commutative-Ring-𝔽 : UU l
  type-Commutative-Ring-𝔽 = type-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  is-set-type-Commutative-Ring-𝔽 : is-set type-Commutative-Ring-𝔽
  is-set-type-Commutative-Ring-𝔽 =
    is-set-type-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  finite-type-Commutative-Ring-𝔽 : 𝔽 l
  finite-type-Commutative-Ring-𝔽 =
    finite-type-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  is-finite-type-Commutative-Ring-𝔽 : is-finite (type-Commutative-Ring-𝔽)
  is-finite-type-Commutative-Ring-𝔽 =
    is-finite-type-Ring-𝔽 finite-ring-Commutative-Ring-𝔽
```

### Addition in a commutative finite ring

```agda
  has-associative-add-Commutative-Ring-𝔽 :
    has-associative-mul-Set set-Commutative-Ring-𝔽
  has-associative-add-Commutative-Ring-𝔽 =
    has-associative-add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  add-Commutative-Ring-𝔽 :
    type-Commutative-Ring-𝔽 → type-Commutative-Ring-𝔽 → type-Commutative-Ring-𝔽
  add-Commutative-Ring-𝔽 = add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  add-Commutative-Ring-𝔽' :
    type-Commutative-Ring-𝔽 → type-Commutative-Ring-𝔽 → type-Commutative-Ring-𝔽
  add-Commutative-Ring-𝔽' = add-Ring-𝔽' finite-ring-Commutative-Ring-𝔽

  ap-add-Commutative-Ring-𝔽 :
    {x x' y y' : type-Commutative-Ring-𝔽} →
    (x ＝ x') → (y ＝ y') →
    add-Commutative-Ring-𝔽 x y ＝ add-Commutative-Ring-𝔽 x' y'
  ap-add-Commutative-Ring-𝔽 = ap-add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  associative-add-Commutative-Ring-𝔽 :
    (x y z : type-Commutative-Ring-𝔽) →
    ( add-Commutative-Ring-𝔽 (add-Commutative-Ring-𝔽 x y) z) ＝
    ( add-Commutative-Ring-𝔽 x (add-Commutative-Ring-𝔽 y z))
  associative-add-Commutative-Ring-𝔽 =
    associative-add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  additive-semigroup-Commutative-Ring-𝔽 : Semigroup l
  additive-semigroup-Commutative-Ring-𝔽 = semigroup-Ab ab-Commutative-Ring-𝔽

  is-group-additive-semigroup-Commutative-Ring-𝔽 :
    is-group-Semigroup additive-semigroup-Commutative-Ring-𝔽
  is-group-additive-semigroup-Commutative-Ring-𝔽 =
    is-group-Ab ab-Commutative-Ring-𝔽

  commutative-add-Commutative-Ring-𝔽 :
    (x y : type-Commutative-Ring-𝔽) →
    Id (add-Commutative-Ring-𝔽 x y) (add-Commutative-Ring-𝔽 y x)
  commutative-add-Commutative-Ring-𝔽 = commutative-add-Ab ab-Commutative-Ring-𝔽

  interchange-add-add-Commutative-Ring-𝔽 :
    (x y x' y' : type-Commutative-Ring-𝔽) →
    ( add-Commutative-Ring-𝔽
      ( add-Commutative-Ring-𝔽 x y)
      ( add-Commutative-Ring-𝔽 x' y')) ＝
    ( add-Commutative-Ring-𝔽
      ( add-Commutative-Ring-𝔽 x x')
      ( add-Commutative-Ring-𝔽 y y'))
  interchange-add-add-Commutative-Ring-𝔽 =
    interchange-add-add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  right-swap-add-Commutative-Ring-𝔽 :
    (x y z : type-Commutative-Ring-𝔽) →
    ( add-Commutative-Ring-𝔽 (add-Commutative-Ring-𝔽 x y) z) ＝
    ( add-Commutative-Ring-𝔽 (add-Commutative-Ring-𝔽 x z) y)
  right-swap-add-Commutative-Ring-𝔽 =
    right-swap-add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  left-swap-add-Commutative-Ring-𝔽 :
    (x y z : type-Commutative-Ring-𝔽) →
    ( add-Commutative-Ring-𝔽 x (add-Commutative-Ring-𝔽 y z)) ＝
    ( add-Commutative-Ring-𝔽 y (add-Commutative-Ring-𝔽 x z))
  left-swap-add-Commutative-Ring-𝔽 =
    left-swap-add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  is-equiv-add-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) → is-equiv (add-Commutative-Ring-𝔽 x)
  is-equiv-add-Commutative-Ring-𝔽 = is-equiv-add-Ab ab-Commutative-Ring-𝔽

  is-equiv-add-Commutative-Ring-𝔽' :
    (x : type-Commutative-Ring-𝔽) → is-equiv (add-Commutative-Ring-𝔽' x)
  is-equiv-add-Commutative-Ring-𝔽' = is-equiv-add-Ab' ab-Commutative-Ring-𝔽

  is-binary-equiv-add-Commutative-Ring-𝔽 :
    is-binary-equiv add-Commutative-Ring-𝔽
  pr1 is-binary-equiv-add-Commutative-Ring-𝔽 = is-equiv-add-Commutative-Ring-𝔽'
  pr2 is-binary-equiv-add-Commutative-Ring-𝔽 = is-equiv-add-Commutative-Ring-𝔽

  is-binary-emb-add-Commutative-Ring-𝔽 : is-binary-emb add-Commutative-Ring-𝔽
  is-binary-emb-add-Commutative-Ring-𝔽 =
    is-binary-emb-add-Ab ab-Commutative-Ring-𝔽

  is-emb-add-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) → is-emb (add-Commutative-Ring-𝔽 x)
  is-emb-add-Commutative-Ring-𝔽 = is-emb-add-Ab ab-Commutative-Ring-𝔽

  is-emb-add-Commutative-Ring-𝔽' :
    (x : type-Commutative-Ring-𝔽) → is-emb (add-Commutative-Ring-𝔽' x)
  is-emb-add-Commutative-Ring-𝔽' = is-emb-add-Ab' ab-Commutative-Ring-𝔽

  is-injective-add-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) → is-injective (add-Commutative-Ring-𝔽 x)
  is-injective-add-Commutative-Ring-𝔽 =
    is-injective-add-Ab ab-Commutative-Ring-𝔽

  is-injective-add-Commutative-Ring-𝔽' :
    (x : type-Commutative-Ring-𝔽) → is-injective (add-Commutative-Ring-𝔽' x)
  is-injective-add-Commutative-Ring-𝔽' =
    is-injective-add-Ab' ab-Commutative-Ring-𝔽
```

### The zero element of a commutative finite ring

```agda
  has-zero-Commutative-Ring-𝔽 : is-unital add-Commutative-Ring-𝔽
  has-zero-Commutative-Ring-𝔽 = has-zero-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  zero-Commutative-Ring-𝔽 : type-Commutative-Ring-𝔽
  zero-Commutative-Ring-𝔽 = zero-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  is-zero-Commutative-Ring-𝔽 : type-Commutative-Ring-𝔽 → UU l
  is-zero-Commutative-Ring-𝔽 = is-zero-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  is-nonzero-Commutative-Ring-𝔽 : type-Commutative-Ring-𝔽 → UU l
  is-nonzero-Commutative-Ring-𝔽 =
    is-nonzero-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  is-zero-commutative-finite-ring-Prop : type-Commutative-Ring-𝔽 → Prop l
  is-zero-commutative-finite-ring-Prop =
    is-zero-commutative-ring-Prop commutative-ring-Commutative-Ring-𝔽

  is-nonzero-commutative-finite-ring-Prop : type-Commutative-Ring-𝔽 → Prop l
  is-nonzero-commutative-finite-ring-Prop =
    is-nonzero-commutative-ring-Prop commutative-ring-Commutative-Ring-𝔽

  left-unit-law-add-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) →
    add-Commutative-Ring-𝔽 zero-Commutative-Ring-𝔽 x ＝ x
  left-unit-law-add-Commutative-Ring-𝔽 =
    left-unit-law-add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  right-unit-law-add-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) →
    add-Commutative-Ring-𝔽 x zero-Commutative-Ring-𝔽 ＝ x
  right-unit-law-add-Commutative-Ring-𝔽 =
    right-unit-law-add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽
```

### Additive inverses in a commutative finite ring

```agda
  has-negatives-Commutative-Ring-𝔽 :
    is-group-is-unital-Semigroup
      ( additive-semigroup-Commutative-Ring-𝔽)
      ( has-zero-Commutative-Ring-𝔽)
  has-negatives-Commutative-Ring-𝔽 = has-negatives-Ab ab-Commutative-Ring-𝔽

  neg-Commutative-Ring-𝔽 : type-Commutative-Ring-𝔽 → type-Commutative-Ring-𝔽
  neg-Commutative-Ring-𝔽 = neg-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  left-inverse-law-add-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) →
    add-Commutative-Ring-𝔽 (neg-Commutative-Ring-𝔽 x) x ＝
    zero-Commutative-Ring-𝔽
  left-inverse-law-add-Commutative-Ring-𝔽 =
    left-inverse-law-add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  right-inverse-law-add-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) →
    add-Commutative-Ring-𝔽 x (neg-Commutative-Ring-𝔽 x) ＝
    zero-Commutative-Ring-𝔽
  right-inverse-law-add-Commutative-Ring-𝔽 =
    right-inverse-law-add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  neg-neg-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) →
    neg-Commutative-Ring-𝔽 (neg-Commutative-Ring-𝔽 x) ＝ x
  neg-neg-Commutative-Ring-𝔽 = neg-neg-Ab ab-Commutative-Ring-𝔽

  distributive-neg-add-Commutative-Ring-𝔽 :
    (x y : type-Commutative-Ring-𝔽) →
    neg-Commutative-Ring-𝔽 (add-Commutative-Ring-𝔽 x y) ＝
    add-Commutative-Ring-𝔽 (neg-Commutative-Ring-𝔽 x) (neg-Commutative-Ring-𝔽 y)
  distributive-neg-add-Commutative-Ring-𝔽 =
    distributive-neg-add-Ab ab-Commutative-Ring-𝔽
```

### Multiplication in a commutative finite ring

```agda
  has-associative-mul-Commutative-Ring-𝔽 :
    has-associative-mul-Set set-Commutative-Ring-𝔽
  has-associative-mul-Commutative-Ring-𝔽 =
    has-associative-mul-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  mul-Commutative-Ring-𝔽 :
    (x y : type-Commutative-Ring-𝔽) → type-Commutative-Ring-𝔽
  mul-Commutative-Ring-𝔽 = mul-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  mul-Commutative-Ring-𝔽' :
    (x y : type-Commutative-Ring-𝔽) → type-Commutative-Ring-𝔽
  mul-Commutative-Ring-𝔽' = mul-Ring-𝔽' finite-ring-Commutative-Ring-𝔽

  ap-mul-Commutative-Ring-𝔽 :
    {x x' y y' : type-Commutative-Ring-𝔽} (p : Id x x') (q : Id y y') →
    Id (mul-Commutative-Ring-𝔽 x y) (mul-Commutative-Ring-𝔽 x' y')
  ap-mul-Commutative-Ring-𝔽 p q = ap-binary mul-Commutative-Ring-𝔽 p q

  associative-mul-Commutative-Ring-𝔽 :
    (x y z : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽 (mul-Commutative-Ring-𝔽 x y) z ＝
    mul-Commutative-Ring-𝔽 x (mul-Commutative-Ring-𝔽 y z)
  associative-mul-Commutative-Ring-𝔽 =
    associative-mul-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  multiplicative-semigroup-Commutative-Ring-𝔽 : Semigroup l
  pr1 multiplicative-semigroup-Commutative-Ring-𝔽 = set-Commutative-Ring-𝔽
  pr2 multiplicative-semigroup-Commutative-Ring-𝔽 =
    has-associative-mul-Commutative-Ring-𝔽

  left-distributive-mul-add-Commutative-Ring-𝔽 :
    (x y z : type-Commutative-Ring-𝔽) →
    ( mul-Commutative-Ring-𝔽 x (add-Commutative-Ring-𝔽 y z)) ＝
    ( add-Commutative-Ring-𝔽
      ( mul-Commutative-Ring-𝔽 x y)
      ( mul-Commutative-Ring-𝔽 x z))
  left-distributive-mul-add-Commutative-Ring-𝔽 =
    left-distributive-mul-add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  right-distributive-mul-add-Commutative-Ring-𝔽 :
    (x y z : type-Commutative-Ring-𝔽) →
    ( mul-Commutative-Ring-𝔽 (add-Commutative-Ring-𝔽 x y) z) ＝
    ( add-Commutative-Ring-𝔽
      ( mul-Commutative-Ring-𝔽 x z)
      ( mul-Commutative-Ring-𝔽 y z))
  right-distributive-mul-add-Commutative-Ring-𝔽 =
    right-distributive-mul-add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  commutative-mul-Commutative-Ring-𝔽 :
    (x y : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽 x y ＝ mul-Commutative-Ring-𝔽 y x
  commutative-mul-Commutative-Ring-𝔽 = pr2 A
```

### Multiplicative units in a commutative finite ring

```agda
  is-unital-Commutative-Ring-𝔽 : is-unital mul-Commutative-Ring-𝔽
  is-unital-Commutative-Ring-𝔽 = is-unital-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  multiplicative-monoid-Commutative-Ring-𝔽 : Monoid l
  multiplicative-monoid-Commutative-Ring-𝔽 =
    multiplicative-monoid-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  one-Commutative-Ring-𝔽 : type-Commutative-Ring-𝔽
  one-Commutative-Ring-𝔽 = one-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  left-unit-law-mul-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽 one-Commutative-Ring-𝔽 x ＝ x
  left-unit-law-mul-Commutative-Ring-𝔽 =
    left-unit-law-mul-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  right-unit-law-mul-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽 x one-Commutative-Ring-𝔽 ＝ x
  right-unit-law-mul-Commutative-Ring-𝔽 =
    right-unit-law-mul-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  right-swap-mul-Commutative-Ring-𝔽 :
    (x y z : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽 (mul-Commutative-Ring-𝔽 x y) z ＝
    mul-Commutative-Ring-𝔽 (mul-Commutative-Ring-𝔽 x z) y
  right-swap-mul-Commutative-Ring-𝔽 x y z =
    ( associative-mul-Commutative-Ring-𝔽 x y z) ∙
    ( ( ap
        ( mul-Commutative-Ring-𝔽 x)
        ( commutative-mul-Commutative-Ring-𝔽 y z)) ∙
      ( inv (associative-mul-Commutative-Ring-𝔽 x z y)))

  left-swap-mul-Commutative-Ring-𝔽 :
    (x y z : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽 x (mul-Commutative-Ring-𝔽 y z) ＝
    mul-Commutative-Ring-𝔽 y (mul-Commutative-Ring-𝔽 x z)
  left-swap-mul-Commutative-Ring-𝔽 x y z =
    ( inv (associative-mul-Commutative-Ring-𝔽 x y z)) ∙
    ( ( ap
        ( mul-Commutative-Ring-𝔽' z)
        ( commutative-mul-Commutative-Ring-𝔽 x y)) ∙
      ( associative-mul-Commutative-Ring-𝔽 y x z))

  interchange-mul-mul-Commutative-Ring-𝔽 :
    (x y z w : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽
      ( mul-Commutative-Ring-𝔽 x y)
      ( mul-Commutative-Ring-𝔽 z w) ＝
    mul-Commutative-Ring-𝔽
      ( mul-Commutative-Ring-𝔽 x z)
      ( mul-Commutative-Ring-𝔽 y w)
  interchange-mul-mul-Commutative-Ring-𝔽 =
    interchange-law-commutative-and-associative
      mul-Commutative-Ring-𝔽
      commutative-mul-Commutative-Ring-𝔽
      associative-mul-Commutative-Ring-𝔽
```

### The zero laws for multiplication of a commutative finite ring

```agda
  left-zero-law-mul-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽 zero-Commutative-Ring-𝔽 x ＝
    zero-Commutative-Ring-𝔽
  left-zero-law-mul-Commutative-Ring-𝔽 =
    left-zero-law-mul-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  right-zero-law-mul-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽 x zero-Commutative-Ring-𝔽 ＝
    zero-Commutative-Ring-𝔽
  right-zero-law-mul-Commutative-Ring-𝔽 =
    right-zero-law-mul-Ring-𝔽 finite-ring-Commutative-Ring-𝔽
```

### Commutative rings are commutative finite semirings

```agda
  multiplicative-commutative-monoid-Commutative-Ring-𝔽 : Commutative-Monoid l
  pr1 multiplicative-commutative-monoid-Commutative-Ring-𝔽 =
    multiplicative-monoid-Ring-𝔽 finite-ring-Commutative-Ring-𝔽
  pr2 multiplicative-commutative-monoid-Commutative-Ring-𝔽 =
    commutative-mul-Commutative-Ring-𝔽

  semifinite-ring-Commutative-Ring-𝔽 : Semiring l
  semifinite-ring-Commutative-Ring-𝔽 =
    semiring-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  commutative-semiring-Commutative-Ring-𝔽 : Commutative-Semiring l
  pr1 commutative-semiring-Commutative-Ring-𝔽 =
    semifinite-ring-Commutative-Ring-𝔽
  pr2 commutative-semiring-Commutative-Ring-𝔽 =
    commutative-mul-Commutative-Ring-𝔽
```

### Computing multiplication with minus one in a ring

```agda
  neg-one-Commutative-Ring-𝔽 : type-Commutative-Ring-𝔽
  neg-one-Commutative-Ring-𝔽 = neg-one-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  mul-neg-one-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽 neg-one-Commutative-Ring-𝔽 x ＝
    neg-Commutative-Ring-𝔽 x
  mul-neg-one-Commutative-Ring-𝔽 =
    mul-neg-one-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  mul-neg-one-Commutative-Ring-𝔽' :
    (x : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽 x neg-one-Commutative-Ring-𝔽 ＝
    neg-Commutative-Ring-𝔽 x
  mul-neg-one-Commutative-Ring-𝔽' =
    mul-neg-one-Ring-𝔽' finite-ring-Commutative-Ring-𝔽

  is-involution-mul-neg-one-Commutative-Ring-𝔽 :
    is-involution (mul-Commutative-Ring-𝔽 neg-one-Commutative-Ring-𝔽)
  is-involution-mul-neg-one-Commutative-Ring-𝔽 =
    is-involution-mul-neg-one-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  is-involution-mul-neg-one-Commutative-Ring-𝔽' :
    is-involution (mul-Commutative-Ring-𝔽' neg-one-Commutative-Ring-𝔽)
  is-involution-mul-neg-one-Commutative-Ring-𝔽' =
    is-involution-mul-neg-one-Ring-𝔽' finite-ring-Commutative-Ring-𝔽
```

### Left and right negative laws for multiplication

```agda
  left-negative-law-mul-Commutative-Ring-𝔽 :
    (x y : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽 (neg-Commutative-Ring-𝔽 x) y ＝
    neg-Commutative-Ring-𝔽 (mul-Commutative-Ring-𝔽 x y)
  left-negative-law-mul-Commutative-Ring-𝔽 =
    left-negative-law-mul-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  right-negative-law-mul-Commutative-Ring-𝔽 :
    (x y : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽 x (neg-Commutative-Ring-𝔽 y) ＝
    neg-Commutative-Ring-𝔽 (mul-Commutative-Ring-𝔽 x y)
  right-negative-law-mul-Commutative-Ring-𝔽 =
    right-negative-law-mul-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  mul-neg-Commutative-Ring-𝔽 :
    (x y : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽
      ( neg-Commutative-Ring-𝔽 x)
      ( neg-Commutative-Ring-𝔽 y) ＝
    mul-Commutative-Ring-𝔽 x y
  mul-neg-Commutative-Ring-𝔽 = mul-neg-Ring-𝔽 finite-ring-Commutative-Ring-𝔽
```

### Scalar multiplication of elements of a commutative finite ring by natural numbers

```agda
  mul-nat-scalar-Commutative-Ring-𝔽 :
    ℕ → type-Commutative-Ring-𝔽 → type-Commutative-Ring-𝔽
  mul-nat-scalar-Commutative-Ring-𝔽 =
    mul-nat-scalar-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  ap-mul-nat-scalar-Commutative-Ring-𝔽 :
    {m n : ℕ} {x y : type-Commutative-Ring-𝔽} →
    (m ＝ n) → (x ＝ y) →
    mul-nat-scalar-Commutative-Ring-𝔽 m x ＝
    mul-nat-scalar-Commutative-Ring-𝔽 n y
  ap-mul-nat-scalar-Commutative-Ring-𝔽 =
    ap-mul-nat-scalar-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  left-zero-law-mul-nat-scalar-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) →
    mul-nat-scalar-Commutative-Ring-𝔽 0 x ＝ zero-Commutative-Ring-𝔽
  left-zero-law-mul-nat-scalar-Commutative-Ring-𝔽 =
    left-zero-law-mul-nat-scalar-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  right-zero-law-mul-nat-scalar-Commutative-Ring-𝔽 :
    (n : ℕ) →
    mul-nat-scalar-Commutative-Ring-𝔽 n zero-Commutative-Ring-𝔽 ＝
    zero-Commutative-Ring-𝔽
  right-zero-law-mul-nat-scalar-Commutative-Ring-𝔽 =
    right-zero-law-mul-nat-scalar-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  left-unit-law-mul-nat-scalar-Commutative-Ring-𝔽 :
    (x : type-Commutative-Ring-𝔽) →
    mul-nat-scalar-Commutative-Ring-𝔽 1 x ＝ x
  left-unit-law-mul-nat-scalar-Commutative-Ring-𝔽 =
    left-unit-law-mul-nat-scalar-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  left-nat-scalar-law-mul-Commutative-Ring-𝔽 :
    (n : ℕ) (x y : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽 (mul-nat-scalar-Commutative-Ring-𝔽 n x) y ＝
    mul-nat-scalar-Commutative-Ring-𝔽 n (mul-Commutative-Ring-𝔽 x y)
  left-nat-scalar-law-mul-Commutative-Ring-𝔽 =
    left-nat-scalar-law-mul-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  right-nat-scalar-law-mul-Commutative-Ring-𝔽 :
    (n : ℕ) (x y : type-Commutative-Ring-𝔽) →
    mul-Commutative-Ring-𝔽 x (mul-nat-scalar-Commutative-Ring-𝔽 n y) ＝
    mul-nat-scalar-Commutative-Ring-𝔽 n (mul-Commutative-Ring-𝔽 x y)
  right-nat-scalar-law-mul-Commutative-Ring-𝔽 =
    right-nat-scalar-law-mul-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  left-distributive-mul-nat-scalar-add-Commutative-Ring-𝔽 :
    (n : ℕ) (x y : type-Commutative-Ring-𝔽) →
    mul-nat-scalar-Commutative-Ring-𝔽 n (add-Commutative-Ring-𝔽 x y) ＝
    add-Commutative-Ring-𝔽
      ( mul-nat-scalar-Commutative-Ring-𝔽 n x)
      ( mul-nat-scalar-Commutative-Ring-𝔽 n y)
  left-distributive-mul-nat-scalar-add-Commutative-Ring-𝔽 =
    left-distributive-mul-nat-scalar-add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  right-distributive-mul-nat-scalar-add-Commutative-Ring-𝔽 :
    (m n : ℕ) (x : type-Commutative-Ring-𝔽) →
    mul-nat-scalar-Commutative-Ring-𝔽 (m +ℕ n) x ＝
    add-Commutative-Ring-𝔽
      ( mul-nat-scalar-Commutative-Ring-𝔽 m x)
      ( mul-nat-scalar-Commutative-Ring-𝔽 n x)
  right-distributive-mul-nat-scalar-add-Commutative-Ring-𝔽 =
    right-distributive-mul-nat-scalar-add-Ring-𝔽 finite-ring-Commutative-Ring-𝔽
```

### Addition of a list of elements in a commutative finite ring

```agda
  add-list-Commutative-Ring-𝔽 :
    list type-Commutative-Ring-𝔽 → type-Commutative-Ring-𝔽
  add-list-Commutative-Ring-𝔽 = add-list-Ring-𝔽 finite-ring-Commutative-Ring-𝔽

  preserves-concat-add-list-Commutative-Ring-𝔽 :
    (l1 l2 : list type-Commutative-Ring-𝔽) →
    Id
      ( add-list-Commutative-Ring-𝔽 (concat-list l1 l2))
      ( add-Commutative-Ring-𝔽
        ( add-list-Commutative-Ring-𝔽 l1)
        ( add-list-Commutative-Ring-𝔽 l2))
  preserves-concat-add-list-Commutative-Ring-𝔽 =
    preserves-concat-add-list-Ring-𝔽 finite-ring-Commutative-Ring-𝔽
```

### Equipping a finite type with the structure of a commutative finite ring

```agda
module _
  {l1 : Level}
  (X : 𝔽 l1)
  where

  structure-commutative-ring-𝔽 :
    UU l1
  structure-commutative-ring-𝔽 =
    Σ ( structure-ring-𝔽 X)
      ( λ r → is-commutative-Ring-𝔽 (finite-ring-structure-ring-𝔽 X r))

  finite-commutative-ring-structure-commutative-ring-𝔽 :
    structure-commutative-ring-𝔽 →
    Commutative-Ring-𝔽 l1
  pr1 (finite-commutative-ring-structure-commutative-ring-𝔽 (r , c)) =
    finite-ring-structure-ring-𝔽 X r
  pr2 (finite-commutative-ring-structure-commutative-ring-𝔽 (r , c)) = c

  is-finite-structure-commutative-ring-𝔽 :
    is-finite structure-commutative-ring-𝔽
  is-finite-structure-commutative-ring-𝔽 =
    is-finite-Σ
      ( is-finite-structure-ring-𝔽 X)
      ( λ r →
        is-finite-Π
          ( is-finite-type-𝔽 X)
          ( λ _ →
            is-finite-Π
              ( is-finite-type-𝔽 X)
              ( λ _ → is-finite-eq-𝔽 X)))
```
