# Meet-semilattices

```agda
module order-theory.meet-semilattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.semigroups

open import order-theory.greatest-lower-bounds-posets
open import order-theory.lower-bounds-posets
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

A **meet-semilattice** is a poset in which every pair of elements has a greatest
binary-lower bound. Alternatively, meet-semilattices can be defined algebraically as a set `X` equipped with a binary operation `∧ : X → X → X` satisfying

1. Asociativity: `(x ∧ y) ∧ z ＝ x ∧ (y ∧ z)`,
2. Commutativity: `x ∧ y ＝ y ∧ x`,
3. Idempotency: `x ∧ x ＝ x`.

We will follow the algebraic approach for our principal definition of meet-semilattices, since it requires only one universe level. This is necessary in order to consider the [large category](category-theory.large-categories.md) of meet-semilattices.

## Definitions

### Algebraic definition of meet-semilattices

```agda
module _
  {l : Level} (X : Semigroup l)
  where

  is-meet-semilattice-Semigroup-Prop : Prop l
  is-meet-semilattice-Semigroup-Prop =
    prod-Prop
      ( Π-Prop
        ( type-Semigroup X)
        ( λ x →
          Π-Prop
            ( type-Semigroup X)
            ( λ y →
              Id-Prop
                ( set-Semigroup X)
                ( mul-Semigroup X x y)
                ( mul-Semigroup X y x))))
      ( Π-Prop
        ( type-Semigroup X)
        ( λ x →
          Id-Prop
            ( set-Semigroup X)
            ( mul-Semigroup X x x)
            ( x)))

  is-meet-semilattice-Semigroup : UU l
  is-meet-semilattice-Semigroup =
    type-Prop is-meet-semilattice-Semigroup-Prop

  is-prop-is-meet-semilattice-Semigroup :
    is-prop is-meet-semilattice-Semigroup
  is-prop-is-meet-semilattice-Semigroup =
    is-prop-type-Prop is-meet-semilattice-Semigroup-Prop

Meet-Semilattice : (l : Level) → UU (lsuc l)
Meet-Semilattice l = type-subtype is-meet-semilattice-Semigroup-Prop

module _
  {l : Level} (X : Meet-Semilattice l)
  where

  semigroup-Meet-Semilattice : Semigroup l
  semigroup-Meet-Semilattice = pr1 X

  set-Meet-Semilattice : Set l
  set-Meet-Semilattice = set-Semigroup semigroup-Meet-Semilattice

  type-Meet-Semilattice : UU l
  type-Meet-Semilattice = type-Semigroup semigroup-Meet-Semilattice

  is-set-type-Meet-Semilattice : is-set type-Meet-Semilattice
  is-set-type-Meet-Semilattice =
    is-set-type-Semigroup semigroup-Meet-Semilattice

  meet-Meet-Semilattice : (x y : type-Meet-Semilattice) → type-Meet-Semilattice
  meet-Meet-Semilattice = mul-Semigroup semigroup-Meet-Semilattice

  meet-Meet-Semilattice' : (x y : type-Meet-Semilattice) → type-Meet-Semilattice
  meet-Meet-Semilattice' x y = meet-Meet-Semilattice y x

  private
    _∧_ = meet-Meet-Semilattice

  associative-meet-Meet-Semilattice :
    (x y z : type-Meet-Semilattice) → ((x ∧ y) ∧ z) ＝ (x ∧ (y ∧ z))
  associative-meet-Meet-Semilattice =
    associative-mul-Semigroup semigroup-Meet-Semilattice

  is-meet-semilattice-Meet-Semilattice :
    is-meet-semilattice-Semigroup semigroup-Meet-Semilattice
  is-meet-semilattice-Meet-Semilattice = pr2 X

  commutative-meet-Meet-Semilattice :
    (x y : type-Meet-Semilattice) → (x ∧ y) ＝ (y ∧ x)
  commutative-meet-Meet-Semilattice =
    pr1 is-meet-semilattice-Meet-Semilattice

  idempotent-meet-Meet-Semilattice :
    (x : type-Meet-Semilattice) → (x ∧ x) ＝ x
  idempotent-meet-Meet-Semilattice =
    pr2 is-meet-semilattice-Meet-Semilattice

  leq-Meet-Semilattice-Prop :
    (x y : type-Meet-Semilattice) → Prop l
  leq-Meet-Semilattice-Prop x y =
    Id-Prop set-Meet-Semilattice (x ∧ y) x

  leq-Meet-Semilattice :
    (x y : type-Meet-Semilattice) → UU l
  leq-Meet-Semilattice x y = type-Prop (leq-Meet-Semilattice-Prop x y)

  is-prop-leq-Meet-Semilattice :
    (x y : type-Meet-Semilattice) → is-prop (leq-Meet-Semilattice x y)
  is-prop-leq-Meet-Semilattice x y =
    is-prop-type-Prop (leq-Meet-Semilattice-Prop x y)

  private
    _≤_ = leq-Meet-Semilattice

  refl-leq-Meet-Semilattice :
    (x : type-Meet-Semilattice) → x ≤ x
  refl-leq-Meet-Semilattice x = idempotent-meet-Meet-Semilattice x

  transitive-leq-Meet-Semilattice :
    (x y z : type-Meet-Semilattice) → y ≤ z → x ≤ y → x ≤ z
  transitive-leq-Meet-Semilattice x y z H K =
    equational-reasoning
      x ∧ z
      ＝ (x ∧ y) ∧ z
        by ap (meet-Meet-Semilattice' z) (inv K)
      ＝ x ∧ (y ∧ z)
        by associative-meet-Meet-Semilattice x y z
      ＝ x ∧ y
        by ap (meet-Meet-Semilattice x) H
      ＝ x
        by K

  antisymmetric-leq-Meet-Semilattice :
    (x y : type-Meet-Semilattice) →
    leq-Meet-Semilattice x y → leq-Meet-Semilattice y x → x ＝ y
  antisymmetric-leq-Meet-Semilattice x y H K =
    equational-reasoning
      x ＝ x ∧ y
          by inv H
        ＝ y ∧ x
          by commutative-meet-Meet-Semilattice x y
        ＝ y
          by K

  preorder-Meet-Semilattice : Preorder l l
  pr1 preorder-Meet-Semilattice = type-Meet-Semilattice
  pr1 (pr2 preorder-Meet-Semilattice) = leq-Meet-Semilattice-Prop
  pr1 (pr2 (pr2 preorder-Meet-Semilattice)) = refl-leq-Meet-Semilattice
  pr2 (pr2 (pr2 preorder-Meet-Semilattice)) = transitive-leq-Meet-Semilattice

  poset-Meet-Semilattice : Poset l l
  pr1 poset-Meet-Semilattice = preorder-Meet-Semilattice
  pr2 poset-Meet-Semilattice = antisymmetric-leq-Meet-Semilattice

  is-binary-lower-bound-meet-Meet-Semilattice :
    (x y : type-Meet-Semilattice) →
    is-binary-lower-bound-Poset
      ( poset-Meet-Semilattice)
      ( x)
      ( y)
      ( meet-Meet-Semilattice x y)
  pr1 (is-binary-lower-bound-meet-Meet-Semilattice x y) =
    equational-reasoning
      (x ∧ y) ∧ x
      ＝ x ∧ (x ∧ y)
        by
        commutative-meet-Meet-Semilattice (meet-Meet-Semilattice x y) x
      ＝ (x ∧ x) ∧ y
        by
        inv (associative-meet-Meet-Semilattice x x y)
      ＝ x ∧ y
        by
        ap (meet-Meet-Semilattice' y) (idempotent-meet-Meet-Semilattice x)
  pr2 (is-binary-lower-bound-meet-Meet-Semilattice x y) =
    equational-reasoning
      (x ∧ y) ∧ y
      ＝ x ∧ (y ∧ y)
        by
        associative-meet-Meet-Semilattice x y y
      ＝ x ∧ y
        by
        ap (meet-Meet-Semilattice x) (idempotent-meet-Meet-Semilattice y)

  is-greatest-binary-lower-bound-meet-Meet-Semilattice :
    (x y : type-Meet-Semilattice) →
    is-greatest-binary-lower-bound-Poset
      ( poset-Meet-Semilattice)
      ( x)
      ( y)
      ( meet-Meet-Semilattice x y)
  pr1 (is-greatest-binary-lower-bound-meet-Meet-Semilattice x y) =
    is-binary-lower-bound-meet-Meet-Semilattice x y
  pr2 (is-greatest-binary-lower-bound-meet-Meet-Semilattice x y) w (H , K) =
    equational-reasoning
      w ∧ (x ∧ y)
      ＝ (w ∧ x) ∧ y
        by
        inv (associative-meet-Meet-Semilattice w x y)
      ＝ w ∧ y
        by
        ap (meet-Meet-Semilattice' y) H
      ＝ w
        by K
```

### Order theoretic meet-semilattices

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-meet-semilattice-Poset-Prop : Prop (l1 ⊔ l2)
  is-meet-semilattice-Poset-Prop =
    Π-Prop
      ( type-Poset P)
      ( λ x →
        Π-Prop
          ( type-Poset P)
          ( has-greatest-binary-lower-bound-Poset-Prop P x))

  is-meet-semilattice-Poset : UU (l1 ⊔ l2)
  is-meet-semilattice-Poset = type-Prop is-meet-semilattice-Poset-Prop

  is-prop-is-meet-semilattice-Poset :
    is-prop is-meet-semilattice-Poset
  is-prop-is-meet-semilattice-Poset =
    is-prop-type-Prop is-meet-semilattice-Poset-Prop

Order-Theoretic-Meet-Semilattice : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Order-Theoretic-Meet-Semilattice l1 l2 =
  Σ (Poset l1 l2) is-meet-semilattice-Poset

module _
  {l1 l2 : Level} (A : Order-Theoretic-Meet-Semilattice l1 l2)
  where

  poset-Order-Theoretic-Meet-Semilattice : Poset l1 l2
  poset-Order-Theoretic-Meet-Semilattice = pr1 A

  type-Order-Theoretic-Meet-Semilattice : UU l1
  type-Order-Theoretic-Meet-Semilattice =
    type-Poset poset-Order-Theoretic-Meet-Semilattice

  leq-meet-semilattice-Prop :
    (x y : type-Order-Theoretic-Meet-Semilattice) → Prop l2
  leq-meet-semilattice-Prop =
    leq-Poset-Prop poset-Order-Theoretic-Meet-Semilattice

  leq-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) → UU l2
  leq-Order-Theoretic-Meet-Semilattice =
    leq-Poset poset-Order-Theoretic-Meet-Semilattice

  is-prop-leq-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    is-prop (leq-Order-Theoretic-Meet-Semilattice x y)
  is-prop-leq-Order-Theoretic-Meet-Semilattice =
    is-prop-leq-Poset poset-Order-Theoretic-Meet-Semilattice

  refl-leq-Order-Theoretic-Meet-Semilattice :
    (x : type-Order-Theoretic-Meet-Semilattice) →
    leq-Order-Theoretic-Meet-Semilattice x x
  refl-leq-Order-Theoretic-Meet-Semilattice =
    refl-leq-Poset poset-Order-Theoretic-Meet-Semilattice

  antisymmetric-leq-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    leq-Order-Theoretic-Meet-Semilattice x y →
    leq-Order-Theoretic-Meet-Semilattice y x →
    x ＝ y
  antisymmetric-leq-Order-Theoretic-Meet-Semilattice =
    antisymmetric-leq-Poset poset-Order-Theoretic-Meet-Semilattice

  transitive-leq-Order-Theoretic-Meet-Semilattice :
    (x y z : type-Order-Theoretic-Meet-Semilattice) →
    leq-Order-Theoretic-Meet-Semilattice y z →
    leq-Order-Theoretic-Meet-Semilattice x y →
    leq-Order-Theoretic-Meet-Semilattice x z
  transitive-leq-Order-Theoretic-Meet-Semilattice =
    transitive-leq-Poset poset-Order-Theoretic-Meet-Semilattice

  is-set-type-Order-Theoretic-Meet-Semilattice :
    is-set type-Order-Theoretic-Meet-Semilattice
  is-set-type-Order-Theoretic-Meet-Semilattice =
    is-set-type-Poset poset-Order-Theoretic-Meet-Semilattice

  set-Order-Theoretic-Meet-Semilattice : Set l1
  set-Order-Theoretic-Meet-Semilattice =
    set-Poset poset-Order-Theoretic-Meet-Semilattice

  is-meet-semilattice-Order-Theoretic-Meet-Semilattice :
    is-meet-semilattice-Poset poset-Order-Theoretic-Meet-Semilattice
  is-meet-semilattice-Order-Theoretic-Meet-Semilattice = pr2 A

  meet-semilattice-Order-Theoretic-Meet-Semilattice :
    Order-Theoretic-Meet-Semilattice l1 l2
  pr1 meet-semilattice-Order-Theoretic-Meet-Semilattice =
    poset-Order-Theoretic-Meet-Semilattice
  pr2 meet-semilattice-Order-Theoretic-Meet-Semilattice =
    is-meet-semilattice-Order-Theoretic-Meet-Semilattice

  meet-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    type-Order-Theoretic-Meet-Semilattice
  meet-Order-Theoretic-Meet-Semilattice x y =
    pr1 (is-meet-semilattice-Order-Theoretic-Meet-Semilattice x y)

  is-greatest-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    is-greatest-binary-lower-bound-Poset
      ( poset-Order-Theoretic-Meet-Semilattice)
      ( x)
      ( y)
      ( meet-Order-Theoretic-Meet-Semilattice x y)
  is-greatest-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice x y =
    pr2 (is-meet-semilattice-Order-Theoretic-Meet-Semilattice x y)
```

### Algebraic meet-semilattices

```agda
Algebraic-Meet-Semilattice : (l : Level) → UU (lsuc l)
Algebraic-Meet-Semilattice l =
  Σ ( Semigroup l)
    ( λ X →
      ( (x y : type-Semigroup X) →
        Id (mul-Semigroup X x y) (mul-Semigroup X y x)) ×
      ( (x : type-Semigroup X) → Id (mul-Semigroup X x x) x))
```
