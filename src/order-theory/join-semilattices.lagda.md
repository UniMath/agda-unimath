# Join-semilattices

```agda
module order-theory.join-semilattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.semigroups

open import order-theory.least-upper-bounds-posets
open import order-theory.posets
open import order-theory.preorders
open import order-theory.upper-bounds-posets
```

</details>

## Idea

A **join-semilattice** is a poset in which every pair of elements has a least
binary upper bound. Alternatively, join-semilattices can be defined
algebraically as a set `X` equipped with a binary operation `∧ : X → X → X`
satisfying

1. Asociativity: `(x ∧ y) ∧ z ＝ x ∧ (y ∧ z)`,
2. Commutativity: `x ∧ y ＝ y ∧ x`,
3. Idempotency: `x ∧ x ＝ x`.

Note that this definition is identical to the definition of
[meet-semilattices](order-theory.meet-semilattices.md). We will follow the
algebraic approach for our principal definition of join-semilattices, since it
requires only one universe level. This is necessary in order to consider the
[large category](category-theory.large-categories.md) of join-semilattices.

## Definitions

### The predicate on semigroups of being a join-semilattice

```agda
module _
  {l : Level} (X : Semigroup l)
  where

  is-join-semilattice-prop-Semigroup : Prop l
  is-join-semilattice-prop-Semigroup =
    product-Prop
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

  is-join-semilattice-Semigroup : UU l
  is-join-semilattice-Semigroup =
    type-Prop is-join-semilattice-prop-Semigroup

  is-prop-is-join-semilattice-Semigroup :
    is-prop is-join-semilattice-Semigroup
  is-prop-is-join-semilattice-Semigroup =
    is-prop-type-Prop is-join-semilattice-prop-Semigroup
```

### The algebraic definition of join-semilattices

```agda
Join-Semilattice : (l : Level) → UU (lsuc l)
Join-Semilattice l = type-subtype is-join-semilattice-prop-Semigroup

module _
  {l : Level} (X : Join-Semilattice l)
  where

  semigroup-Join-Semilattice : Semigroup l
  semigroup-Join-Semilattice = pr1 X

  set-Join-Semilattice : Set l
  set-Join-Semilattice = set-Semigroup semigroup-Join-Semilattice

  type-Join-Semilattice : UU l
  type-Join-Semilattice = type-Semigroup semigroup-Join-Semilattice

  is-set-type-Join-Semilattice : is-set type-Join-Semilattice
  is-set-type-Join-Semilattice =
    is-set-type-Semigroup semigroup-Join-Semilattice

  join-Join-Semilattice : (x y : type-Join-Semilattice) → type-Join-Semilattice
  join-Join-Semilattice = mul-Semigroup semigroup-Join-Semilattice

  join-Join-Semilattice' : (x y : type-Join-Semilattice) → type-Join-Semilattice
  join-Join-Semilattice' x y = join-Join-Semilattice y x

  private
    _∨_ = join-Join-Semilattice

  associative-join-Join-Semilattice :
    (x y z : type-Join-Semilattice) → ((x ∨ y) ∨ z) ＝ (x ∨ (y ∨ z))
  associative-join-Join-Semilattice =
    associative-mul-Semigroup semigroup-Join-Semilattice

  is-join-semilattice-Join-Semilattice :
    is-join-semilattice-Semigroup semigroup-Join-Semilattice
  is-join-semilattice-Join-Semilattice = pr2 X

  commutative-join-Join-Semilattice :
    (x y : type-Join-Semilattice) → (x ∨ y) ＝ (y ∨ x)
  commutative-join-Join-Semilattice =
    pr1 is-join-semilattice-Join-Semilattice

  idempotent-join-Join-Semilattice :
    (x : type-Join-Semilattice) → (x ∨ x) ＝ x
  idempotent-join-Join-Semilattice =
    pr2 is-join-semilattice-Join-Semilattice

  leq-Join-Semilattice-Prop :
    (x y : type-Join-Semilattice) → Prop l
  leq-Join-Semilattice-Prop x y =
    Id-Prop set-Join-Semilattice (x ∨ y) y

  leq-Join-Semilattice :
    (x y : type-Join-Semilattice) → UU l
  leq-Join-Semilattice x y = type-Prop (leq-Join-Semilattice-Prop x y)

  is-prop-leq-Join-Semilattice :
    (x y : type-Join-Semilattice) → is-prop (leq-Join-Semilattice x y)
  is-prop-leq-Join-Semilattice x y =
    is-prop-type-Prop (leq-Join-Semilattice-Prop x y)

  private
    _≤_ = leq-Join-Semilattice

  refl-leq-Join-Semilattice : is-reflexive leq-Join-Semilattice
  refl-leq-Join-Semilattice x = idempotent-join-Join-Semilattice x

  transitive-leq-Join-Semilattice : is-transitive leq-Join-Semilattice
  transitive-leq-Join-Semilattice x y z H K =
    equational-reasoning
      x ∨ z
      ＝ x ∨ (y ∨ z)
        by ap (join-Join-Semilattice x) (inv H)
      ＝ (x ∨ y) ∨ z
        by inv (associative-join-Join-Semilattice x y z)
      ＝ y ∨ z
        by ap (join-Join-Semilattice' z) K
      ＝ z
        by H

  antisymmetric-leq-Join-Semilattice : is-antisymmetric leq-Join-Semilattice
  antisymmetric-leq-Join-Semilattice x y H K =
    equational-reasoning
      x ＝ y ∨ x
          by inv K
        ＝ x ∨ y
          by commutative-join-Join-Semilattice y x
        ＝ y
          by H

  preorder-Join-Semilattice : Preorder l l
  pr1 preorder-Join-Semilattice = type-Join-Semilattice
  pr1 (pr2 preorder-Join-Semilattice) = leq-Join-Semilattice-Prop
  pr1 (pr2 (pr2 preorder-Join-Semilattice)) = refl-leq-Join-Semilattice
  pr2 (pr2 (pr2 preorder-Join-Semilattice)) = transitive-leq-Join-Semilattice

  poset-Join-Semilattice : Poset l l
  pr1 poset-Join-Semilattice = preorder-Join-Semilattice
  pr2 poset-Join-Semilattice = antisymmetric-leq-Join-Semilattice

  is-binary-upper-bound-join-Join-Semilattice :
    (x y : type-Join-Semilattice) →
    is-binary-upper-bound-Poset
      ( poset-Join-Semilattice)
      ( x)
      ( y)
      ( join-Join-Semilattice x y)
  pr1 (is-binary-upper-bound-join-Join-Semilattice x y) =
    equational-reasoning
      x ∨ (x ∨ y)
      ＝ (x ∨ x) ∨ y
        by
        inv (associative-join-Join-Semilattice x x y)
      ＝ x ∨ y
        by
        ap (join-Join-Semilattice' y) (idempotent-join-Join-Semilattice x)
  pr2 (is-binary-upper-bound-join-Join-Semilattice x y) =
    equational-reasoning
      y ∨ (x ∨ y)
      ＝ (x ∨ y) ∨ y
        by commutative-join-Join-Semilattice y (x ∨ y)
      ＝ x ∨ (y ∨ y)
        by
        associative-join-Join-Semilattice x y y
      ＝ x ∨ y
        by
        ap (join-Join-Semilattice x) (idempotent-join-Join-Semilattice y)

  is-least-binary-upper-bound-join-Join-Semilattice :
    (x y : type-Join-Semilattice) →
    is-least-binary-upper-bound-Poset
      ( poset-Join-Semilattice)
      ( x)
      ( y)
      ( join-Join-Semilattice x y)
  is-least-binary-upper-bound-join-Join-Semilattice x y =
    prove-is-least-binary-upper-bound-Poset
      ( poset-Join-Semilattice)
      ( is-binary-upper-bound-join-Join-Semilattice x y)
      ( λ z (H , K) →
        equational-reasoning
          (x ∨ y) ∨ z
          ＝ x ∨ (y ∨ z)
            by associative-join-Join-Semilattice x y z
          ＝ x ∨ z
            by ap (join-Join-Semilattice x) K
          ＝ z
            by H)

  leq-left-join-Join-Semilattice :
    (a b : type-Join-Semilattice) →
    leq-Join-Semilattice a (join-Join-Semilattice a b)
  leq-left-join-Join-Semilattice a b =
    equational-reasoning
      a ∨ (a ∨ b)
      ＝ (a ∨ a) ∨ b by inv (associative-join-Join-Semilattice a a b)
      ＝ a ∨ b by ap (_∨ b) (idempotent-join-Join-Semilattice a)

  leq-right-join-Join-Semilattice :
    (a b : type-Join-Semilattice) →
    leq-Join-Semilattice b (join-Join-Semilattice a b)
  leq-right-join-Join-Semilattice a b =
    equational-reasoning
      b ∨ (a ∨ b)
      ＝ (a ∨ b) ∨ b by commutative-join-Join-Semilattice _ _
      ＝ a ∨ (b ∨ b) by associative-join-Join-Semilattice a b b
      ＝ a ∨ b by ap (a ∨_) (idempotent-join-Join-Semilattice b)

  join-leq-leq-Join-Semilattice :
    (a b c d : type-Join-Semilattice) →
    leq-Join-Semilattice a b → leq-Join-Semilattice c d →
    leq-Join-Semilattice (join-Join-Semilattice a c) (join-Join-Semilattice b d)
  join-leq-leq-Join-Semilattice a b c d a≤b c≤d =
    forward-implication
      ( is-least-binary-upper-bound-join-Join-Semilattice
        ( a)
        ( c)
        ( join-Join-Semilattice b d))
      ( transitive-leq-Join-Semilattice
          ( a)
          ( b)
          ( b ∨ d)
          ( leq-left-join-Join-Semilattice b d)
          ( a≤b) ,
        transitive-leq-Join-Semilattice
          ( c)
          ( d)
          ( b ∨ d)
          ( leq-right-join-Join-Semilattice b d)
          ( c≤d))
```

### The predicate on posets of being a join-semilattice

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-join-semilattice-Poset-Prop : Prop (l1 ⊔ l2)
  is-join-semilattice-Poset-Prop =
    Π-Prop
      ( type-Poset P)
      ( λ x →
        Π-Prop
          ( type-Poset P)
          ( has-least-binary-upper-bound-prop-Poset P x))

  is-join-semilattice-Poset : UU (l1 ⊔ l2)
  is-join-semilattice-Poset = type-Prop is-join-semilattice-Poset-Prop

  is-prop-is-join-semilattice-Poset :
    is-prop is-join-semilattice-Poset
  is-prop-is-join-semilattice-Poset =
    is-prop-type-Prop is-join-semilattice-Poset-Prop

  module _
    (H : is-join-semilattice-Poset)
    where

    join-is-join-semilattice-Poset :
      type-Poset P → type-Poset P → type-Poset P
    join-is-join-semilattice-Poset x y = pr1 (H x y)

    is-least-binary-upper-bound-join-is-join-semilattice-Poset :
      (x y : type-Poset P) →
      is-least-binary-upper-bound-Poset P x y
        ( join-is-join-semilattice-Poset x y)
    is-least-binary-upper-bound-join-is-join-semilattice-Poset x y =
      pr2 (H x y)
```

### The order-theoretic definition of join semilattices

```agda
Order-Theoretic-Join-Semilattice : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Order-Theoretic-Join-Semilattice l1 l2 =
  Σ (Poset l1 l2) is-join-semilattice-Poset

module _
  {l1 l2 : Level} (A : Order-Theoretic-Join-Semilattice l1 l2)
  where

  poset-Order-Theoretic-Join-Semilattice : Poset l1 l2
  poset-Order-Theoretic-Join-Semilattice = pr1 A

  type-Order-Theoretic-Join-Semilattice : UU l1
  type-Order-Theoretic-Join-Semilattice =
    type-Poset poset-Order-Theoretic-Join-Semilattice

  is-set-type-Order-Theoretic-Join-Semilattice :
    is-set type-Order-Theoretic-Join-Semilattice
  is-set-type-Order-Theoretic-Join-Semilattice =
    is-set-type-Poset poset-Order-Theoretic-Join-Semilattice

  set-Order-Theoretic-Join-Semilattice : Set l1
  set-Order-Theoretic-Join-Semilattice =
    set-Poset poset-Order-Theoretic-Join-Semilattice

  leq-Order-Theoretic-Join-Semilattice-Prop :
    (x y : type-Order-Theoretic-Join-Semilattice) → Prop l2
  leq-Order-Theoretic-Join-Semilattice-Prop =
    leq-prop-Poset poset-Order-Theoretic-Join-Semilattice

  leq-Order-Theoretic-Join-Semilattice :
    (x y : type-Order-Theoretic-Join-Semilattice) → UU l2
  leq-Order-Theoretic-Join-Semilattice =
    leq-Poset poset-Order-Theoretic-Join-Semilattice

  is-prop-leq-Order-Theoretic-Join-Semilattice :
    (x y : type-Order-Theoretic-Join-Semilattice) →
    is-prop (leq-Order-Theoretic-Join-Semilattice x y)
  is-prop-leq-Order-Theoretic-Join-Semilattice =
    is-prop-leq-Poset poset-Order-Theoretic-Join-Semilattice

  refl-leq-Order-Theoretic-Join-Semilattice :
    (x : type-Order-Theoretic-Join-Semilattice) →
    leq-Order-Theoretic-Join-Semilattice x x
  refl-leq-Order-Theoretic-Join-Semilattice =
    refl-leq-Poset poset-Order-Theoretic-Join-Semilattice

  antisymmetric-leq-Order-Theoretic-Join-Semilattice :
    {x y : type-Order-Theoretic-Join-Semilattice} →
    leq-Order-Theoretic-Join-Semilattice x y →
    leq-Order-Theoretic-Join-Semilattice y x →
    x ＝ y
  antisymmetric-leq-Order-Theoretic-Join-Semilattice {x} {y} =
    antisymmetric-leq-Poset poset-Order-Theoretic-Join-Semilattice x y

  transitive-leq-Order-Theoretic-Join-Semilattice :
    (x y z : type-Order-Theoretic-Join-Semilattice) →
    leq-Order-Theoretic-Join-Semilattice y z →
    leq-Order-Theoretic-Join-Semilattice x y →
    leq-Order-Theoretic-Join-Semilattice x z
  transitive-leq-Order-Theoretic-Join-Semilattice =
    transitive-leq-Poset poset-Order-Theoretic-Join-Semilattice

  is-join-semilattice-Order-Theoretic-Join-Semilattice :
    is-join-semilattice-Poset poset-Order-Theoretic-Join-Semilattice
  is-join-semilattice-Order-Theoretic-Join-Semilattice = pr2 A

  join-Order-Theoretic-Join-Semilattice :
    (x y : type-Order-Theoretic-Join-Semilattice) →
    type-Order-Theoretic-Join-Semilattice
  join-Order-Theoretic-Join-Semilattice =
    join-is-join-semilattice-Poset
      poset-Order-Theoretic-Join-Semilattice
      is-join-semilattice-Order-Theoretic-Join-Semilattice

  private
    _∨_ = join-Order-Theoretic-Join-Semilattice

  is-least-binary-upper-bound-join-Order-Theoretic-Join-Semilattice :
    (x y : type-Order-Theoretic-Join-Semilattice) →
    is-least-binary-upper-bound-Poset
      ( poset-Order-Theoretic-Join-Semilattice)
      ( x)
      ( y)
      ( x ∨ y)
  is-least-binary-upper-bound-join-Order-Theoretic-Join-Semilattice =
    is-least-binary-upper-bound-join-is-join-semilattice-Poset
      poset-Order-Theoretic-Join-Semilattice
      is-join-semilattice-Order-Theoretic-Join-Semilattice

  is-binary-upper-bound-join-Order-Theoretic-Join-Semilattice :
    (x y : type-Order-Theoretic-Join-Semilattice) →
    is-binary-upper-bound-Poset
      ( poset-Order-Theoretic-Join-Semilattice)
      ( x)
      ( y)
      ( x ∨ y)
  is-binary-upper-bound-join-Order-Theoretic-Join-Semilattice x y =
    is-binary-upper-bound-is-least-binary-upper-bound-Poset
      ( poset-Order-Theoretic-Join-Semilattice)
      ( is-least-binary-upper-bound-join-Order-Theoretic-Join-Semilattice
        ( x)
        ( y))

  leq-left-join-Order-Theoretic-Join-Semilattice :
    (x y : type-Order-Theoretic-Join-Semilattice) →
    leq-Order-Theoretic-Join-Semilattice x (x ∨ y)
  leq-left-join-Order-Theoretic-Join-Semilattice x y =
    leq-left-is-binary-upper-bound-Poset
      ( poset-Order-Theoretic-Join-Semilattice)
      ( is-binary-upper-bound-join-Order-Theoretic-Join-Semilattice x y)

  leq-right-join-Order-Theoretic-Join-Semilattice :
    (x y : type-Order-Theoretic-Join-Semilattice) →
    leq-Order-Theoretic-Join-Semilattice y (x ∨ y)
  leq-right-join-Order-Theoretic-Join-Semilattice x y =
    leq-right-is-binary-upper-bound-Poset
      ( poset-Order-Theoretic-Join-Semilattice)
      ( is-binary-upper-bound-join-Order-Theoretic-Join-Semilattice x y)

  leq-join-Order-Theoretic-Join-Semilattice :
    {x y z : type-Order-Theoretic-Join-Semilattice} →
    leq-Order-Theoretic-Join-Semilattice x z →
    leq-Order-Theoretic-Join-Semilattice y z →
    leq-Order-Theoretic-Join-Semilattice (x ∨ y) z
  leq-join-Order-Theoretic-Join-Semilattice {x} {y} {z} H K =
    forward-implication
      ( is-least-binary-upper-bound-join-Order-Theoretic-Join-Semilattice
        ( x)
        ( y)
        ( z))
      ( H , K)

  join-leq-leq-Order-Theoretic-Join-Semilattice :
    (a b c d : type-Order-Theoretic-Join-Semilattice) →
    leq-Order-Theoretic-Join-Semilattice a b →
    leq-Order-Theoretic-Join-Semilattice c d →
    leq-Order-Theoretic-Join-Semilattice
      ( join-Order-Theoretic-Join-Semilattice a c)
      ( join-Order-Theoretic-Join-Semilattice b d)
  join-leq-leq-Order-Theoretic-Join-Semilattice a b c d a≤b c≤d =
    forward-implication
      ( is-least-binary-upper-bound-join-Order-Theoretic-Join-Semilattice
        ( a)
        ( c)
        ( b ∨ d))
      ( transitive-leq-Order-Theoretic-Join-Semilattice
          ( a)
          ( b)
          ( b ∨ d)
          ( leq-left-join-Order-Theoretic-Join-Semilattice b d)
          ( a≤b) ,
        transitive-leq-Order-Theoretic-Join-Semilattice
          ( c)
          ( d)
          ( b ∨ d)
          ( leq-right-join-Order-Theoretic-Join-Semilattice b d)
          ( c≤d))
```

## Properties

### The join operation of order theoretic join-semilattices is associative

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Join-Semilattice l1 l2)
  (x y z : type-Order-Theoretic-Join-Semilattice A)
  where

  private
    _∨_ = join-Order-Theoretic-Join-Semilattice A
    _≤_ = leq-Order-Theoretic-Join-Semilattice A

  leq-left-triple-join-Order-Theoretic-Join-Semilattice :
    x ≤ ((x ∨ y) ∨ z)
  leq-left-triple-join-Order-Theoretic-Join-Semilattice =
    calculate-in-Poset
      ( poset-Order-Theoretic-Join-Semilattice A)
      chain-of-inequalities
        x ≤ x ∨ y
            by leq-left-join-Order-Theoretic-Join-Semilattice A x y
            in-Poset poset-Order-Theoretic-Join-Semilattice A
          ≤ (x ∨ y) ∨ z
            by leq-left-join-Order-Theoretic-Join-Semilattice A (x ∨ y) z
            in-Poset poset-Order-Theoretic-Join-Semilattice A

  leq-center-triple-join-Order-Theoretic-Join-Semilattice :
    y ≤ ((x ∨ y) ∨ z)
  leq-center-triple-join-Order-Theoretic-Join-Semilattice =
    calculate-in-Poset
      ( poset-Order-Theoretic-Join-Semilattice A)
      chain-of-inequalities
        y ≤ x ∨ y
            by leq-right-join-Order-Theoretic-Join-Semilattice A x y
            in-Poset poset-Order-Theoretic-Join-Semilattice A
          ≤ (x ∨ y) ∨ z
            by leq-left-join-Order-Theoretic-Join-Semilattice A (x ∨ y) z
            in-Poset poset-Order-Theoretic-Join-Semilattice A

  leq-right-triple-join-Order-Theoretic-Join-Semilattice :
    z ≤ ((x ∨ y) ∨ z)
  leq-right-triple-join-Order-Theoretic-Join-Semilattice =
    leq-right-join-Order-Theoretic-Join-Semilattice A (x ∨ y) z

  leq-left-triple-join-Order-Theoretic-Join-Semilattice' :
    x ≤ (x ∨ (y ∨ z))
  leq-left-triple-join-Order-Theoretic-Join-Semilattice' =
    leq-left-join-Order-Theoretic-Join-Semilattice A x (y ∨ z)

  leq-center-triple-join-Order-Theoretic-Join-Semilattice' :
    y ≤ (x ∨ (y ∨ z))
  leq-center-triple-join-Order-Theoretic-Join-Semilattice' =
    calculate-in-Poset
      ( poset-Order-Theoretic-Join-Semilattice A)
      chain-of-inequalities
        y ≤ y ∨ z
            by leq-left-join-Order-Theoretic-Join-Semilattice A y z
            in-Poset poset-Order-Theoretic-Join-Semilattice A
          ≤ x ∨ (y ∨ z)
            by leq-right-join-Order-Theoretic-Join-Semilattice A x (y ∨ z)
            in-Poset poset-Order-Theoretic-Join-Semilattice A

  leq-right-triple-join-Order-Theoretic-Join-Semilattice' :
    z ≤ (x ∨ (y ∨ z))
  leq-right-triple-join-Order-Theoretic-Join-Semilattice' =
    calculate-in-Poset
      ( poset-Order-Theoretic-Join-Semilattice A)
      chain-of-inequalities
        z ≤ y ∨ z
            by leq-right-join-Order-Theoretic-Join-Semilattice A y z
            in-Poset poset-Order-Theoretic-Join-Semilattice A
          ≤ x ∨ (y ∨ z)
            by leq-right-join-Order-Theoretic-Join-Semilattice A x (y ∨ z)
            in-Poset poset-Order-Theoretic-Join-Semilattice A

  leq-associative-join-Order-Theoretic-Join-Semilattice :
    ((x ∨ y) ∨ z) ≤ (x ∨ (y ∨ z))
  leq-associative-join-Order-Theoretic-Join-Semilattice =
    leq-join-Order-Theoretic-Join-Semilattice A
      ( leq-join-Order-Theoretic-Join-Semilattice A
        ( leq-left-triple-join-Order-Theoretic-Join-Semilattice')
        ( leq-center-triple-join-Order-Theoretic-Join-Semilattice'))
      ( leq-right-triple-join-Order-Theoretic-Join-Semilattice')

  leq-associative-join-Order-Theoretic-Join-Semilattice' :
    (x ∨ (y ∨ z)) ≤ ((x ∨ y) ∨ z)
  leq-associative-join-Order-Theoretic-Join-Semilattice' =
    leq-join-Order-Theoretic-Join-Semilattice A
      ( leq-left-triple-join-Order-Theoretic-Join-Semilattice)
      ( leq-join-Order-Theoretic-Join-Semilattice A
        ( leq-center-triple-join-Order-Theoretic-Join-Semilattice)
        ( leq-right-triple-join-Order-Theoretic-Join-Semilattice))

  associative-join-Order-Theoretic-Join-Semilattice :
    ((x ∨ y) ∨ z) ＝ (x ∨ (y ∨ z))
  associative-join-Order-Theoretic-Join-Semilattice =
    antisymmetric-leq-Order-Theoretic-Join-Semilattice A
      leq-associative-join-Order-Theoretic-Join-Semilattice
      leq-associative-join-Order-Theoretic-Join-Semilattice'
```

### The join operation of order theoretic join-semilattices is commutative

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Join-Semilattice l1 l2)
  (x y : type-Order-Theoretic-Join-Semilattice A)
  where

  private
    _∨_ = join-Order-Theoretic-Join-Semilattice A
    _≤_ = leq-Order-Theoretic-Join-Semilattice A

  leq-commutative-join-Order-Theoretic-Join-Semilattice :
    (x ∨ y) ≤ (y ∨ x)
  leq-commutative-join-Order-Theoretic-Join-Semilattice =
    leq-join-Order-Theoretic-Join-Semilattice A
      ( leq-right-join-Order-Theoretic-Join-Semilattice A y x)
      ( leq-left-join-Order-Theoretic-Join-Semilattice A y x)

  leq-commutative-join-Order-Theoretic-Join-Semilattice' :
    (y ∨ x) ≤ (x ∨ y)
  leq-commutative-join-Order-Theoretic-Join-Semilattice' =
    leq-join-Order-Theoretic-Join-Semilattice A
      ( leq-right-join-Order-Theoretic-Join-Semilattice A x y)
      ( leq-left-join-Order-Theoretic-Join-Semilattice A x y)

  commutative-join-Order-Theoretic-Join-Semilattice :
    (x ∨ y) ＝ (y ∨ x)
  commutative-join-Order-Theoretic-Join-Semilattice =
    antisymmetric-leq-Order-Theoretic-Join-Semilattice A
      leq-commutative-join-Order-Theoretic-Join-Semilattice
      leq-commutative-join-Order-Theoretic-Join-Semilattice'
```

### The join operation of order theoretic join-semilattices is idempotent

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Join-Semilattice l1 l2)
  (x : type-Order-Theoretic-Join-Semilattice A)
  where

  private
    _∨_ = join-Order-Theoretic-Join-Semilattice A
    _≤_ = leq-Order-Theoretic-Join-Semilattice A

  idempotent-join-Order-Theoretic-Join-Semilattice :
    (x ∨ x) ＝ x
  idempotent-join-Order-Theoretic-Join-Semilattice =
    antisymmetric-leq-Order-Theoretic-Join-Semilattice A
      ( leq-join-Order-Theoretic-Join-Semilattice A
        ( refl-leq-Order-Theoretic-Join-Semilattice A x)
        ( refl-leq-Order-Theoretic-Join-Semilattice A x))
      ( leq-left-join-Order-Theoretic-Join-Semilattice A x x)
```

### Any order theoretic join-semilattice is an algebraic join semilattice

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Join-Semilattice l1 l2)
  where

  semigroup-Order-Theoretic-Join-Semilattice : Semigroup l1
  pr1 semigroup-Order-Theoretic-Join-Semilattice =
    set-Order-Theoretic-Join-Semilattice A
  pr1 (pr2 semigroup-Order-Theoretic-Join-Semilattice) =
    join-Order-Theoretic-Join-Semilattice A
  pr2 (pr2 semigroup-Order-Theoretic-Join-Semilattice) =
    associative-join-Order-Theoretic-Join-Semilattice A

  join-semilattice-Order-Theoretic-Join-Semilattice :
    Join-Semilattice l1
  pr1 join-semilattice-Order-Theoretic-Join-Semilattice =
    semigroup-Order-Theoretic-Join-Semilattice
  pr1 (pr2 join-semilattice-Order-Theoretic-Join-Semilattice) =
    commutative-join-Order-Theoretic-Join-Semilattice A
  pr2 (pr2 join-semilattice-Order-Theoretic-Join-Semilattice) =
    idempotent-join-Order-Theoretic-Join-Semilattice A
```
