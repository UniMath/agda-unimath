# Meet-semilattices

```agda
module order-theory.meet-semilattices where
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

open import group-theory.commutative-semigroups
open import group-theory.isomorphisms-semigroups
open import group-theory.semigroups

open import order-theory.greatest-lower-bounds-posets
open import order-theory.lower-bounds-posets
open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

A
{{#concept "meet-semilattice" WDID=Q29018102 WD="lower semilattice" Agda=Meet-Semilattice}}
is a [poset](order-theory.posets.md) in which every pair of elements has a
[greatest binary lower bound](order-theory.greatest-lower-bounds.md).
Alternatively, meet-semilattices can be defined algebraically as a set `X`
equipped with a binary operation `∧ : X → X → X` satisfying

1. Associativity: `(x ∧ y) ∧ z ＝ x ∧ (y ∧ z)`,
2. Commutativity: `x ∧ y ＝ y ∧ x`,
3. Idempotency: `x ∧ x ＝ x`.

We will follow the algebraic approach for our principal definition of
meet-semilattices, since it requires only one universe level. This is necessary
in order to consider the [large category](category-theory.large-categories.md)
of meet-semilattices.

## Definitions

### The predicate on commutative semigroups of being a meet-semilattice

```agda
module _
  {l : Level} (X : Commutative-Semigroup l)
  where

  is-meet-semilattice-prop-Commutative-Semigroup : Prop l
  is-meet-semilattice-prop-Commutative-Semigroup =
    Π-Prop
      ( type-Commutative-Semigroup X)
      ( λ x →
        Id-Prop
          ( set-Commutative-Semigroup X)
          ( mul-Commutative-Semigroup X x x)
          ( x))

  is-meet-semilattice-Commutative-Semigroup : UU l
  is-meet-semilattice-Commutative-Semigroup =
    type-Prop is-meet-semilattice-prop-Commutative-Semigroup

  is-prop-is-meet-semilattice-Commutative-Semigroup :
    is-prop is-meet-semilattice-Commutative-Semigroup
  is-prop-is-meet-semilattice-Commutative-Semigroup =
    is-prop-type-Prop is-meet-semilattice-prop-Commutative-Semigroup
```

### The algebraic definition of meet-semilattices

```agda
Meet-Semilattice : (l : Level) → UU (lsuc l)
Meet-Semilattice l = type-subtype is-meet-semilattice-prop-Commutative-Semigroup

module _
  {l : Level} (X : Meet-Semilattice l)
  where

  commutative-semigroup-Meet-Semilattice : Commutative-Semigroup l
  commutative-semigroup-Meet-Semilattice = pr1 X

  semigroup-Meet-Semilattice : Semigroup l
  semigroup-Meet-Semilattice =
    semigroup-Commutative-Semigroup commutative-semigroup-Meet-Semilattice

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
    is-meet-semilattice-Commutative-Semigroup
      ( commutative-semigroup-Meet-Semilattice)
  is-meet-semilattice-Meet-Semilattice = pr2 X

  commutative-meet-Meet-Semilattice :
    (x y : type-Meet-Semilattice) → (x ∧ y) ＝ (y ∧ x)
  commutative-meet-Meet-Semilattice =
    commutative-mul-Commutative-Semigroup commutative-semigroup-Meet-Semilattice

  idempotent-meet-Meet-Semilattice :
    (x : type-Meet-Semilattice) → (x ∧ x) ＝ x
  idempotent-meet-Meet-Semilattice =
    is-meet-semilattice-Meet-Semilattice

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

  refl-leq-Meet-Semilattice : is-reflexive leq-Meet-Semilattice
  refl-leq-Meet-Semilattice x = idempotent-meet-Meet-Semilattice x

  transitive-leq-Meet-Semilattice : is-transitive leq-Meet-Semilattice
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

  antisymmetric-leq-Meet-Semilattice : is-antisymmetric leq-Meet-Semilattice
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
  is-greatest-binary-lower-bound-meet-Meet-Semilattice x y =
    prove-is-greatest-binary-lower-bound-Poset
      ( poset-Meet-Semilattice)
      ( is-binary-lower-bound-meet-Meet-Semilattice x y)
      ( λ z (H , K) →
        equational-reasoning
          z ∧ (x ∧ y)
          ＝ (z ∧ x) ∧ y
            by inv (associative-meet-Meet-Semilattice z x y)
          ＝ z ∧ y
            by ap (meet-Meet-Semilattice' y) H
          ＝ z
            by K)

  has-greatest-binary-lower-bound-Meet-Semilattice :
    (x y : type-Meet-Semilattice) →
    has-greatest-binary-lower-bound-Poset (poset-Meet-Semilattice) x y
  pr1 (has-greatest-binary-lower-bound-Meet-Semilattice x y) =
    meet-Meet-Semilattice x y
  pr2 (has-greatest-binary-lower-bound-Meet-Semilattice x y) =
    is-greatest-binary-lower-bound-meet-Meet-Semilattice x y

  leq-left-meet-Meet-Semilattice :
    (x y : type-Meet-Semilattice) → leq-Meet-Semilattice (x ∧ y) x
  leq-left-meet-Meet-Semilattice x y =
    equational-reasoning
      (x ∧ y) ∧ x
      ＝ x ∧ (x ∧ y) by commutative-meet-Meet-Semilattice _ _
      ＝ (x ∧ x) ∧ y by inv (associative-meet-Meet-Semilattice x x y)
      ＝ x ∧ y by ap (_∧ y) (idempotent-meet-Meet-Semilattice x)

  leq-right-meet-Meet-Semilattice :
    (x y : type-Meet-Semilattice) → leq-Meet-Semilattice (x ∧ y) y
  leq-right-meet-Meet-Semilattice x y =
    equational-reasoning
      (x ∧ y) ∧ y
      ＝ x ∧ (y ∧ y) by associative-meet-Meet-Semilattice x y y
      ＝ x ∧ y by ap (x ∧_) (idempotent-meet-Meet-Semilattice y)

  meet-leq-leq-Meet-Semilattice :
    (a b c d : type-Meet-Semilattice) →
    leq-Meet-Semilattice a b → leq-Meet-Semilattice c d →
    leq-Meet-Semilattice (meet-Meet-Semilattice a c) (meet-Meet-Semilattice b d)
  meet-leq-leq-Meet-Semilattice a b c d a≤b c≤d =
    forward-implication
      ( is-greatest-binary-lower-bound-meet-Meet-Semilattice
        ( b)
        ( d)
        ( meet-Meet-Semilattice a c))
      ( transitive-leq-Meet-Semilattice
        ( a ∧ c)
        ( a)
        ( b)
        ( a≤b)
        ( leq-left-meet-Meet-Semilattice a c) ,
        transitive-leq-Meet-Semilattice
          ( a ∧ c)
          ( c)
          ( d)
          ( c≤d)
          ( leq-right-meet-Meet-Semilattice a c))
```

### The predicate on posets of being a meet-semilattice

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

  module _
    (H : is-meet-semilattice-Poset)
    where

    meet-is-meet-semilattice-Poset :
      type-Poset P → type-Poset P → type-Poset P
    meet-is-meet-semilattice-Poset x y = pr1 (H x y)

    is-greatest-binary-lower-bound-meet-is-meet-semilattice-Poset :
      (x y : type-Poset P) →
      is-greatest-binary-lower-bound-Poset P x y
        ( meet-is-meet-semilattice-Poset x y)
    is-greatest-binary-lower-bound-meet-is-meet-semilattice-Poset x y =
      pr2 (H x y)
```

### The order-theoretic definition of meet semilattices

```agda
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

  is-set-type-Order-Theoretic-Meet-Semilattice :
    is-set type-Order-Theoretic-Meet-Semilattice
  is-set-type-Order-Theoretic-Meet-Semilattice =
    is-set-type-Poset poset-Order-Theoretic-Meet-Semilattice

  set-Order-Theoretic-Meet-Semilattice : Set l1
  set-Order-Theoretic-Meet-Semilattice =
    set-Poset poset-Order-Theoretic-Meet-Semilattice

  leq-Order-Theoretic-Meet-Semilattice-Prop :
    (x y : type-Order-Theoretic-Meet-Semilattice) → Prop l2
  leq-Order-Theoretic-Meet-Semilattice-Prop =
    leq-prop-Poset poset-Order-Theoretic-Meet-Semilattice

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
    {x y : type-Order-Theoretic-Meet-Semilattice} →
    leq-Order-Theoretic-Meet-Semilattice x y →
    leq-Order-Theoretic-Meet-Semilattice y x →
    x ＝ y
  antisymmetric-leq-Order-Theoretic-Meet-Semilattice {x} {y} =
    antisymmetric-leq-Poset poset-Order-Theoretic-Meet-Semilattice x y

  transitive-leq-Order-Theoretic-Meet-Semilattice :
    (x y z : type-Order-Theoretic-Meet-Semilattice) →
    leq-Order-Theoretic-Meet-Semilattice y z →
    leq-Order-Theoretic-Meet-Semilattice x y →
    leq-Order-Theoretic-Meet-Semilattice x z
  transitive-leq-Order-Theoretic-Meet-Semilattice =
    transitive-leq-Poset poset-Order-Theoretic-Meet-Semilattice

  is-meet-semilattice-Order-Theoretic-Meet-Semilattice :
    is-meet-semilattice-Poset poset-Order-Theoretic-Meet-Semilattice
  is-meet-semilattice-Order-Theoretic-Meet-Semilattice = pr2 A

  meet-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    type-Order-Theoretic-Meet-Semilattice
  meet-Order-Theoretic-Meet-Semilattice =
    meet-is-meet-semilattice-Poset
      poset-Order-Theoretic-Meet-Semilattice
      is-meet-semilattice-Order-Theoretic-Meet-Semilattice

  private
    _∧_ = meet-Order-Theoretic-Meet-Semilattice

  is-greatest-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    is-greatest-binary-lower-bound-Poset
      ( poset-Order-Theoretic-Meet-Semilattice)
      ( x)
      ( y)
      ( x ∧ y)
  is-greatest-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice =
    is-greatest-binary-lower-bound-meet-is-meet-semilattice-Poset
      poset-Order-Theoretic-Meet-Semilattice
      is-meet-semilattice-Order-Theoretic-Meet-Semilattice

  is-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    is-binary-lower-bound-Poset
      ( poset-Order-Theoretic-Meet-Semilattice)
      ( x)
      ( y)
      ( x ∧ y)
  is-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice x y =
    is-binary-lower-bound-is-greatest-binary-lower-bound-Poset
      ( poset-Order-Theoretic-Meet-Semilattice)
      ( is-greatest-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice
        ( x)
        ( y))

  leq-left-meet-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    leq-Order-Theoretic-Meet-Semilattice (x ∧ y) x
  leq-left-meet-Order-Theoretic-Meet-Semilattice x y =
    leq-left-is-binary-lower-bound-Poset
      ( poset-Order-Theoretic-Meet-Semilattice)
      ( is-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice x y)

  leq-right-meet-Order-Theoretic-Meet-Semilattice :
    (x y : type-Order-Theoretic-Meet-Semilattice) →
    leq-Order-Theoretic-Meet-Semilattice (x ∧ y) y
  leq-right-meet-Order-Theoretic-Meet-Semilattice x y =
    leq-right-is-binary-lower-bound-Poset
      ( poset-Order-Theoretic-Meet-Semilattice)
      ( is-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice x y)

  leq-meet-Order-Theoretic-Meet-Semilattice :
    {x y z : type-Order-Theoretic-Meet-Semilattice} →
    leq-Order-Theoretic-Meet-Semilattice z x →
    leq-Order-Theoretic-Meet-Semilattice z y →
    leq-Order-Theoretic-Meet-Semilattice z (x ∧ y)
  leq-meet-Order-Theoretic-Meet-Semilattice {x} {y} {z} H K =
    forward-implication
      ( is-greatest-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice
        ( x)
        ( y)
        ( z))
      ( H , K)

  meet-leq-leq-Order-Theoretic-Meet-Semilattice :
    (a b c d : type-Order-Theoretic-Meet-Semilattice) →
    leq-Order-Theoretic-Meet-Semilattice a b →
    leq-Order-Theoretic-Meet-Semilattice c d →
    leq-Order-Theoretic-Meet-Semilattice
      (meet-Order-Theoretic-Meet-Semilattice a c)
      (meet-Order-Theoretic-Meet-Semilattice b d)
  meet-leq-leq-Order-Theoretic-Meet-Semilattice a b c d a≤b c≤d =
    forward-implication
      ( is-greatest-binary-lower-bound-meet-Order-Theoretic-Meet-Semilattice
        ( b)
        ( d)
        ( meet-Order-Theoretic-Meet-Semilattice a c))
      ( transitive-leq-Order-Theoretic-Meet-Semilattice
          ( a ∧ c)
          ( a)
          ( b)
          ( a≤b)
          ( leq-left-meet-Order-Theoretic-Meet-Semilattice a c) ,
        transitive-leq-Order-Theoretic-Meet-Semilattice
          ( a ∧ c)
          ( c)
          ( d)
          ( c≤d)
          ( leq-right-meet-Order-Theoretic-Meet-Semilattice a c))
```

## Properties

### The meet operation of order theoretic meet-semilattices is associative

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Meet-Semilattice l1 l2)
  (x y z : type-Order-Theoretic-Meet-Semilattice A)
  where

  private
    _∧_ = meet-Order-Theoretic-Meet-Semilattice A
    _≤_ = leq-Order-Theoretic-Meet-Semilattice A

  leq-left-triple-meet-Order-Theoretic-Meet-Semilattice :
    ((x ∧ y) ∧ z) ≤ x
  leq-left-triple-meet-Order-Theoretic-Meet-Semilattice =
    calculate-in-Poset
      ( poset-Order-Theoretic-Meet-Semilattice A)
      chain-of-inequalities
        (x ∧ y) ∧ z
          ≤ x ∧ y
            by leq-left-meet-Order-Theoretic-Meet-Semilattice A (x ∧ y) z
            in-Poset poset-Order-Theoretic-Meet-Semilattice A
          ≤ x
            by leq-left-meet-Order-Theoretic-Meet-Semilattice A x y
            in-Poset poset-Order-Theoretic-Meet-Semilattice A

  leq-center-triple-meet-Order-Theoretic-Meet-Semilattice :
    ((x ∧ y) ∧ z) ≤ y
  leq-center-triple-meet-Order-Theoretic-Meet-Semilattice =
    calculate-in-Poset
      ( poset-Order-Theoretic-Meet-Semilattice A)
      chain-of-inequalities
        (x ∧ y) ∧ z
          ≤ x ∧ y
            by leq-left-meet-Order-Theoretic-Meet-Semilattice A (x ∧ y) z
            in-Poset poset-Order-Theoretic-Meet-Semilattice A
          ≤ y
            by leq-right-meet-Order-Theoretic-Meet-Semilattice A x y
            in-Poset poset-Order-Theoretic-Meet-Semilattice A

  leq-right-triple-meet-Order-Theoretic-Meet-Semilattice :
    ((x ∧ y) ∧ z) ≤ z
  leq-right-triple-meet-Order-Theoretic-Meet-Semilattice =
    leq-right-meet-Order-Theoretic-Meet-Semilattice A (x ∧ y) z

  leq-left-triple-meet-Order-Theoretic-Meet-Semilattice' :
    (x ∧ (y ∧ z)) ≤ x
  leq-left-triple-meet-Order-Theoretic-Meet-Semilattice' =
    leq-left-meet-Order-Theoretic-Meet-Semilattice A x (y ∧ z)

  leq-center-triple-meet-Order-Theoretic-Meet-Semilattice' :
    (x ∧ (y ∧ z)) ≤ y
  leq-center-triple-meet-Order-Theoretic-Meet-Semilattice' =
    calculate-in-Poset
      ( poset-Order-Theoretic-Meet-Semilattice A)
      chain-of-inequalities
        x ∧ (y ∧ z)
          ≤ y ∧ z
            by leq-right-meet-Order-Theoretic-Meet-Semilattice A x (y ∧ z)
            in-Poset poset-Order-Theoretic-Meet-Semilattice A
          ≤ y
            by leq-left-meet-Order-Theoretic-Meet-Semilattice A y z
            in-Poset poset-Order-Theoretic-Meet-Semilattice A

  leq-right-triple-meet-Order-Theoretic-Meet-Semilattice' :
    (x ∧ (y ∧ z)) ≤ z
  leq-right-triple-meet-Order-Theoretic-Meet-Semilattice' =
    calculate-in-Poset
      ( poset-Order-Theoretic-Meet-Semilattice A)
      chain-of-inequalities
        x ∧ (y ∧ z)
          ≤ y ∧ z
            by leq-right-meet-Order-Theoretic-Meet-Semilattice A x (y ∧ z)
            in-Poset poset-Order-Theoretic-Meet-Semilattice A
          ≤ z
            by leq-right-meet-Order-Theoretic-Meet-Semilattice A y z
            in-Poset poset-Order-Theoretic-Meet-Semilattice A

  leq-associative-meet-Order-Theoretic-Meet-Semilattice :
    ((x ∧ y) ∧ z) ≤ (x ∧ (y ∧ z))
  leq-associative-meet-Order-Theoretic-Meet-Semilattice =
    leq-meet-Order-Theoretic-Meet-Semilattice A
      ( leq-left-triple-meet-Order-Theoretic-Meet-Semilattice)
      ( leq-meet-Order-Theoretic-Meet-Semilattice A
        ( leq-center-triple-meet-Order-Theoretic-Meet-Semilattice)
        ( leq-right-triple-meet-Order-Theoretic-Meet-Semilattice))

  leq-associative-meet-Order-Theoretic-Meet-Semilattice' :
    (x ∧ (y ∧ z)) ≤ ((x ∧ y) ∧ z)
  leq-associative-meet-Order-Theoretic-Meet-Semilattice' =
    leq-meet-Order-Theoretic-Meet-Semilattice A
      ( leq-meet-Order-Theoretic-Meet-Semilattice A
        ( leq-left-triple-meet-Order-Theoretic-Meet-Semilattice')
        ( leq-center-triple-meet-Order-Theoretic-Meet-Semilattice'))
      ( leq-right-triple-meet-Order-Theoretic-Meet-Semilattice')

  associative-meet-Order-Theoretic-Meet-Semilattice :
    ((x ∧ y) ∧ z) ＝ (x ∧ (y ∧ z))
  associative-meet-Order-Theoretic-Meet-Semilattice =
    antisymmetric-leq-Order-Theoretic-Meet-Semilattice A
      leq-associative-meet-Order-Theoretic-Meet-Semilattice
      leq-associative-meet-Order-Theoretic-Meet-Semilattice'
```

### The meet operation of order theoretic meet-semilattices is commutative

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Meet-Semilattice l1 l2)
  (x y : type-Order-Theoretic-Meet-Semilattice A)
  where

  private
    _∧_ = meet-Order-Theoretic-Meet-Semilattice A
    _≤_ = leq-Order-Theoretic-Meet-Semilattice A

  leq-commutative-meet-Order-Theoretic-Meet-Semilattice :
    (x ∧ y) ≤ (y ∧ x)
  leq-commutative-meet-Order-Theoretic-Meet-Semilattice =
    leq-meet-Order-Theoretic-Meet-Semilattice A
      ( leq-right-meet-Order-Theoretic-Meet-Semilattice A x y)
      ( leq-left-meet-Order-Theoretic-Meet-Semilattice A x y)

  leq-commutative-meet-Order-Theoretic-Meet-Semilattice' :
    (y ∧ x) ≤ (x ∧ y)
  leq-commutative-meet-Order-Theoretic-Meet-Semilattice' =
    leq-meet-Order-Theoretic-Meet-Semilattice A
      ( leq-right-meet-Order-Theoretic-Meet-Semilattice A y x)
      ( leq-left-meet-Order-Theoretic-Meet-Semilattice A y x)

  commutative-meet-Order-Theoretic-Meet-Semilattice :
    (x ∧ y) ＝ (y ∧ x)
  commutative-meet-Order-Theoretic-Meet-Semilattice =
    antisymmetric-leq-Order-Theoretic-Meet-Semilattice A
      leq-commutative-meet-Order-Theoretic-Meet-Semilattice
      leq-commutative-meet-Order-Theoretic-Meet-Semilattice'
```

### The meet operation of order theoretic meet-semilattices is idempotent

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Meet-Semilattice l1 l2)
  (x : type-Order-Theoretic-Meet-Semilattice A)
  where

  private
    _∧_ = meet-Order-Theoretic-Meet-Semilattice A
    _≤_ = leq-Order-Theoretic-Meet-Semilattice A

  idempotent-meet-Order-Theoretic-Meet-Semilattice :
    (x ∧ x) ＝ x
  idempotent-meet-Order-Theoretic-Meet-Semilattice =
    antisymmetric-leq-Order-Theoretic-Meet-Semilattice A
      ( leq-left-meet-Order-Theoretic-Meet-Semilattice A x x)
      ( leq-meet-Order-Theoretic-Meet-Semilattice A
        ( refl-leq-Order-Theoretic-Meet-Semilattice A x)
        ( refl-leq-Order-Theoretic-Meet-Semilattice A x))
```

### Any order theoretic meet-semilattice is an algebraic meet semilattice

```agda
module _
  {l1 l2 : Level} (A : Order-Theoretic-Meet-Semilattice l1 l2)
  where

  semigroup-Order-Theoretic-Meet-Semilattice : Semigroup l1
  pr1 semigroup-Order-Theoretic-Meet-Semilattice =
    set-Order-Theoretic-Meet-Semilattice A
  pr1 (pr2 semigroup-Order-Theoretic-Meet-Semilattice) =
    meet-Order-Theoretic-Meet-Semilattice A
  pr2 (pr2 semigroup-Order-Theoretic-Meet-Semilattice) =
    associative-meet-Order-Theoretic-Meet-Semilattice A

  commutative-semigroup-Order-Theoretic-Meet-Semilattice :
    Commutative-Semigroup l1
  pr1 commutative-semigroup-Order-Theoretic-Meet-Semilattice =
    semigroup-Order-Theoretic-Meet-Semilattice
  pr2 commutative-semigroup-Order-Theoretic-Meet-Semilattice =
    commutative-meet-Order-Theoretic-Meet-Semilattice A

  meet-semilattice-Order-Theoretic-Meet-Semilattice :
    Meet-Semilattice l1
  pr1 meet-semilattice-Order-Theoretic-Meet-Semilattice =
    commutative-semigroup-Order-Theoretic-Meet-Semilattice
  pr2 meet-semilattice-Order-Theoretic-Meet-Semilattice =
    idempotent-meet-Order-Theoretic-Meet-Semilattice A
```

### Any meet-semilattice `A` is isomorphic to the meet-semilattice obtained from the order theoretic meet-semilattice obtained from `A`

```agda
module _
  {l1 : Level} (A : Meet-Semilattice l1)
  where

  order-theoretic-meet-semilattice-Meet-Semilattice :
    Order-Theoretic-Meet-Semilattice l1 l1
  pr1 order-theoretic-meet-semilattice-Meet-Semilattice =
    poset-Meet-Semilattice A
  pr1 (pr2 order-theoretic-meet-semilattice-Meet-Semilattice x y) =
    meet-Meet-Semilattice A x y
  pr2 (pr2 order-theoretic-meet-semilattice-Meet-Semilattice x y) =
    is-greatest-binary-lower-bound-meet-Meet-Semilattice A x y

  compute-meet-order-theoretic-meet-semilattice-Meet-Semilattice :
    (x y : type-Meet-Semilattice A) →
    meet-Meet-Semilattice A x y ＝
    meet-Order-Theoretic-Meet-Semilattice
      ( order-theoretic-meet-semilattice-Meet-Semilattice)
      ( x)
      ( y)
  compute-meet-order-theoretic-meet-semilattice-Meet-Semilattice x y = refl

  compute-order-theoretic-meet-semilattice-Meet-Semilattice :
    iso-Semigroup
      ( semigroup-Meet-Semilattice A)
      ( semigroup-Meet-Semilattice
        ( meet-semilattice-Order-Theoretic-Meet-Semilattice
          ( order-theoretic-meet-semilattice-Meet-Semilattice)))
  compute-order-theoretic-meet-semilattice-Meet-Semilattice =
    id-iso-Semigroup (semigroup-Meet-Semilattice A)
```
