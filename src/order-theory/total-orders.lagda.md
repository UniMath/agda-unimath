# Total orders

```agda
module order-theory.total-orders where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.interchange-law
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-posets
open import order-theory.join-semilattices
open import order-theory.least-upper-bounds-posets
open import order-theory.meet-semilattices
open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-preorders
```

</details>

## Idea

A
{{#concept "total order" Disambiguation="on a type" WD="total order" WDID=Q369377 Agda=Total-Order}},
or a **linear order**, is a [poset](order-theory.posets.md) `P` such that for
every two elements `x` and `y` in `P` the
[disjunction](foundation.disjunction.md) `(x ≤ y) ∨ (y ≤ x)` holds. In other
words, total orders are _totally ordered_ in the sense that any two elements are
comparable.

## Definitions

### Being a totally ordered poset

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  incident-Poset-Prop : (x y : type-Poset X) → Prop l2
  incident-Poset-Prop = incident-Preorder-Prop (preorder-Poset X)

  incident-Poset : (x y : type-Poset X) → UU l2
  incident-Poset = incident-Preorder (preorder-Poset X)

  is-prop-incident-Poset :
    (x y : type-Poset X) → is-prop (incident-Poset x y)
  is-prop-incident-Poset = is-prop-incident-Preorder (preorder-Poset X)

  is-total-Poset-Prop : Prop (l1 ⊔ l2)
  is-total-Poset-Prop = is-total-Preorder-Prop (preorder-Poset X)

  is-total-Poset : UU (l1 ⊔ l2)
  is-total-Poset = is-total-Preorder (preorder-Poset X)

  is-prop-is-total-Poset : is-prop is-total-Poset
  is-prop-is-total-Poset = is-prop-is-total-Preorder (preorder-Poset X)
```

### The type of total orders

```agda
Total-Order : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Total-Order l1 l2 = Σ (Poset l1 l2) is-total-Poset

module _
  {l1 l2 : Level} (X : Total-Order l1 l2)
  where

  poset-Total-Order : Poset l1 l2
  poset-Total-Order = pr1 X

  preorder-Total-Order : Preorder l1 l2
  preorder-Total-Order = preorder-Poset poset-Total-Order

  is-total-Total-Order : is-total-Poset (poset-Total-Order)
  is-total-Total-Order = pr2 X

  type-Total-Order : UU l1
  type-Total-Order = type-Poset poset-Total-Order

  leq-prop-Total-Order : (x y : type-Total-Order) → Prop l2
  leq-prop-Total-Order = leq-prop-Poset poset-Total-Order

  leq-Total-Order : (x y : type-Total-Order) → UU l2
  leq-Total-Order = leq-Poset poset-Total-Order

  is-prop-leq-Total-Order :
    (x y : type-Total-Order) → is-prop (leq-Total-Order x y)
  is-prop-leq-Total-Order = is-prop-leq-Poset poset-Total-Order

  concatenate-eq-leq-Total-Order :
    {x y z : type-Total-Order} → x ＝ y →
    leq-Total-Order y z → leq-Total-Order x z
  concatenate-eq-leq-Total-Order = concatenate-eq-leq-Poset poset-Total-Order

  concatenate-leq-eq-Total-Order :
    {x y z : type-Total-Order} →
    leq-Total-Order x y → y ＝ z → leq-Total-Order x z
  concatenate-leq-eq-Total-Order = concatenate-leq-eq-Poset poset-Total-Order

  refl-leq-Total-Order : is-reflexive leq-Total-Order
  refl-leq-Total-Order = refl-leq-Poset poset-Total-Order

  transitive-leq-Total-Order : is-transitive leq-Total-Order
  transitive-leq-Total-Order = transitive-leq-Poset poset-Total-Order

  antisymmetric-leq-Total-Order : is-antisymmetric leq-Total-Order
  antisymmetric-leq-Total-Order = antisymmetric-leq-Poset poset-Total-Order

  is-set-type-Total-Order : is-set type-Total-Order
  is-set-type-Total-Order = is-set-type-Poset poset-Total-Order

  set-Total-Order : Set l1
  set-Total-Order = set-Poset poset-Total-Order
```

### The maximum operation on a total order

```agda
module _
  {l1 l2 : Level} (X : Total-Order l1 l2)
  (x y : type-Total-Order X)
  where

  opaque
    has-least-binary-upper-bound-Total-Order :
      has-least-binary-upper-bound-Poset (poset-Total-Order X) x y
    has-least-binary-upper-bound-Total-Order =
      elim-disjunction
        ( has-least-binary-upper-bound-prop-Poset (poset-Total-Order X) x y)
        ( has-least-binary-upper-bound-leq-Poset (poset-Total-Order X) x y)
        ( λ y≤x →
          symmetric-has-least-binary-upper-bound-Poset
            ( poset-Total-Order X)
            ( y)
            ( x)
            ( has-least-binary-upper-bound-leq-Poset
              ( poset-Total-Order X)
              ( y)
              ( x)
              ( y≤x)))
        ( is-total-Total-Order X x y)

  max-Total-Order : type-Total-Order X
  max-Total-Order = pr1 has-least-binary-upper-bound-Total-Order

  max-is-least-binary-upper-bound-Total-Order :
    is-least-binary-upper-bound-Poset (poset-Total-Order X) x y max-Total-Order
  max-is-least-binary-upper-bound-Total-Order =
    pr2 has-least-binary-upper-bound-Total-Order
```

### The minimum operation on a total order

```agda
module _
  {l1 l2 : Level} (X : Total-Order l1 l2)
  (x y : type-Total-Order X)
  where

  opaque
    has-greatest-binary-lower-bound-Total-Order :
      has-greatest-binary-lower-bound-Poset (poset-Total-Order X) x y
    has-greatest-binary-lower-bound-Total-Order =
      elim-disjunction
        ( has-greatest-binary-lower-bound-prop-Poset (poset-Total-Order X) x y)
        ( has-greatest-binary-lower-bound-leq-Poset
            ( poset-Total-Order X)
            ( x)
            ( y))
        ( λ y≤x →
          symmetric-has-greatest-binary-lower-bound-Poset
            ( poset-Total-Order X)
            ( y)
            ( x)
            ( has-greatest-binary-lower-bound-leq-Poset
              ( poset-Total-Order X)
              ( y)
              ( x)
              ( y≤x)))
        ( is-total-Total-Order X x y)

  min-Total-Order : type-Total-Order X
  min-Total-Order = pr1 has-greatest-binary-lower-bound-Total-Order

  min-is-greatest-binary-lower-bound-Total-Order :
    is-greatest-binary-lower-bound-Poset
      ( poset-Total-Order X)
      ( x)
      ( y)
      ( min-Total-Order)
  min-is-greatest-binary-lower-bound-Total-Order =
    pr2 has-greatest-binary-lower-bound-Total-Order
```

## Properties

### The minimum of two values is a lower bound

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  (x y : type-Total-Order T)
  where

  leq-left-min-Total-Order :
    leq-Total-Order T (min-Total-Order T x y) x
  leq-left-min-Total-Order =
    leq-left-is-greatest-binary-lower-bound-Poset
      ( poset-Total-Order T)
      ( min-is-greatest-binary-lower-bound-Total-Order T x y)

  leq-right-min-Total-Order :
    leq-Total-Order T (min-Total-Order T x y) y
  leq-right-min-Total-Order =
    leq-right-is-greatest-binary-lower-bound-Poset
      ( poset-Total-Order T)
      ( min-is-greatest-binary-lower-bound-Total-Order T x y)
```

### The maximum of two values is an upper bound

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  (x y : type-Total-Order T)
  where

  leq-left-max-Total-Order :
    leq-Total-Order T x (max-Total-Order T x y)
  leq-left-max-Total-Order =
    leq-left-is-least-binary-upper-bound-Poset
      ( poset-Total-Order T)
      ( max-is-least-binary-upper-bound-Total-Order T x y)

  leq-right-max-Total-Order :
    leq-Total-Order T y (max-Total-Order T x y)
  leq-right-max-Total-Order =
    leq-right-is-least-binary-upper-bound-Poset
      ( poset-Total-Order T)
      ( max-is-least-binary-upper-bound-Total-Order T x y)
```

### The minimum of two values is less than or equal to their maximum

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  (x y : type-Total-Order T)
  where

  abstract
    min-leq-max-Total-Order :
      leq-Total-Order T (min-Total-Order T x y) (max-Total-Order T x y)
    min-leq-max-Total-Order =
      transitive-leq-Total-Order T
        ( min-Total-Order T x y)
        ( x)
        ( max-Total-Order T x y)
        ( leq-left-max-Total-Order T x y)
        ( leq-left-min-Total-Order T x y)
```

### Total orders are meet semilattices

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  where

  is-meet-semilattice-Total-Order :
    is-meet-semilattice-Poset (poset-Total-Order T)
  is-meet-semilattice-Total-Order =
    has-greatest-binary-lower-bound-Total-Order T

  order-theoretic-meet-semilattice-Total-Order :
    Order-Theoretic-Meet-Semilattice l1 l2
  order-theoretic-meet-semilattice-Total-Order =
    poset-Total-Order T , is-meet-semilattice-Total-Order
```

### Total orders are join semilattices

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  where

  is-join-semilattice-Total-Order :
    is-join-semilattice-Poset (poset-Total-Order T)
  is-join-semilattice-Total-Order =
    has-least-binary-upper-bound-Total-Order T

  order-theoretic-join-semilattice-Total-Order :
    Order-Theoretic-Join-Semilattice l1 l2
  order-theoretic-join-semilattice-Total-Order =
    poset-Total-Order T , is-join-semilattice-Total-Order
```

### The binary minimum operation is associative

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  where

  associative-min-Total-Order :
    (x y z : type-Total-Order T) →
    min-Total-Order T (min-Total-Order T x y) z ＝
    min-Total-Order T x (min-Total-Order T y z)
  associative-min-Total-Order =
    associative-meet-Order-Theoretic-Meet-Semilattice
      ( order-theoretic-meet-semilattice-Total-Order T)
```

### The binary maximum operation is associative

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  where

  associative-max-Total-Order :
    (x y z : type-Total-Order T) →
    max-Total-Order T (max-Total-Order T x y) z ＝
    max-Total-Order T x (max-Total-Order T y z)
  associative-max-Total-Order =
    associative-join-Order-Theoretic-Join-Semilattice
      ( order-theoretic-join-semilattice-Total-Order T)
```

### The binary minimum operation is commutative

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  where

  commutative-min-Total-Order :
    (x y : type-Total-Order T) →
    min-Total-Order T x y ＝ min-Total-Order T y x
  commutative-min-Total-Order =
    commutative-meet-Order-Theoretic-Meet-Semilattice
      ( order-theoretic-meet-semilattice-Total-Order T)
```

### The binary maximum operation is commutative

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  where

  commutative-max-Total-Order :
    (x y : type-Total-Order T) →
    max-Total-Order T x y ＝ max-Total-Order T y x
  commutative-max-Total-Order =
    commutative-join-Order-Theoretic-Join-Semilattice
      ( order-theoretic-join-semilattice-Total-Order T)
```

### Interchange on the binary minimum operation

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  abstract
    interchange-law-min-Total-Order :
      (a b c d : type-Total-Order T) →
      min-Total-Order T (min-Total-Order T a b) (min-Total-Order T c d) ＝
      min-Total-Order T (min-Total-Order T a c) (min-Total-Order T b d)
    interchange-law-min-Total-Order =
      interchange-law-commutative-and-associative
        ( min-Total-Order T)
        ( commutative-min-Total-Order T)
        ( associative-min-Total-Order T)
```

### Interchange on the binary maximum operation

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  abstract
    interchange-law-max-Total-Order :
      (a b c d : type-Total-Order T) →
      max-Total-Order T (max-Total-Order T a b) (max-Total-Order T c d) ＝
      max-Total-Order T (max-Total-Order T a c) (max-Total-Order T b d)
    interchange-law-max-Total-Order =
      interchange-law-commutative-and-associative
        ( max-Total-Order T)
        ( commutative-max-Total-Order T)
        ( associative-max-Total-Order T)
```

### The binary minimum operation is idempotent

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  where

  idempotent-min-Total-Order :
    (x : type-Total-Order T) →
    min-Total-Order T x x ＝ x
  idempotent-min-Total-Order =
    idempotent-meet-Order-Theoretic-Meet-Semilattice
      ( order-theoretic-meet-semilattice-Total-Order T)
```

### The binary maximum operation is idempotent

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  where

  idempotent-max-Total-Order :
    (x : type-Total-Order T) →
    max-Total-Order T x x ＝ x
  idempotent-max-Total-Order =
    idempotent-join-Order-Theoretic-Join-Semilattice
      ( order-theoretic-join-semilattice-Total-Order T)
```

### If `x` is less than or equal to `y`, the minimum of `x` and `y` is `x`

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  where

  abstract
    left-leq-right-min-Total-Order :
      (x y : type-Total-Order T) →
      leq-Total-Order T x y → min-Total-Order T x y ＝ x
    left-leq-right-min-Total-Order x y x≤y =
      ap pr1
        ( eq-type-Prop
          ( has-greatest-binary-lower-bound-prop-Poset
            ( poset-Total-Order T)
            ( x)
            ( y))
          { has-greatest-binary-lower-bound-Total-Order T x y}
          { has-greatest-binary-lower-bound-leq-Poset
            ( poset-Total-Order T)
            ( x)
            ( y)
            ( x≤y)})
```

### If `y` is less than or equal to `x`, the minimum of `x` and `y` is `y`

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  where

  abstract
    right-leq-left-min-Total-Order :
      (x y : type-Total-Order T) →
      leq-Total-Order T y x → min-Total-Order T x y ＝ y
    right-leq-left-min-Total-Order x y y≤x =
      commutative-min-Total-Order T x y ∙
      left-leq-right-min-Total-Order T y x y≤x
```

### If `x` is less than or equal to `y`, the maximum of `x` and `y` is `y`

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  where

  abstract
    left-leq-right-max-Total-Order :
      (x y : type-Total-Order T) →
      leq-Total-Order T x y → max-Total-Order T x y ＝ y
    left-leq-right-max-Total-Order x y x≤y =
      ap pr1
        ( eq-type-Prop
          ( has-least-binary-upper-bound-prop-Poset
            ( poset-Total-Order T)
            ( x)
            ( y))
          { has-least-binary-upper-bound-Total-Order T x y}
          { has-least-binary-upper-bound-leq-Poset
            ( poset-Total-Order T)
            ( x)
            ( y)
            ( x≤y)})
```

### If `y` is less than or equal to `x`, the maximum of `x` and `y` is `x`

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  where

  abstract
    right-leq-left-max-Total-Order :
      (x y : type-Total-Order T) →
      leq-Total-Order T y x → max-Total-Order T x y ＝ x
    right-leq-left-max-Total-Order x y y≤x =
      commutative-max-Total-Order T x y ∙
      left-leq-right-max-Total-Order T y x y≤x
```

### If `a ≤ b` and `c ≤ d`, then `min a c ≤ min b d`

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  where

  abstract
    min-leq-leq-Total-Order :
      (a b c d : type-Total-Order T) →
      leq-Total-Order T a b → leq-Total-Order T c d →
      leq-Total-Order
        ( T)
        ( min-Total-Order T a c)
        ( min-Total-Order T b d)
    min-leq-leq-Total-Order =
      meet-leq-leq-Order-Theoretic-Meet-Semilattice
        ( order-theoretic-meet-semilattice-Total-Order T)
```

### If `a ≤ b` and `a ≤ c`, then `a ≤ min b c`

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  abstract
    leq-min-leq-both-Total-Order :
      (a b c : type-Total-Order T) →
      leq-Total-Order T a b → leq-Total-Order T a c →
      leq-Total-Order T a (min-Total-Order T b c)
    leq-min-leq-both-Total-Order a b c a≤b a≤c =
      tr
        ( λ d → leq-Total-Order T d (min-Total-Order T b c))
        ( idempotent-min-Total-Order T a)
        ( min-leq-leq-Total-Order T a b a c a≤b a≤c)
```

### If `a ≤ b` and `c ≤ d`, then `max a c ≤ max b d`

```agda
module _
  {l1 l2 : Level}
  (T : Total-Order l1 l2)
  where

  abstract
    max-leq-leq-Total-Order :
      (a b c d : type-Total-Order T) →
      leq-Total-Order T a b → leq-Total-Order T c d →
      leq-Total-Order
        ( T)
        ( max-Total-Order T a c)
        ( max-Total-Order T b d)
    max-leq-leq-Total-Order =
      join-leq-leq-Order-Theoretic-Join-Semilattice
        ( order-theoretic-join-semilattice-Total-Order T)
```

### The minimum of two values is equal to one of them

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  abstract
    eq-one-min-Total-Order :
      (x y : type-Total-Order T) →
      type-disjunction-Prop
        ( Id-Prop (set-Total-Order T) (min-Total-Order T x y) x)
        ( Id-Prop (set-Total-Order T) (min-Total-Order T x y) y)
    eq-one-min-Total-Order x y =
      map-disjunction
        ( left-leq-right-min-Total-Order T x y)
        ( right-leq-left-min-Total-Order T x y)
        ( is-total-Total-Order T x y)

    eq-one-of-four-min-Total-Order :
      (x y z w : type-Total-Order T) →
      let
        min=_ =
          Id-Prop
            ( set-Total-Order T)
            ( min-Total-Order T (min-Total-Order T x y) (min-Total-Order T z w))
      in type-disjunction-Prop (min= x ∨ min= y) (min= z ∨ min= w)
    eq-one-of-four-min-Total-Order x y z w =
      map-disjunction
        ( λ min=minxy →
          map-disjunction
            ( min=minxy ∙_)
            ( min=minxy ∙_)
            ( eq-one-min-Total-Order x y))
        ( λ min=minzw →
          map-disjunction
            ( min=minzw ∙_)
            ( min=minzw ∙_)
            ( eq-one-min-Total-Order z w))
        ( eq-one-min-Total-Order
          ( min-Total-Order T x y)
          ( min-Total-Order T z w))
```

### The maximum of two values is equal to one of them

```agda
module _
  {l1 l2 : Level} (T : Total-Order l1 l2)
  where

  abstract
    eq-one-max-Total-Order :
      (x y : type-Total-Order T) →
      type-disjunction-Prop
        ( Id-Prop (set-Total-Order T) (max-Total-Order T x y) x)
        ( Id-Prop (set-Total-Order T) (max-Total-Order T x y) y)
    eq-one-max-Total-Order x y =
      map-disjunction
        ( right-leq-left-max-Total-Order T x y)
        ( left-leq-right-max-Total-Order T x y)
        ( is-total-Total-Order T y x)

    eq-one-of-four-max-Total-Order :
      (x y z w : type-Total-Order T) →
      let
        max=_ =
          Id-Prop
            ( set-Total-Order T)
            ( max-Total-Order T (max-Total-Order T x y) (max-Total-Order T z w))
      in type-disjunction-Prop (max= x ∨ max= y) (max= z ∨ max= w)
    eq-one-of-four-max-Total-Order x y z w =
      map-disjunction
        ( λ max=maxxy →
          map-disjunction
            ( max=maxxy ∙_)
            ( max=maxxy ∙_)
            ( eq-one-max-Total-Order x y))
        ( λ max=maxzw →
          map-disjunction
            ( max=maxzw ∙_)
            ( max=maxzw ∙_)
            ( eq-one-max-Total-Order z w))
        ( eq-one-max-Total-Order
          ( max-Total-Order T x y)
          ( max-Total-Order T z w))
```

## External links

- [Total order](https://en.wikipedia.org/wiki/Total_order) at Wikipedia
- [total order](https://ncatlab.org/nlab/show/total+order) at $n$Lab
- [Total orders](https://1lab.dev/Order.Total.html) at 1lab
