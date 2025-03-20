# Large meet-semilattices

```agda
open import foundation.function-extensionality-axiom

module
  order-theory.large-meet-semilattices
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.large-binary-relations funext
open import foundation.sets funext
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets funext
open import order-theory.large-posets funext
open import order-theory.meet-semilattices funext
open import order-theory.posets funext
open import order-theory.top-elements-large-posets funext
```

</details>

## Idea

A **large meet-semilattice** is a
[large semigroup](group-theory.large-semigroups.md) which is commutative and
idempotent.

## Definition

### The predicate that a large poset has meets

```agda
record
  has-meets-Large-Poset
    { α : Level → Level}
    { β : Level → Level → Level}
    ( P : Large-Poset α β) :
    UUω
  where
  constructor
    make-has-meets-Large-Poset
  field
    meet-has-meets-Large-Poset :
      {l1 l2 : Level}
      (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
      type-Large-Poset P (l1 ⊔ l2)
    is-greatest-binary-lower-bound-meet-has-meets-Large-Poset :
      {l1 l2 : Level}
      (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
      is-greatest-binary-lower-bound-Large-Poset P x y
        ( meet-has-meets-Large-Poset x y)

open has-meets-Large-Poset public
```

### The predicate of being a large meet-semilattice

```agda
record
  is-large-meet-semilattice-Large-Poset
    { α : Level → Level}
    { β : Level → Level → Level}
    ( P : Large-Poset α β) :
    UUω
  where
  field
    has-meets-is-large-meet-semilattice-Large-Poset :
      has-meets-Large-Poset P
    has-top-element-is-large-meet-semilattice-Large-Poset :
      has-top-element-Large-Poset P

open is-large-meet-semilattice-Large-Poset public

module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (P : Large-Poset α β)
  (H : is-large-meet-semilattice-Large-Poset P)
  where

  meet-is-large-meet-semilattice-Large-Poset :
    {l1 l2 : Level} (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
    type-Large-Poset P (l1 ⊔ l2)
  meet-is-large-meet-semilattice-Large-Poset =
    meet-has-meets-Large-Poset
      ( has-meets-is-large-meet-semilattice-Large-Poset H)

  is-greatest-binary-lower-bound-meet-is-large-meet-semilattice-Large-Poset :
    {l1 l2 : Level} (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
    is-greatest-binary-lower-bound-Large-Poset P x y
      ( meet-is-large-meet-semilattice-Large-Poset x y)
  is-greatest-binary-lower-bound-meet-is-large-meet-semilattice-Large-Poset =
    is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
      ( has-meets-is-large-meet-semilattice-Large-Poset H)

  top-is-large-meet-semilattice-Large-Poset :
    type-Large-Poset P lzero
  top-is-large-meet-semilattice-Large-Poset =
    top-has-top-element-Large-Poset
      ( has-top-element-is-large-meet-semilattice-Large-Poset H)

  is-top-element-top-is-large-meet-semilattice-Large-Poset :
    {l1 : Level} (x : type-Large-Poset P l1) →
    leq-Large-Poset P x top-is-large-meet-semilattice-Large-Poset
  is-top-element-top-is-large-meet-semilattice-Large-Poset =
    is-top-element-top-has-top-element-Large-Poset
      ( has-top-element-is-large-meet-semilattice-Large-Poset H)
```

### Large meet-semilattices

```agda
record
  Large-Meet-Semilattice
    ( α : Level → Level)
    ( β : Level → Level → Level) :
    UUω
  where
  constructor
    make-Large-Meet-Semilattice
  field
    large-poset-Large-Meet-Semilattice :
      Large-Poset α β
    is-large-meet-semilattice-Large-Meet-Semilattice :
      is-large-meet-semilattice-Large-Poset
        large-poset-Large-Meet-Semilattice

open Large-Meet-Semilattice public

module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Meet-Semilattice α β)
  where

  type-Large-Meet-Semilattice : (l : Level) → UU (α l)
  type-Large-Meet-Semilattice =
    type-Large-Poset (large-poset-Large-Meet-Semilattice L)

  set-Large-Meet-Semilattice : (l : Level) → Set (α l)
  set-Large-Meet-Semilattice =
    set-Large-Poset (large-poset-Large-Meet-Semilattice L)

  is-set-type-Large-Meet-Semilattice :
    {l : Level} → is-set (type-Large-Meet-Semilattice l)
  is-set-type-Large-Meet-Semilattice =
    is-set-type-Large-Poset (large-poset-Large-Meet-Semilattice L)

  leq-Large-Meet-Semilattice : Large-Relation β type-Large-Meet-Semilattice
  leq-Large-Meet-Semilattice =
    leq-Large-Poset (large-poset-Large-Meet-Semilattice L)

  refl-leq-Large-Meet-Semilattice :
    is-reflexive-Large-Relation
      ( type-Large-Meet-Semilattice)
      ( leq-Large-Meet-Semilattice)
  refl-leq-Large-Meet-Semilattice =
    refl-leq-Large-Poset (large-poset-Large-Meet-Semilattice L)

  antisymmetric-leq-Large-Meet-Semilattice :
    is-antisymmetric-Large-Relation
      ( type-Large-Meet-Semilattice)
      ( leq-Large-Meet-Semilattice)
  antisymmetric-leq-Large-Meet-Semilattice =
    antisymmetric-leq-Large-Poset (large-poset-Large-Meet-Semilattice L)

  transitive-leq-Large-Meet-Semilattice :
    is-transitive-Large-Relation
      ( type-Large-Meet-Semilattice)
      ( leq-Large-Meet-Semilattice)
  transitive-leq-Large-Meet-Semilattice =
    transitive-leq-Large-Poset (large-poset-Large-Meet-Semilattice L)

  has-meets-Large-Meet-Semilattice :
    has-meets-Large-Poset (large-poset-Large-Meet-Semilattice L)
  has-meets-Large-Meet-Semilattice =
    has-meets-is-large-meet-semilattice-Large-Poset
      ( is-large-meet-semilattice-Large-Meet-Semilattice L)

  meet-Large-Meet-Semilattice :
    {l1 l2 : Level}
    (x : type-Large-Meet-Semilattice l1)
    (y : type-Large-Meet-Semilattice l2) →
    type-Large-Meet-Semilattice (l1 ⊔ l2)
  meet-Large-Meet-Semilattice =
    meet-is-large-meet-semilattice-Large-Poset
      ( large-poset-Large-Meet-Semilattice L)
      ( is-large-meet-semilattice-Large-Meet-Semilattice L)

  is-greatest-binary-lower-bound-meet-Large-Meet-Semilattice :
    {l1 l2 : Level}
    (x : type-Large-Meet-Semilattice l1)
    (y : type-Large-Meet-Semilattice l2) →
    is-greatest-binary-lower-bound-Large-Poset
      ( large-poset-Large-Meet-Semilattice L)
      ( x)
      ( y)
      ( meet-Large-Meet-Semilattice x y)
  is-greatest-binary-lower-bound-meet-Large-Meet-Semilattice =
    is-greatest-binary-lower-bound-meet-is-large-meet-semilattice-Large-Poset
      ( large-poset-Large-Meet-Semilattice L)
      ( is-large-meet-semilattice-Large-Meet-Semilattice L)

  ap-meet-Large-Meet-Semilattice :
    {l1 l2 : Level}
    {x x' : type-Large-Meet-Semilattice l1}
    {y y' : type-Large-Meet-Semilattice l2} →
    (x ＝ x') → (y ＝ y') →
    meet-Large-Meet-Semilattice x y ＝ meet-Large-Meet-Semilattice x' y'
  ap-meet-Large-Meet-Semilattice p q =
    ap-binary meet-Large-Meet-Semilattice p q

  has-top-element-Large-Meet-Semilattice :
    has-top-element-Large-Poset (large-poset-Large-Meet-Semilattice L)
  has-top-element-Large-Meet-Semilattice =
    has-top-element-is-large-meet-semilattice-Large-Poset
      ( is-large-meet-semilattice-Large-Meet-Semilattice L)

  top-Large-Meet-Semilattice :
    type-Large-Meet-Semilattice lzero
  top-Large-Meet-Semilattice =
    top-is-large-meet-semilattice-Large-Poset
      ( large-poset-Large-Meet-Semilattice L)
      ( is-large-meet-semilattice-Large-Meet-Semilattice L)

  is-top-element-top-Large-Meet-Semilattice :
    {l1 : Level} (x : type-Large-Meet-Semilattice l1) →
    leq-Large-Meet-Semilattice x top-Large-Meet-Semilattice
  is-top-element-top-Large-Meet-Semilattice =
    is-top-element-top-is-large-meet-semilattice-Large-Poset
      ( large-poset-Large-Meet-Semilattice L)
      ( is-large-meet-semilattice-Large-Meet-Semilattice L)
```

### Small meet semilattices from large meet semilattices

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Meet-Semilattice α β)
  where

  poset-Large-Meet-Semilattice : (l : Level) → Poset (α l) (β l l)
  poset-Large-Meet-Semilattice =
    poset-Large-Poset (large-poset-Large-Meet-Semilattice L)

  is-meet-semilattice-poset-Large-Meet-Semilattice :
    {l : Level} → is-meet-semilattice-Poset (poset-Large-Meet-Semilattice l)
  pr1 (is-meet-semilattice-poset-Large-Meet-Semilattice x y) =
    meet-Large-Meet-Semilattice L x y
  pr2 (is-meet-semilattice-poset-Large-Meet-Semilattice x y) =
    is-greatest-binary-lower-bound-meet-Large-Meet-Semilattice L x y

  order-theoretic-meet-semilattice-Large-Meet-Semilattice :
    (l : Level) → Order-Theoretic-Meet-Semilattice (α l) (β l l)
  pr1 (order-theoretic-meet-semilattice-Large-Meet-Semilattice l) =
    poset-Large-Meet-Semilattice l
  pr2 (order-theoretic-meet-semilattice-Large-Meet-Semilattice l) =
    is-meet-semilattice-poset-Large-Meet-Semilattice

  meet-semilattice-Large-Meet-Semilattice :
    (l : Level) → Meet-Semilattice (α l)
  meet-semilattice-Large-Meet-Semilattice l =
    meet-semilattice-Order-Theoretic-Meet-Semilattice
      ( order-theoretic-meet-semilattice-Large-Meet-Semilattice l)
```
