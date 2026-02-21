# Large rings

```agda
module ring-theory.large-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.cumulative-large-sets
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.large-similarity-relations
open import foundation.sets
open import foundation.similarity-preserving-binary-maps-cumulative-large-sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.large-abelian-groups
open import group-theory.large-monoids
open import group-theory.large-semigroups
open import group-theory.monoids

open import ring-theory.homomorphisms-rings
open import ring-theory.rings
```

</details>

## Idea

A {{#concept "large ring" Agda=Large-Ring}} is a
[large abelian group](group-theory.large-abelian-groups.md) endowed with an
additional operation, called multiplication, which in addition to forming a
[large monoid](group-theory.large-monoids.md) is distributive over addition.

## Definition

```agda
record Large-Ring (α : Level → Level) (β : Level → Level → Level) : UUω where

  constructor
    make-Large-Ring

  field
    large-ab-Large-Ring : Large-Ab α β

  cumulative-large-set-Large-Ring : Cumulative-Large-Set α β
  cumulative-large-set-Large-Ring =
    cumulative-large-set-Large-Ab large-ab-Large-Ring

  type-Large-Ring : (l : Level) → UU (α l)
  type-Large-Ring = type-Large-Ab large-ab-Large-Ring

  set-Large-Ring : (l : Level) → Set (α l)
  set-Large-Ring = set-Large-Ab large-ab-Large-Ring

  add-Large-Ring :
    {l1 l2 : Level} →
    type-Large-Ring l1 → type-Large-Ring l2 → type-Large-Ring (l1 ⊔ l2)
  add-Large-Ring = add-Large-Ab large-ab-Large-Ring

  neg-Large-Ring : {l : Level} → type-Large-Ring l → type-Large-Ring l
  neg-Large-Ring = neg-Large-Ab large-ab-Large-Ring

  zero-Large-Ring : type-Large-Ring lzero
  zero-Large-Ring = zero-Large-Ab large-ab-Large-Ring

  sim-prop-Large-Ring : Large-Relation-Prop β type-Large-Ring
  sim-prop-Large-Ring = sim-prop-Large-Ab large-ab-Large-Ring

  sim-Large-Ring : Large-Relation β type-Large-Ring
  sim-Large-Ring = sim-Large-Ab large-ab-Large-Ring

  raise-Large-Ring :
    {l1 : Level} (l2 : Level) (x : type-Large-Ring l1) →
    type-Large-Ring (l1 ⊔ l2)
  raise-Large-Ring = raise-Large-Ab large-ab-Large-Ring

  field
    mul-Large-Ring :
      {l1 l2 : Level} →
      type-Large-Ring l1 → type-Large-Ring l2 → type-Large-Ring (l1 ⊔ l2)

    preserves-sim-mul-Large-Ring :
      {l1 l2 l3 l4 : Level} →
      (x : type-Large-Ring l1) (x' : type-Large-Ring l2) → sim-Large-Ring x x' →
      (y : type-Large-Ring l3) (y' : type-Large-Ring l4) → sim-Large-Ring y y' →
      sim-Large-Ring (mul-Large-Ring x y) (mul-Large-Ring x' y')

    one-Large-Ring : type-Large-Ring lzero

    associative-mul-Large-Ring :
      {l1 l2 l3 : Level} →
      (a : type-Large-Ring l1) →
      (b : type-Large-Ring l2) →
      (c : type-Large-Ring l3) →
      mul-Large-Ring (mul-Large-Ring a b) c ＝
      mul-Large-Ring a (mul-Large-Ring b c)

    left-unit-law-mul-Large-Ring :
      {l : Level} (a : type-Large-Ring l) → mul-Large-Ring one-Large-Ring a ＝ a

    right-unit-law-mul-Large-Ring :
      {l : Level} (a : type-Large-Ring l) → mul-Large-Ring a one-Large-Ring ＝ a

    left-distributive-mul-add-Large-Ring :
      {l1 l2 l3 : Level} →
      (a : type-Large-Ring l1) →
      (b : type-Large-Ring l2) →
      (c : type-Large-Ring l3) →
      mul-Large-Ring a (add-Large-Ring b c) ＝
      add-Large-Ring (mul-Large-Ring a b) (mul-Large-Ring a c)

    right-distributive-mul-add-Large-Ring :
      {l1 l2 l3 : Level} →
      (a : type-Large-Ring l1) →
      (b : type-Large-Ring l2) →
      (c : type-Large-Ring l3) →
      mul-Large-Ring (add-Large-Ring a b) c ＝
      add-Large-Ring (mul-Large-Ring a c) (mul-Large-Ring b c)

open Large-Ring public
```

## Properties

### The similarity relation of a large ring

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  large-similarity-relation-Large-Ring :
    Large-Similarity-Relation β (type-Large-Ring R)
  large-similarity-relation-Large-Ring =
    large-similarity-relation-Large-Ab (large-ab-Large-Ring R)

  refl-sim-Large-Ring :
    {l : Level} (x : type-Large-Ring R l) → sim-Large-Ring R x x
  refl-sim-Large-Ring = refl-sim-Large-Ab (large-ab-Large-Ring R)

  symmetric-sim-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    sim-Large-Ring R x y → sim-Large-Ring R y x
  symmetric-sim-Large-Ring = symmetric-sim-Large-Ab (large-ab-Large-Ring R)

  transitive-sim-Large-Ring :
    {l1 l2 l3 : Level} →
    (x : type-Large-Ring R l1) →
    (y : type-Large-Ring R l2) →
    (z : type-Large-Ring R l3) →
    sim-Large-Ring R y z → sim-Large-Ring R x y → sim-Large-Ring R x z
  transitive-sim-Large-Ring =
    transitive-sim-Large-Ab (large-ab-Large-Ring R)
```

### Raising universe levels

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  raise-zero-Large-Ring : (l : Level) → type-Large-Ring R l
  raise-zero-Large-Ring = raise-zero-Large-Ab (large-ab-Large-Ring R)

  sim-raise-Large-Ring :
    {l1 : Level} (l2 : Level) (x : type-Large-Ring R l1) →
    sim-Large-Ring R x (raise-Large-Ring R l2 x)
  sim-raise-Large-Ring = sim-raise-Large-Ab (large-ab-Large-Ring R)

  sim-raise-Large-Ring' :
    {l1 : Level} (l2 : Level) (x : type-Large-Ring R l1) →
    sim-Large-Ring R (raise-Large-Ring R l2 x) x
  sim-raise-Large-Ring' = sim-raise-Large-Ab' (large-ab-Large-Ring R)

  eq-raise-Large-Ring :
    (l1 : Level) {l2 : Level} (x : type-Large-Ring R (l1 ⊔ l2)) →
    raise-Large-Ring R l2 x ＝ x
  eq-raise-Large-Ring = eq-raise-Large-Ab (large-ab-Large-Ring R)

  raise-raise-Large-Ring :
    {l1 l2 l3 : Level} → (x : type-Large-Ring R l1) →
    raise-Large-Ring R l2 (raise-Large-Ring R l3 x) ＝
    raise-Large-Ring R (l2 ⊔ l3) x
  raise-raise-Large-Ring = raise-raise-Large-Ab (large-ab-Large-Ring R)

  raise-left-add-Large-Ring :
    {l1 l2 l3 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    add-Large-Ring R (raise-Large-Ring R l3 x) y ＝
    raise-Large-Ring R l3 (add-Large-Ring R x y)
  raise-left-add-Large-Ring = raise-left-add-Large-Ab (large-ab-Large-Ring R)

  raise-right-add-Large-Ring :
    {l1 l2 l3 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    add-Large-Ring R x (raise-Large-Ring R l3 y) ＝
    raise-Large-Ring R l3 (add-Large-Ring R x y)
  raise-right-add-Large-Ring = raise-right-add-Large-Ab (large-ab-Large-Ring R)

  raise-left-unit-law-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) →
    add-Large-Ring R (raise-zero-Large-Ring l2) x ＝ raise-Large-Ring R l2 x
  raise-left-unit-law-Large-Ring =
    raise-left-unit-law-Large-Ab (large-ab-Large-Ring R)

  raise-right-unit-law-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) →
    add-Large-Ring R x (raise-zero-Large-Ring l2) ＝
    raise-Large-Ring R l2 x
  raise-right-unit-law-Large-Ring =
    raise-right-unit-law-Large-Ab (large-ab-Large-Ring R)

  raise-zero-lzero-Large-Ring :
    raise-zero-Large-Ring lzero ＝ zero-Large-Ring R
  raise-zero-lzero-Large-Ring =
    raise-unit-lzero-Large-Ab (large-ab-Large-Ring R)
```

### The multiplicative monoid of a large ring

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  multiplicative-large-semigroup-Large-Ring : Large-Semigroup α β
  multiplicative-large-semigroup-Large-Ring =
    λ where
      .cumulative-large-set-Large-Semigroup →
        cumulative-large-set-Large-Ring R
      .sim-preserving-binary-operator-mul-Large-Semigroup →
        make-sim-preserving-binary-operator-Cumulative-Large-Set
          ( cumulative-large-set-Large-Ring R)
          ( mul-Large-Ring R)
          ( λ x x' y y' x~x' y~y' →
            preserves-sim-mul-Large-Ring R x x' x~x' y y' y~y')
      .associative-mul-Large-Semigroup →
        associative-mul-Large-Ring R

  multiplicative-large-monoid-Large-Ring : Large-Monoid α β
  multiplicative-large-monoid-Large-Ring =
    λ where
      .large-semigroup-Large-Monoid →
        multiplicative-large-semigroup-Large-Ring
      .unit-Large-Monoid →
        one-Large-Ring R
      .left-unit-law-mul-Large-Monoid →
        left-unit-law-mul-Large-Ring R
      .right-unit-law-mul-Large-Monoid →
        right-unit-law-mul-Large-Ring R

  raise-one-Large-Ring : (l : Level) → type-Large-Ring R l
  raise-one-Large-Ring =
    raise-unit-Large-Monoid multiplicative-large-monoid-Large-Ring
```

### Abelian group properties of addition in a large ring

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  associative-add-Large-Ring :
    {l1 l2 l3 : Level} →
    (a : type-Large-Ring R l1) →
    (b : type-Large-Ring R l2) →
    (c : type-Large-Ring R l3) →
    add-Large-Ring R (add-Large-Ring R a b) c ＝
    add-Large-Ring R a (add-Large-Ring R b c)
  associative-add-Large-Ring = associative-add-Large-Ab (large-ab-Large-Ring R)

  left-unit-law-add-Large-Ring :
    {l : Level} (x : type-Large-Ring R l) →
    add-Large-Ring R (zero-Large-Ring R) x ＝ x
  left-unit-law-add-Large-Ring =
    left-unit-law-add-Large-Ab (large-ab-Large-Ring R)

  right-unit-law-add-Large-Ring :
    {l : Level} (x : type-Large-Ring R l) →
    add-Large-Ring R x (zero-Large-Ring R) ＝ x
  right-unit-law-add-Large-Ring =
    right-unit-law-add-Large-Ab (large-ab-Large-Ring R)

  left-inverse-law-add-Large-Ring :
    {l : Level} (x : type-Large-Ring R l) →
    add-Large-Ring R (neg-Large-Ring R x) x ＝ raise-zero-Large-Ring R l
  left-inverse-law-add-Large-Ring =
    left-inverse-law-add-Large-Ab (large-ab-Large-Ring R)

  right-inverse-law-add-Large-Ring :
    {l : Level} (x : type-Large-Ring R l) →
    add-Large-Ring R x (neg-Large-Ring R x) ＝ raise-zero-Large-Ring R l
  right-inverse-law-add-Large-Ring =
    right-inverse-law-add-Large-Ab (large-ab-Large-Ring R)

  commutative-add-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Ring R l1) (y : type-Large-Ring R l2) →
    add-Large-Ring R x y ＝ add-Large-Ring R y x
  commutative-add-Large-Ring = commutative-add-Large-Ab (large-ab-Large-Ring R)
```

### Small rings from large rings

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  ring-Large-Ring : (l : Level) → Ring (α l)
  ring-Large-Ring l =
    ( ab-Large-Ab (large-ab-Large-Ring R) l ,
      ( mul-Large-Ring R , associative-mul-Large-Ring R) ,
      is-unital-Monoid
        ( monoid-Large-Monoid (multiplicative-large-monoid-Large-Ring R) l) ,
      left-distributive-mul-add-Large-Ring R ,
      right-distributive-mul-add-Large-Ring R)
```

### The raise operation is a ring homomorphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  (l1 l2 : Level)
  where

  hom-raise-Large-Ring :
    hom-Ring
      ( ring-Large-Ring R l1)
      ( ring-Large-Ring R (l1 ⊔ l2))
  hom-raise-Large-Ring =
    ( hom-raise-Large-Ab (large-ab-Large-Ring R) l1 l2 ,
      inv
        ( mul-raise-raise-Large-Monoid
          ( multiplicative-large-monoid-Large-Ring R)
          ( l2)
          ( l2)
          ( _)
          ( _)) ,
      raise-raise-Large-Ring R _)
```

### Zero laws of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (R : Large-Ring α β)
  where

  abstract
    left-raise-zero-law-mul-Large-Ring :
      (l1 : Level) {l2 : Level} (x : type-Large-Ring R l2) →
      mul-Large-Ring R (raise-zero-Large-Ring R l1) x ＝
      raise-zero-Large-Ring R (l1 ⊔ l2)
    left-raise-zero-law-mul-Large-Ring l1 {l2} x =
      is-zero-is-idempotent-Ab
        ( ab-Large-Ab (large-ab-Large-Ring R) (l1 ⊔ l2))
        ( equational-reasoning
          add-Large-Ring
            ( R)
            ( mul-Large-Ring R (raise-zero-Large-Ring R l1) x)
            ( mul-Large-Ring R (raise-zero-Large-Ring R l1) x)
          ＝
            mul-Large-Ring R
              ( add-Large-Ring R
                ( raise-zero-Large-Ring R l1)
                ( raise-zero-Large-Ring R l1))
              ( x)
            by inv (right-distributive-mul-add-Large-Ring R _ _ _)
          ＝ mul-Large-Ring R (raise-zero-Large-Ring R l1) x
            by
              ap-binary
                ( mul-Large-Ring R)
                ( right-unit-law-add-Ab
                  ( ab-Large-Ab (large-ab-Large-Ring R) l1)
                  ( raise-zero-Large-Ring R l1))
                ( refl))

    left-zero-law-mul-Large-Ring :
      {l : Level} (x : type-Large-Ring R l) →
      sim-Large-Ring R
        ( mul-Large-Ring R (zero-Large-Ring R) x)
        ( zero-Large-Ring R)
    left-zero-law-mul-Large-Ring {l} x =
      inv-tr
        ( λ y → sim-Large-Ring R y (zero-Large-Ring R))
        ( ( ap-binary
            ( mul-Large-Ring R)
            ( inv (eq-raise-Large-Ring R lzero (zero-Large-Ring R)))
            ( refl)) ∙
          ( left-raise-zero-law-mul-Large-Ring lzero x))
        ( sim-raise-Large-Ring' R l (zero-Large-Ring R))

    right-raise-zero-law-mul-Large-Ring :
      (l1 : Level) {l2 : Level} (x : type-Large-Ring R l2) →
      mul-Large-Ring R x (raise-zero-Large-Ring R l1) ＝
      raise-zero-Large-Ring R (l1 ⊔ l2)
    right-raise-zero-law-mul-Large-Ring l1 {l2} x =
      is-zero-is-idempotent-Ab
        ( ab-Large-Ab (large-ab-Large-Ring R) (l1 ⊔ l2))
        ( equational-reasoning
          add-Large-Ring
            ( R)
            ( mul-Large-Ring R x (raise-zero-Large-Ring R l1))
            ( mul-Large-Ring R x (raise-zero-Large-Ring R l1))
          ＝
            mul-Large-Ring R
              ( x)
              ( add-Large-Ring R
                ( raise-zero-Large-Ring R l1)
                ( raise-zero-Large-Ring R l1))
            by inv (left-distributive-mul-add-Large-Ring R _ _ _)
          ＝ mul-Large-Ring R x (raise-zero-Large-Ring R l1)
            by
              ap-binary
                ( mul-Large-Ring R)
                ( refl)
                ( right-unit-law-add-Ab
                  ( ab-Large-Ab (large-ab-Large-Ring R) l1)
                  ( raise-zero-Large-Ring R l1)))

    right-zero-law-mul-Large-Ring :
      {l : Level} (x : type-Large-Ring R l) →
      sim-Large-Ring R
        ( mul-Large-Ring R x (zero-Large-Ring R))
        ( zero-Large-Ring R)
    right-zero-law-mul-Large-Ring {l} x =
      inv-tr
        ( λ y → sim-Large-Ring R y (zero-Large-Ring R))
        ( ( ap-binary
            ( mul-Large-Ring R)
            ( refl)
            ( inv (eq-raise-Large-Ring R lzero (zero-Large-Ring R)))) ∙
          ( right-raise-zero-law-mul-Large-Ring lzero x))
        ( sim-raise-Large-Ring' R l (zero-Large-Ring R))
```
