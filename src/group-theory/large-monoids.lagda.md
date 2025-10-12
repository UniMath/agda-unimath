# Large monoids

```agda
module group-theory.large-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.large-similarity-relations
open import foundation.subtypes
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.homomorphisms-monoids
open import group-theory.large-semigroups
open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Idea

A {{#concept "large monoid" Agda=Large-Monoid}} is a
[large semigroup](group-theory.large-semigroups.md) with an
[identity element](foundation.unital-binary-operations.md), further endowed with
a [large similarity relation](foundation.large-similarity-relations.md)
preserved by the binary operation of the monoid, and an operation to
[raise the universe level](foundation.raising-universe-levels.md) of an element.

## Definition

```agda
record Large-Monoid (α : Level → Level) (β : Level → Level → Level) : UUω where
  constructor
    make-Large-Monoid
  field
    large-semigroup-Large-Monoid : Large-Semigroup α

  type-Large-Monoid : (l : Level) → UU (α l)
  type-Large-Monoid = type-Large-Semigroup large-semigroup-Large-Monoid

  set-Large-Monoid : (l : Level) → Set (α l)
  set-Large-Monoid = set-Large-Semigroup large-semigroup-Large-Monoid

  field
    large-similarity-relation-Large-Monoid :
      Large-Similarity-Relation β type-Large-Monoid

  sim-prop-Large-Monoid : Large-Relation-Prop β type-Large-Monoid
  sim-prop-Large-Monoid =
    sim-prop-Large-Similarity-Relation large-similarity-relation-Large-Monoid

  sim-Large-Monoid : Large-Relation β type-Large-Monoid
  sim-Large-Monoid x y = type-Prop (sim-prop-Large-Monoid x y)

  field
    raise-Large-Monoid :
      {l1 : Level} (l2 : Level) → type-Large-Monoid l1 →
      type-Large-Monoid (l1 ⊔ l2)
    sim-raise-Large-Monoid :
      {l1 : Level} (l2 : Level) (x : type-Large-Monoid l1) →
      sim-Large-Monoid x (raise-Large-Monoid l2 x)

  mul-Large-Monoid :
    {l1 l2 : Level} → type-Large-Monoid l1 → type-Large-Monoid l2 →
    type-Large-Monoid (l1 ⊔ l2)
  mul-Large-Monoid =
    mul-Large-Semigroup large-semigroup-Large-Monoid

  ap-mul-Large-Monoid :
    {l1 l2 : Level} →
    {x x' : type-Large-Monoid l1} → x ＝ x' →
    {y y' : type-Large-Monoid l2} → y ＝ y' →
    mul-Large-Monoid x y ＝ mul-Large-Monoid x' y'
  ap-mul-Large-Monoid = ap-binary mul-Large-Monoid

  field
    preserves-sim-mul-Large-Monoid :
      {l1 l2 l3 l4 : Level}
      (x : type-Large-Monoid l1) (x' : type-Large-Monoid l2) →
      sim-Large-Monoid x x' →
      (y : type-Large-Monoid l3) (y' : type-Large-Monoid l4) →
      sim-Large-Monoid y y' →
      sim-Large-Monoid (mul-Large-Monoid x y) (mul-Large-Monoid x' y')

  field
    unit-Large-Monoid : type-Large-Monoid lzero
    left-unit-law-mul-Large-Monoid :
      {l : Level} (x : type-Large-Monoid l) →
      mul-Large-Monoid unit-Large-Monoid x ＝ x
    right-unit-law-mul-Large-Monoid :
      {l : Level} (x : type-Large-Monoid l) →
      mul-Large-Monoid x unit-Large-Monoid ＝ x

  raise-unit-Large-Monoid : (l : Level) → type-Large-Monoid l
  raise-unit-Large-Monoid l = raise-Large-Monoid l unit-Large-Monoid

  associative-mul-Large-Monoid :
    {l1 l2 l3 : Level} →
    (x : type-Large-Monoid l1) (y : type-Large-Monoid l2)
    (z : type-Large-Monoid l3) →
    mul-Large-Monoid (mul-Large-Monoid x y) z ＝
    mul-Large-Monoid x (mul-Large-Monoid y z)
  associative-mul-Large-Monoid =
    associative-mul-Large-Semigroup large-semigroup-Large-Monoid

  semigroup-Large-Monoid : (l : Level) → Semigroup (α l)
  semigroup-Large-Monoid =
    semigroup-Large-Semigroup large-semigroup-Large-Monoid

open Large-Monoid public
```

## Properties

### The similarity relation of a large monoid is a large similarity relation

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  refl-sim-Large-Monoid :
    is-reflexive-Large-Relation-Prop
      ( type-Large-Monoid M)
      ( sim-prop-Large-Monoid M)
  refl-sim-Large-Monoid =
    refl-sim-Large-Similarity-Relation
      ( large-similarity-relation-Large-Monoid M)

  sim-eq-Large-Monoid :
    {l : Level} {x y : type-Large-Monoid M l} → x ＝ y → sim-Large-Monoid M x y
  sim-eq-Large-Monoid =
    sim-eq-Large-Similarity-Relation
      ( large-similarity-relation-Large-Monoid M)

  symmetric-sim-Large-Monoid :
    {l1 l2 : Level} (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2) →
    sim-Large-Monoid M x y → sim-Large-Monoid M y x
  symmetric-sim-Large-Monoid =
    symmetric-sim-Large-Similarity-Relation
      ( large-similarity-relation-Large-Monoid M)

  transitive-sim-Large-Monoid :
    {l1 l2 l3 : Level} →
    (x : type-Large-Monoid M l1) →
    (y : type-Large-Monoid M l2) →
    (z : type-Large-Monoid M l3) →
    sim-Large-Monoid M y z → sim-Large-Monoid M x y → sim-Large-Monoid M x z
  transitive-sim-Large-Monoid =
    transitive-sim-Large-Similarity-Relation
      ( large-similarity-relation-Large-Monoid M)

  eq-sim-Large-Monoid :
    {l : Level} (x y : type-Large-Monoid M l) → sim-Large-Monoid M x y → x ＝ y
  eq-sim-Large-Monoid =
    eq-sim-Large-Similarity-Relation (large-similarity-relation-Large-Monoid M)

  sim-raise-Large-Monoid' :
    {l1 : Level} (l2 : Level) (x : type-Large-Monoid M l1) →
    sim-Large-Monoid M (raise-Large-Monoid M l2 x) x
  sim-raise-Large-Monoid' l2 x =
    symmetric-sim-Large-Monoid _ _ (sim-raise-Large-Monoid M l2 x)
```

### Raising an element of a large monoid by two universe levels is equivalent to raising it by the lub of the universe levels

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  raise-raise-Large-Monoid :
    {l1 l2 l3 : Level} → (x : type-Large-Monoid M l1) →
    raise-Large-Monoid M l2 (raise-Large-Monoid M l3 x) ＝
    raise-Large-Monoid M (l2 ⊔ l3) x
  raise-raise-Large-Monoid {l1} {l2} {l3} x =
    inv
      ( eq-sim-Large-Monoid M _ _
        ( transitive-sim-Large-Monoid M
          ( raise-Large-Monoid M (l2 ⊔ l3) x)
          ( x)
          ( raise-Large-Monoid M l2 (raise-Large-Monoid M l3 x))
          ( transitive-sim-Large-Monoid M _ _ _
            ( sim-raise-Large-Monoid M _ _)
            ( sim-raise-Large-Monoid M _ _))
          ( sim-raise-Large-Monoid' M _ _)))
```

### Raising the universe level of an element of a large monoid is the identity for lower universe levels

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  abstract
    eq-raise-Large-Monoid :
      (l1 : Level) {l2 : Level} (x : type-Large-Monoid M (l1 ⊔ l2)) →
      raise-Large-Monoid M l2 x ＝ x
    eq-raise-Large-Monoid _ x =
      eq-sim-Large-Monoid M _ _ (sim-raise-Large-Monoid' M _ x)

    raise-unit-lzero-Large-Monoid :
      raise-unit-Large-Monoid M lzero ＝ unit-Large-Monoid M
    raise-unit-lzero-Large-Monoid = eq-raise-Large-Monoid _ _
```

### Similarity reasoning in large monoids

```agda
module
  similarity-reasoning-Large-Monoid
    {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  open similarity-reasoning-Large-Similarity-Relation
    ( large-similarity-relation-Large-Monoid M) public
```

### The raise operation characterizes the similarity relation

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  open similarity-reasoning-Large-Monoid M

  abstract
    sim-eq-raise-Large-Monoid :
      {l1 l2 : Level} →
      (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2) →
      raise-Large-Monoid M l2 x ＝ raise-Large-Monoid M l1 y →
      sim-Large-Monoid M x y
    sim-eq-raise-Large-Monoid {l1} {l2} x y x=y =
      similarity-reasoning
        x
        ~ raise-Large-Monoid M l2 x
          by sim-raise-Large-Monoid M l2 x
        ~ raise-Large-Monoid M l1 y
          by sim-eq-Large-Monoid M x=y
        ~ y
          by symmetric-sim-Large-Monoid M _ _ (sim-raise-Large-Monoid M l1 y)

    eq-raise-sim-Large-Monoid :
      {l1 l2 : Level} →
      (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2) →
      sim-Large-Monoid M x y →
      raise-Large-Monoid M l2 x ＝ raise-Large-Monoid M l1 y
    eq-raise-sim-Large-Monoid {l1} {l2} x y x~y =
      eq-sim-Large-Monoid M _ _
        ( similarity-reasoning
          raise-Large-Monoid M l2 x
          ~ x
            by sim-raise-Large-Monoid' M l2 x
          ~ y
            by x~y
          ~ raise-Large-Monoid M l1 y
            by sim-raise-Large-Monoid M l1 y)

  sim-iff-eq-raise-Large-Monoid :
    {l1 l2 : Level} →
    (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2) →
    ( sim-Large-Monoid M x y) ↔
    ( raise-Large-Monoid M l2 x ＝ raise-Large-Monoid M l1 y)
  sim-iff-eq-raise-Large-Monoid x y =
    ( eq-raise-sim-Large-Monoid x y ,
      sim-eq-raise-Large-Monoid x y)
```

### Multiplication preserves similarity on each side

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  abstract
    preserves-sim-left-mul-Large-Monoid :
      {l1 l2 l3 : Level} (y : type-Large-Monoid M l1) →
      (x : type-Large-Monoid M l2) (x' : type-Large-Monoid M l3) →
      sim-Large-Monoid M x x' →
      sim-Large-Monoid M (mul-Large-Monoid M x y) (mul-Large-Monoid M x' y)
    preserves-sim-left-mul-Large-Monoid y x x' x~x' =
      preserves-sim-mul-Large-Monoid M x x' x~x' y y (refl-sim-Large-Monoid M y)

    preserves-sim-right-mul-Large-Monoid :
      {l1 l2 l3 : Level} (x : type-Large-Monoid M l1) →
      (y : type-Large-Monoid M l2) (y' : type-Large-Monoid M l3) →
      sim-Large-Monoid M y y' →
      sim-Large-Monoid M (mul-Large-Monoid M x y) (mul-Large-Monoid M x y')
    preserves-sim-right-mul-Large-Monoid x =
      preserves-sim-mul-Large-Monoid M x x (refl-sim-Large-Monoid M x)
```

### Floating raised universe levels out of multiplication

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  abstract
    raise-right-mul-Large-Monoid :
      {l1 l2 l3 : Level} →
      (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2) →
      mul-Large-Monoid M x (raise-Large-Monoid M l3 y) ＝
      raise-Large-Monoid M l3 (mul-Large-Monoid M x y)
    raise-right-mul-Large-Monoid {l3 = l3} x y =
      let open similarity-reasoning-Large-Monoid M
      in
        eq-sim-Large-Monoid M _ _
          ( similarity-reasoning
            mul-Large-Monoid M x (raise-Large-Monoid M l3 y)
            ~ mul-Large-Monoid M x y
              by
                preserves-sim-right-mul-Large-Monoid M x _ _
                  ( sim-raise-Large-Monoid' M _ _)
            ~ raise-Large-Monoid M l3 (mul-Large-Monoid M x y)
              by sim-raise-Large-Monoid M _ _)

    raise-left-mul-Large-Monoid :
      {l1 l2 l3 : Level} →
      (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2) →
      mul-Large-Monoid M (raise-Large-Monoid M l3 x) y ＝
      raise-Large-Monoid M l3 (mul-Large-Monoid M x y)
    raise-left-mul-Large-Monoid {l3 = l3} x y =
      let open similarity-reasoning-Large-Monoid M
      in
        eq-sim-Large-Monoid M _ _
          ( similarity-reasoning
            mul-Large-Monoid M (raise-Large-Monoid M l3 x) y
            ~ mul-Large-Monoid M x y
              by
                preserves-sim-left-mul-Large-Monoid M y _ _
                  ( sim-raise-Large-Monoid' M _ _)
            ~ raise-Large-Monoid M l3 (mul-Large-Monoid M x y)
              by sim-raise-Large-Monoid M _ _)

    raise-mul-Large-Monoid :
      {l1 l2 l3 l4 : Level} →
      (x : type-Large-Monoid M l1) (y : type-Large-Monoid M l2) →
      mul-Large-Monoid M
        ( raise-Large-Monoid M l3 x)
        ( raise-Large-Monoid M l4 y) ＝
      raise-Large-Monoid M (l3 ⊔ l4) (mul-Large-Monoid M x y)
    raise-mul-Large-Monoid {l3 = l3} {l4 = l4} x y =
      equational-reasoning
        mul-Large-Monoid M
          ( raise-Large-Monoid M l3 x)
          ( raise-Large-Monoid M l4 y)
        ＝
          raise-Large-Monoid M l3
            ( mul-Large-Monoid M x (raise-Large-Monoid M l4 y))
          by raise-left-mul-Large-Monoid _ _
        ＝
          raise-Large-Monoid M l3
            ( raise-Large-Monoid M l4 (mul-Large-Monoid M x y))
          by ap (raise-Large-Monoid M l3) (raise-right-mul-Large-Monoid _ _)
        ＝ raise-Large-Monoid M (l3 ⊔ l4) (mul-Large-Monoid M x y)
          by raise-raise-Large-Monoid M _
```

### Raised unit laws

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  abstract
    raise-left-unit-law-Large-Monoid :
      {l1 l2 : Level} (x : type-Large-Monoid M l1) →
      mul-Large-Monoid M (raise-unit-Large-Monoid M l2) x ＝
      raise-Large-Monoid M l2 x
    raise-left-unit-law-Large-Monoid {l1} {l2} x =
      equational-reasoning
        mul-Large-Monoid M (raise-unit-Large-Monoid M l2) x
        ＝ raise-Large-Monoid M l2 (mul-Large-Monoid M (unit-Large-Monoid M) x)
          by raise-left-mul-Large-Monoid M _ _
        ＝ raise-Large-Monoid M l2 x
          by ap (raise-Large-Monoid M l2) (left-unit-law-mul-Large-Monoid M x)

    raise-right-unit-law-Large-Monoid :
      {l1 l2 : Level} (x : type-Large-Monoid M l1) →
      mul-Large-Monoid M x (raise-unit-Large-Monoid M l2) ＝
      raise-Large-Monoid M l2 x
    raise-right-unit-law-Large-Monoid {l1} {l2} x =
      equational-reasoning
        mul-Large-Monoid M x (raise-unit-Large-Monoid M l2)
        ＝ raise-Large-Monoid M l2 (mul-Large-Monoid M x (unit-Large-Monoid M))
          by raise-right-mul-Large-Monoid M _ _
        ＝ raise-Large-Monoid M l2 x
          by ap (raise-Large-Monoid M l2) (right-unit-law-mul-Large-Monoid M x)
```

### Small monoids from large monoids

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  monoid-Large-Monoid : (l : Level) → Monoid (α l)
  monoid-Large-Monoid l =
    ( semigroup-Large-Monoid M l ,
      raise-unit-Large-Monoid M l ,
      ( λ x →
        raise-left-unit-law-Large-Monoid M x ∙ eq-raise-Large-Monoid M l _) ,
      ( λ x →
        raise-right-unit-law-Large-Monoid M x ∙ eq-raise-Large-Monoid M l _))
```

### The raise operation is a monoid homomorphism

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  (l1 l2 : Level)
  where

  hom-raise-Large-Monoid :
    hom-Monoid
      ( monoid-Large-Monoid M l1)
      ( monoid-Large-Monoid M (l1 ⊔ l2))
  hom-raise-Large-Monoid =
    ( ( raise-Large-Monoid M l2 ,
        inv (raise-mul-Large-Monoid M _ _)) ,
      raise-raise-Large-Monoid M _)
```

### Having a similar element at a universe level is a proposition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} (M : Large-Monoid α β)
  where

  open similarity-reasoning-Large-Monoid M

  abstract
    is-prop-sim-Large-Monoid :
      {l1 : Level} (l2 : Level) (x : type-Large-Monoid M l1) →
      is-prop (Σ (type-Large-Monoid M l2) (sim-Large-Monoid M x))
    is-prop-sim-Large-Monoid l2 x =
      is-prop-all-elements-equal
        ( λ (y , x~y) (y' , x~y') →
          eq-type-subtype
            ( sim-prop-Large-Monoid M x)
            ( eq-sim-Large-Monoid M _ _
              ( similarity-reasoning
                y
                ~ x by symmetric-sim-Large-Monoid M _ _ x~y
                ~ y' by x~y')))
```
