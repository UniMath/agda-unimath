# Large left modules over large rings

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.large-left-modules-large-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cumulative-large-sets
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.function-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.large-similarity-relations
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.similarity-preserving-binary-maps-cumulative-large-sets
open import foundation.similarity-preserving-maps-cumulative-large-sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.large-abelian-groups

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-maps-left-modules-rings

open import ring-theory.large-rings
```

</details>

## Idea

A
{{#concept "large left module" Disambiguation="over a large ring" Agda=Large-Left-Module-Large-Ring}}
over a [large ring](ring-theory.large-rings.md) `R` is a
[large abelian group](group-theory.large-abelian-groups.md) `M` endowed with an
action `R → M → M` such that

```text
  r(x+y) = rx + ry
  (r+s)x = rx + sx
   (sr)x = s(rx)
      1x = x
```

which also imply

```text
      0x = 0
      r0 = 0
   (-r)x = -(rx)
   r(-x) = -(rx)
```

## Definition

```agda
record
  Large-Left-Module-Large-Ring
  {α : Level → Level}
  {β : Level → Level → Level}
  (δ : Level → Level)
  (γ : Level → Level → Level)
  (R : Large-Ring α β) :
  UUω
  where

  constructor
    make-Large-Left-Module-Large-Ring

  field
    large-ab-Large-Left-Module-Large-Ring : Large-Ab δ γ

  cumulative-large-set-Large-Left-Module-Large-Ring : Cumulative-Large-Set δ γ
  cumulative-large-set-Large-Left-Module-Large-Ring =
    cumulative-large-set-Large-Ab large-ab-Large-Left-Module-Large-Ring

  set-Large-Left-Module-Large-Ring : (l : Level) → Set (δ l)
  set-Large-Left-Module-Large-Ring =
    set-Large-Ab large-ab-Large-Left-Module-Large-Ring

  type-Large-Left-Module-Large-Ring : (l : Level) → UU (δ l)
  type-Large-Left-Module-Large-Ring l =
    type-Set (set-Large-Left-Module-Large-Ring l)

  add-Large-Left-Module-Large-Ring :
    {l1 l2 : Level} →
    type-Large-Left-Module-Large-Ring l1 →
    type-Large-Left-Module-Large-Ring l2 →
    type-Large-Left-Module-Large-Ring (l1 ⊔ l2)
  add-Large-Left-Module-Large-Ring =
    add-Large-Ab large-ab-Large-Left-Module-Large-Ring

  add-Large-Left-Module-Large-Ring' :
    {l1 l2 : Level} →
    type-Large-Left-Module-Large-Ring l1 →
    type-Large-Left-Module-Large-Ring l2 →
    type-Large-Left-Module-Large-Ring (l1 ⊔ l2)
  add-Large-Left-Module-Large-Ring' x y =
    add-Large-Left-Module-Large-Ring y x

  neg-Large-Left-Module-Large-Ring :
    {l : Level} →
    type-Large-Left-Module-Large-Ring l → type-Large-Left-Module-Large-Ring l
  neg-Large-Left-Module-Large-Ring =
    neg-Large-Ab large-ab-Large-Left-Module-Large-Ring

  field
    sim-preserving-binary-map-mul-Large-Left-Module-Large-Ring :
      sim-preserving-binary-map-Cumulative-Large-Set
        ( cumulative-large-set-Large-Ring R)
        ( cumulative-large-set-Large-Left-Module-Large-Ring)
        ( cumulative-large-set-Large-Left-Module-Large-Ring)

  mul-Large-Left-Module-Large-Ring :
    {l1 l2 : Level} →
    type-Large-Ring R l1 →
    type-Large-Left-Module-Large-Ring l2 →
    type-Large-Left-Module-Large-Ring (l1 ⊔ l2)
  mul-Large-Left-Module-Large-Ring =
    map-sim-preserving-binary-map-Cumulative-Large-Set
      ( cumulative-large-set-Large-Ring R)
      ( cumulative-large-set-Large-Left-Module-Large-Ring)
      ( cumulative-large-set-Large-Left-Module-Large-Ring)
      ( sim-preserving-binary-map-mul-Large-Left-Module-Large-Ring)

  mul-Large-Left-Module-Large-Ring' :
    {l1 l2 : Level} →
    type-Large-Left-Module-Large-Ring l1 →
    type-Large-Ring R l2 →
    type-Large-Left-Module-Large-Ring (l1 ⊔ l2)
  mul-Large-Left-Module-Large-Ring' x r = mul-Large-Left-Module-Large-Ring r x

  field
    left-distributive-mul-add-Large-Left-Module-Large-Ring :
      {l1 l2 l3 : Level} →
      (a : type-Large-Ring R l1) →
      (x : type-Large-Left-Module-Large-Ring l2) →
      (y : type-Large-Left-Module-Large-Ring l3) →
      mul-Large-Left-Module-Large-Ring
        ( a)
        ( add-Large-Left-Module-Large-Ring x y) ＝
      add-Large-Left-Module-Large-Ring
        ( mul-Large-Left-Module-Large-Ring a x)
        ( mul-Large-Left-Module-Large-Ring a y)

    right-distributive-mul-add-Large-Left-Module-Large-Ring :
      {l1 l2 l3 : Level} →
      (a : type-Large-Ring R l1) →
      (b : type-Large-Ring R l2) →
      (x : type-Large-Left-Module-Large-Ring l3) →
      mul-Large-Left-Module-Large-Ring (add-Large-Ring R a b) x ＝
      add-Large-Left-Module-Large-Ring
        ( mul-Large-Left-Module-Large-Ring a x)
        ( mul-Large-Left-Module-Large-Ring b x)

    associative-mul-Large-Left-Module-Large-Ring :
      {l1 l2 l3 : Level} →
      (a : type-Large-Ring R l1) →
      (b : type-Large-Ring R l2) →
      (x : type-Large-Left-Module-Large-Ring l3) →
      mul-Large-Left-Module-Large-Ring (mul-Large-Ring R a b) x ＝
      mul-Large-Left-Module-Large-Ring a (mul-Large-Left-Module-Large-Ring b x)

    left-unit-law-mul-Large-Left-Module-Large-Ring :
      {l : Level} (x : type-Large-Left-Module-Large-Ring l) →
      mul-Large-Left-Module-Large-Ring (one-Large-Ring R) x ＝ x

  ap-mul-Large-Left-Module-Large-Ring :
    {l1 l2 : Level} →
    {a a' : type-Large-Ring R l1} →
    {x x' : type-Large-Left-Module-Large-Ring l2} →
    a ＝ a' → x ＝ x' →
    mul-Large-Left-Module-Large-Ring a x ＝
    mul-Large-Left-Module-Large-Ring a' x'
  ap-mul-Large-Left-Module-Large-Ring a=a' x=x' =
    ap-binary mul-Large-Left-Module-Large-Ring a=a' x=x'

open Large-Left-Module-Large-Ring public
```

## Properties

### Similarity

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  large-similarity-relation-Large-Left-Module-Large-Ring :
    Large-Similarity-Relation γ (type-Large-Left-Module-Large-Ring M)
  large-similarity-relation-Large-Left-Module-Large-Ring =
    large-similarity-relation-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  sim-prop-Large-Left-Module-Large-Ring :
    Large-Relation-Prop γ (type-Large-Left-Module-Large-Ring M)
  sim-prop-Large-Left-Module-Large-Ring =
    sim-prop-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  sim-Large-Left-Module-Large-Ring :
    Large-Relation γ (type-Large-Left-Module-Large-Ring M)
  sim-Large-Left-Module-Large-Ring =
    sim-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  refl-sim-Large-Left-Module-Large-Ring :
    is-reflexive-Large-Relation
      ( type-Large-Left-Module-Large-Ring M)
      ( sim-Large-Left-Module-Large-Ring)
  refl-sim-Large-Left-Module-Large-Ring =
    refl-sim-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  symmetric-sim-Large-Left-Module-Large-Ring :
    is-symmetric-Large-Relation
      ( type-Large-Left-Module-Large-Ring M)
      ( sim-Large-Left-Module-Large-Ring)
  symmetric-sim-Large-Left-Module-Large-Ring =
    symmetric-sim-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  transitive-sim-Large-Left-Module-Large-Ring :
    is-transitive-Large-Relation
      ( type-Large-Left-Module-Large-Ring M)
      ( sim-Large-Left-Module-Large-Ring)
  transitive-sim-Large-Left-Module-Large-Ring =
    transitive-sim-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  sim-eq-Large-Left-Module-Large-Ring :
    {l : Level} {x y : type-Large-Left-Module-Large-Ring M l} →
    x ＝ y → sim-Large-Left-Module-Large-Ring x y
  sim-eq-Large-Left-Module-Large-Ring =
    sim-eq-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  eq-sim-Large-Left-Module-Large-Ring :
    {l : Level} (x y : type-Large-Left-Module-Large-Ring M l) →
    sim-Large-Left-Module-Large-Ring x y → x ＝ y
  eq-sim-Large-Left-Module-Large-Ring =
    eq-sim-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)
```

### Raising universe levels

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  raise-Large-Left-Module-Large-Ring :
    {l0 : Level} (l : Level) →
    type-Large-Left-Module-Large-Ring M l0 →
    type-Large-Left-Module-Large-Ring M (l0 ⊔ l)
  raise-Large-Left-Module-Large-Ring =
    raise-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  sim-raise-Large-Left-Module-Large-Ring :
    {l0 : Level} (l : Level) (x : type-Large-Left-Module-Large-Ring M l0) →
    sim-Large-Left-Module-Large-Ring M
      ( x)
      ( raise-Large-Left-Module-Large-Ring l x)
  sim-raise-Large-Left-Module-Large-Ring =
    sim-raise-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  sim-raise-Large-Left-Module-Large-Ring' :
    {l0 : Level} (l : Level) (x : type-Large-Left-Module-Large-Ring M l0) →
    sim-Large-Left-Module-Large-Ring M
      ( raise-Large-Left-Module-Large-Ring l x)
      ( x)
  sim-raise-Large-Left-Module-Large-Ring' =
    sim-raise-Large-Ab' (large-ab-Large-Left-Module-Large-Ring M)

  eq-raise-Large-Left-Module-Large-Ring :
    {l : Level} (x : type-Large-Left-Module-Large-Ring M l) →
    raise-Large-Left-Module-Large-Ring l x ＝ x
  eq-raise-Large-Left-Module-Large-Ring =
    eq-raise-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  eq-raise-leq-level-Large-Left-Module-Large-Ring :
    (l1 : Level) {l2 : Level}
    (x : type-Large-Left-Module-Large-Ring M (l1 ⊔ l2)) →
    raise-Large-Left-Module-Large-Ring l2 x ＝ x
  eq-raise-leq-level-Large-Left-Module-Large-Ring =
    eq-raise-leq-level-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  is-emb-raise-Large-Left-Module-Large-Ring :
    (l1 l2 : Level) → is-emb (raise-Large-Left-Module-Large-Ring {l1} l2)
  is-emb-raise-Large-Left-Module-Large-Ring =
    is-emb-raise-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  emb-raise-Large-Left-Module-Large-Ring :
    (l1 l2 : Level) →
    type-Large-Left-Module-Large-Ring M l1 ↪
    type-Large-Left-Module-Large-Ring M (l1 ⊔ l2)
  emb-raise-Large-Left-Module-Large-Ring =
    emb-raise-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  raise-raise-Large-Left-Module-Large-Ring :
    {l0 l1 l2 : Level} (x : type-Large-Left-Module-Large-Ring M l0) →
    raise-Large-Left-Module-Large-Ring
      ( l1)
      ( raise-Large-Left-Module-Large-Ring l2 x) ＝
    raise-Large-Left-Module-Large-Ring (l1 ⊔ l2) x
  raise-raise-Large-Left-Module-Large-Ring =
    raise-raise-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  eq-raise-sim-Large-Left-Module-Large-Ring :
    {l1 l2 : Level}
    (x : type-Large-Left-Module-Large-Ring M l1)
    (y : type-Large-Left-Module-Large-Ring M l2) →
    sim-Large-Left-Module-Large-Ring M x y →
    raise-Large-Left-Module-Large-Ring l2 x ＝
    raise-Large-Left-Module-Large-Ring l1 y
  eq-raise-sim-Large-Left-Module-Large-Ring =
    eq-raise-sim-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  sim-eq-raise-Large-Left-Module-Large-Ring :
    {l1 l2 : Level}
    (x : type-Large-Left-Module-Large-Ring M l1)
    (y : type-Large-Left-Module-Large-Ring M l2) →
    ( raise-Large-Left-Module-Large-Ring l2 x ＝
      raise-Large-Left-Module-Large-Ring l1 y) →
    sim-Large-Left-Module-Large-Ring M x y
  sim-eq-raise-Large-Left-Module-Large-Ring =
    sim-eq-raise-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  eq-raise-iff-sim-Large-Left-Module-Large-Ring :
    {l1 l2 : Level} →
    (x : type-Large-Left-Module-Large-Ring M l1)
    (y : type-Large-Left-Module-Large-Ring M l2) →
    ( sim-Large-Left-Module-Large-Ring M x y ↔
      ( raise-Large-Left-Module-Large-Ring l2 x ＝
        raise-Large-Left-Module-Large-Ring l1 y))
  eq-raise-iff-sim-Large-Left-Module-Large-Ring =
    eq-raise-iff-sim-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  eq-raise-sim-Large-Left-Module-Large-Ring' :
    {l1 l2 : Level}
    (x : type-Large-Left-Module-Large-Ring M (l1 ⊔ l2))
    (y : type-Large-Left-Module-Large-Ring M l2) →
    sim-Large-Left-Module-Large-Ring M x y →
    x ＝ raise-Large-Left-Module-Large-Ring l1 y
  eq-raise-sim-Large-Left-Module-Large-Ring' =
    eq-raise-sim-Large-Ab' (large-ab-Large-Left-Module-Large-Ring M)
```

### Similarity preservation of addition

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  sim-preserving-binary-operator-add-Large-Left-Module-Large-Ring :
    sim-preserving-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Left-Module-Large-Ring M)
  sim-preserving-binary-operator-add-Large-Left-Module-Large-Ring =
    sim-preserving-binary-operator-add-Large-Ab
      ( large-ab-Large-Left-Module-Large-Ring M)

  preserves-sim-add-Large-Left-Module-Large-Ring :
    preserves-sim-binary-operator-Cumulative-Large-Set
      ( cumulative-large-set-Large-Left-Module-Large-Ring M)
      ( add-Large-Left-Module-Large-Ring M)
  preserves-sim-add-Large-Left-Module-Large-Ring =
    preserves-sim-add-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  sim-preserving-map-left-add-Large-Left-Module-Large-Ring :
    {l : Level} (x : type-Large-Left-Module-Large-Ring M l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Left-Module-Large-Ring M)
  sim-preserving-map-left-add-Large-Left-Module-Large-Ring =
    sim-preserving-map-left-add-Large-Ab
      ( large-ab-Large-Left-Module-Large-Ring M)

  preserves-sim-left-add-Large-Left-Module-Large-Ring :
    {l : Level} (x : type-Large-Left-Module-Large-Ring M l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Left-Module-Large-Ring M)
      ( add-Large-Left-Module-Large-Ring M x)
  preserves-sim-left-add-Large-Left-Module-Large-Ring =
    preserves-sim-left-add-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  sim-preserving-map-right-add-Large-Left-Module-Large-Ring :
    {l : Level} (y : type-Large-Left-Module-Large-Ring M l) →
    sim-preserving-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Left-Module-Large-Ring M)
  sim-preserving-map-right-add-Large-Left-Module-Large-Ring =
    sim-preserving-map-right-add-Large-Ab
      ( large-ab-Large-Left-Module-Large-Ring M)

  preserves-sim-right-add-Large-Left-Module-Large-Ring :
    {l : Level} (y : type-Large-Left-Module-Large-Ring M l) →
    preserves-sim-endomap-Cumulative-Large-Set
      ( l ⊔_)
      ( cumulative-large-set-Large-Left-Module-Large-Ring M)
      ( add-Large-Left-Module-Large-Ring' M y)
  preserves-sim-right-add-Large-Left-Module-Large-Ring =
    preserves-sim-right-add-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)
```

### Raising universe levels in addition

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  abstract
    add-raise-right-Large-Left-Module-Large-Ring :
      {l1 l2 : Level} (l3 : Level)
      (x : type-Large-Left-Module-Large-Ring M l1)
      (y : type-Large-Left-Module-Large-Ring M l2) →
      add-Large-Left-Module-Large-Ring M
        ( x)
        ( raise-Large-Left-Module-Large-Ring M l3 y) ＝
      raise-Large-Left-Module-Large-Ring M
        ( l3)
        ( add-Large-Left-Module-Large-Ring M x y)
    add-raise-right-Large-Left-Module-Large-Ring =
      add-raise-right-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

    add-raise-left-Large-Left-Module-Large-Ring :
      {l1 l2 : Level} (l3 : Level)
      (x : type-Large-Left-Module-Large-Ring M l1)
      (y : type-Large-Left-Module-Large-Ring M l2) →
      add-Large-Left-Module-Large-Ring M
        ( raise-Large-Left-Module-Large-Ring M l3 x)
        ( y) ＝
      raise-Large-Left-Module-Large-Ring M l3
        ( add-Large-Left-Module-Large-Ring M x y)
    add-raise-left-Large-Left-Module-Large-Ring =
      add-raise-left-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

    add-raise-raise-Large-Left-Module-Large-Ring :
      {l1 l2 : Level} (l3 l4 : Level)
      (x : type-Large-Left-Module-Large-Ring M l1)
      (y : type-Large-Left-Module-Large-Ring M l2) →
      add-Large-Left-Module-Large-Ring M
        ( raise-Large-Left-Module-Large-Ring M l3 x)
        ( raise-Large-Left-Module-Large-Ring M l4 y) ＝
      raise-Large-Left-Module-Large-Ring M
        ( l3 ⊔ l4)
        ( add-Large-Left-Module-Large-Ring M x y)
    add-raise-raise-Large-Left-Module-Large-Ring =
      add-raise-raise-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)
```

### The negation operation preserves similarity

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  sim-preserving-endomap-neg-Large-Left-Module-Large-Ring :
    sim-preserving-endomap-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Large-Left-Module-Large-Ring M)
  sim-preserving-endomap-neg-Large-Left-Module-Large-Ring =
    sim-preserving-endomap-neg-Large-Ab
      ( large-ab-Large-Left-Module-Large-Ring M)

  preserves-sim-neg-Large-Left-Module-Large-Ring :
    preserves-sim-endomap-Cumulative-Large-Set
      ( id)
      ( cumulative-large-set-Large-Left-Module-Large-Ring M)
      ( neg-Large-Left-Module-Large-Ring M)
  preserves-sim-neg-Large-Left-Module-Large-Ring =
    preserves-sim-neg-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)
```

### Semigroup laws of addition

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  associative-add-Large-Left-Module-Large-Ring :
    {l1 l2 l3 : Level}
    (x : type-Large-Left-Module-Large-Ring M l1)
    (y : type-Large-Left-Module-Large-Ring M l2)
    (z : type-Large-Left-Module-Large-Ring M l3) →
    add-Large-Left-Module-Large-Ring M
      ( add-Large-Left-Module-Large-Ring M x y)
      ( z) ＝
    add-Large-Left-Module-Large-Ring M
      ( x)
      ( add-Large-Left-Module-Large-Ring M y z)
  associative-add-Large-Left-Module-Large-Ring =
    associative-add-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)
```

### Monoid laws of addition

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  zero-Large-Left-Module-Large-Ring : type-Large-Left-Module-Large-Ring M lzero
  zero-Large-Left-Module-Large-Ring =
    zero-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  raise-zero-Large-Left-Module-Large-Ring :
    (l : Level) → type-Large-Left-Module-Large-Ring M l
  raise-zero-Large-Left-Module-Large-Ring =
    raise-zero-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  raise-zero-lzero-Large-Left-Module-Large-Ring :
    raise-zero-Large-Left-Module-Large-Ring lzero ＝
    zero-Large-Left-Module-Large-Ring
  raise-zero-lzero-Large-Left-Module-Large-Ring =
    raise-zero-lzero-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  is-zero-prop-Large-Left-Module-Large-Ring :
    {l : Level} → type-Large-Left-Module-Large-Ring M l → Prop (γ l lzero)
  is-zero-prop-Large-Left-Module-Large-Ring =
    is-zero-prop-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  is-zero-Large-Left-Module-Large-Ring :
    {l : Level} → type-Large-Left-Module-Large-Ring M l → UU (γ l lzero)
  is-zero-Large-Left-Module-Large-Ring x =
    type-Prop (is-zero-prop-Large-Left-Module-Large-Ring x)

  is-zero-zero-Large-Left-Module-Large-Ring :
    is-zero-Large-Left-Module-Large-Ring zero-Large-Left-Module-Large-Ring
  is-zero-zero-Large-Left-Module-Large-Ring =
    is-zero-zero-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  is-zero-raise-zero-Large-Left-Module-Large-Ring :
    (l : Level) →
    is-zero-Large-Left-Module-Large-Ring
      ( raise-zero-Large-Left-Module-Large-Ring l)
  is-zero-raise-zero-Large-Left-Module-Large-Ring =
    is-zero-raise-zero-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  eq-raise-zero-is-zero-Large-Left-Module-Large-Ring :
    {l : Level} (x : type-Large-Left-Module-Large-Ring M l) →
    is-zero-Large-Left-Module-Large-Ring x →
    x ＝ raise-zero-Large-Left-Module-Large-Ring l
  eq-raise-zero-is-zero-Large-Left-Module-Large-Ring =
    eq-raise-zero-is-zero-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  left-unit-law-add-Large-Left-Module-Large-Ring :
    {l : Level} (x : type-Large-Left-Module-Large-Ring M l) →
    add-Large-Left-Module-Large-Ring M zero-Large-Left-Module-Large-Ring x ＝ x
  left-unit-law-add-Large-Left-Module-Large-Ring =
    left-unit-law-add-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  right-unit-law-add-Large-Left-Module-Large-Ring :
    {l : Level} (x : type-Large-Left-Module-Large-Ring M l) →
    add-Large-Left-Module-Large-Ring M x zero-Large-Left-Module-Large-Ring ＝ x
  right-unit-law-add-Large-Left-Module-Large-Ring =
    right-unit-law-add-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  left-raise-unit-law-add-Large-Left-Module-Large-Ring :
    {l1 l2 : Level} (y : type-Large-Left-Module-Large-Ring M l2) →
    add-Large-Left-Module-Large-Ring M
      ( raise-zero-Large-Left-Module-Large-Ring l1)
      ( y) ＝
    raise-Large-Left-Module-Large-Ring M l1 y
  left-raise-unit-law-add-Large-Left-Module-Large-Ring =
    left-raise-unit-law-add-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  right-raise-unit-law-add-Large-Left-Module-Large-Ring :
    {l1 l2 : Level} (x : type-Large-Left-Module-Large-Ring M l1) →
    add-Large-Left-Module-Large-Ring M
      ( x)
      ( raise-zero-Large-Left-Module-Large-Ring l2) ＝
    raise-Large-Left-Module-Large-Ring M l2 x
  right-raise-unit-law-add-Large-Left-Module-Large-Ring =
    right-raise-unit-law-add-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  left-raise-unit-law-add-Large-Left-Module-Large-Ring' :
    {l : Level} (y : type-Large-Left-Module-Large-Ring M l) →
    add-Large-Left-Module-Large-Ring M
      ( raise-zero-Large-Left-Module-Large-Ring l)
      ( y) ＝
    y
  left-raise-unit-law-add-Large-Left-Module-Large-Ring' =
    left-raise-unit-law-add-Large-Ab' (large-ab-Large-Left-Module-Large-Ring M)

  right-raise-unit-law-add-Large-Left-Module-Large-Ring' :
    {l : Level} (x : type-Large-Left-Module-Large-Ring M l) →
    add-Large-Left-Module-Large-Ring M
      ( x)
      ( raise-zero-Large-Left-Module-Large-Ring l) ＝
    x
  right-raise-unit-law-add-Large-Left-Module-Large-Ring' =
    right-raise-unit-law-add-Large-Ab' (large-ab-Large-Left-Module-Large-Ring M)

  eq-left-is-zero-law-add-Large-Left-Module-Large-Ring :
    {l1 l2 : Level}
    (x : type-Large-Left-Module-Large-Ring M l1)
    (y : type-Large-Left-Module-Large-Ring M l2) →
    is-zero-Large-Left-Module-Large-Ring x →
    add-Large-Left-Module-Large-Ring M x y ＝
    raise-Large-Left-Module-Large-Ring M l1 y
  eq-left-is-zero-law-add-Large-Left-Module-Large-Ring =
    eq-left-is-zero-law-add-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  eq-right-is-zero-law-add-Large-Left-Module-Large-Ring :
    {l1 l2 : Level}
    (x : type-Large-Left-Module-Large-Ring M l1)
    (y : type-Large-Left-Module-Large-Ring M l2) →
    is-zero-Large-Left-Module-Large-Ring y →
    add-Large-Left-Module-Large-Ring M x y ＝
    raise-Large-Left-Module-Large-Ring M l2 x
  eq-right-is-zero-law-add-Large-Left-Module-Large-Ring =
    eq-right-is-zero-law-add-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  sim-left-is-zero-law-add-Large-Left-Module-Large-Ring :
    {l1 l2 : Level}
    (x : type-Large-Left-Module-Large-Ring M l1)
    (y : type-Large-Left-Module-Large-Ring M l2) →
    is-zero-Large-Left-Module-Large-Ring x →
    sim-Large-Left-Module-Large-Ring M
      ( add-Large-Left-Module-Large-Ring M x y)
      ( y)
  sim-left-is-zero-law-add-Large-Left-Module-Large-Ring =
    sim-left-is-zero-law-add-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

  sim-right-is-zero-law-add-Large-Left-Module-Large-Ring :
    {l1 l2 : Level}
    (x : type-Large-Left-Module-Large-Ring M l1)
    (y : type-Large-Left-Module-Large-Ring M l2) →
    is-zero-Large-Left-Module-Large-Ring y →
    sim-Large-Left-Module-Large-Ring M
      ( add-Large-Left-Module-Large-Ring M x y)
      ( x)
  sim-right-is-zero-law-add-Large-Left-Module-Large-Ring =
    sim-right-is-zero-law-add-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)
```

### Inverse laws of addition

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  abstract
    sim-left-inverse-law-add-Large-Left-Module-Large-Ring :
      {l : Level} (x : type-Large-Left-Module-Large-Ring M l) →
      is-zero-Large-Left-Module-Large-Ring M
        ( add-Large-Left-Module-Large-Ring M
          ( neg-Large-Left-Module-Large-Ring M x)
          ( x))
    sim-left-inverse-law-add-Large-Left-Module-Large-Ring =
      sim-left-inverse-law-add-Large-Ab
        ( large-ab-Large-Left-Module-Large-Ring M)

    sim-right-inverse-law-add-Large-Left-Module-Large-Ring :
      {l : Level} (x : type-Large-Left-Module-Large-Ring M l) →
      is-zero-Large-Left-Module-Large-Ring M
        ( add-Large-Left-Module-Large-Ring M
          ( x)
          ( neg-Large-Left-Module-Large-Ring M x))
    sim-right-inverse-law-add-Large-Left-Module-Large-Ring =
      sim-right-inverse-law-add-Large-Ab
        ( large-ab-Large-Left-Module-Large-Ring M)

    eq-left-inverse-law-add-Large-Left-Module-Large-Ring :
      {l : Level} (x : type-Large-Left-Module-Large-Ring M l) →
      add-Large-Left-Module-Large-Ring M
        ( neg-Large-Left-Module-Large-Ring M x)
        ( x) ＝
      raise-zero-Large-Left-Module-Large-Ring M l
    eq-left-inverse-law-add-Large-Left-Module-Large-Ring =
      eq-left-inverse-law-add-Large-Ab (large-ab-Large-Left-Module-Large-Ring M)

    eq-right-inverse-law-add-Large-Left-Module-Large-Ring :
      {l : Level} (x : type-Large-Left-Module-Large-Ring M l) →
      add-Large-Left-Module-Large-Ring M
        ( x)
        ( neg-Large-Left-Module-Large-Ring M x) ＝
      raise-zero-Large-Left-Module-Large-Ring M l
    eq-right-inverse-law-add-Large-Left-Module-Large-Ring =
      eq-right-inverse-law-add-Large-Ab
        ( large-ab-Large-Left-Module-Large-Ring M)
```

### Similarity reasoning on large left modules

```agda
module
  similarity-reasoning-Large-Left-Module-Large-Ring
    {α : Level → Level}
    {β : Level → Level → Level}
    {δ : Level → Level}
    {γ : Level → Level → Level}
    {R : Large-Ring α β}
    (M : Large-Left-Module-Large-Ring δ γ R)
  where

  open
    similarity-reasoning-Large-Ab
      ( large-ab-Large-Left-Module-Large-Ring M)
    public
```

### Scalar multiplication preserves similarity

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  abstract
    preserves-sim-mul-Large-Left-Module-Large-Ring :
      preserves-sim-binary-map-Cumulative-Large-Set
        ( cumulative-large-set-Large-Ring R)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( mul-Large-Left-Module-Large-Ring M)
    preserves-sim-mul-Large-Left-Module-Large-Ring =
      preserves-sim-map-sim-preserving-binary-map-Cumulative-Large-Set
        ( cumulative-large-set-Large-Ring R)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( sim-preserving-binary-map-mul-Large-Left-Module-Large-Ring M)

    preserves-sim-left-mul-Large-Left-Module-Large-Ring :
      {l : Level} (r : type-Large-Ring R l) →
      preserves-sim-endomap-Cumulative-Large-Set
        ( l ⊔_)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( mul-Large-Left-Module-Large-Ring M r)
    preserves-sim-left-mul-Large-Left-Module-Large-Ring =
      preserves-sim-map-ev-right-sim-preserving-binary-map-Cumulative-Large-Set
        ( cumulative-large-set-Large-Ring R)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( sim-preserving-binary-map-mul-Large-Left-Module-Large-Ring M)

    preserves-sim-right-mul-Large-Left-Module-Large-Ring :
      {l : Level} (x : type-Large-Left-Module-Large-Ring M l) →
      preserves-sim-map-Cumulative-Large-Set
        ( l ⊔_)
        ( cumulative-large-set-Large-Ring R)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( mul-Large-Left-Module-Large-Ring' M x)
    preserves-sim-right-mul-Large-Left-Module-Large-Ring =
      preserves-sim-map-ev-left-sim-preserving-binary-map-Cumulative-Large-Set
        ( cumulative-large-set-Large-Ring R)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( sim-preserving-binary-map-mul-Large-Left-Module-Large-Ring M)

    mul-raise-left-Large-Left-Module-Large-Ring :
      {l1 l2 : Level} (l3 : Level)
      (r : type-Large-Ring R l1)
      (x : type-Large-Left-Module-Large-Ring M l2) →
      mul-Large-Left-Module-Large-Ring M (raise-Large-Ring R l3 r) x ＝
      raise-Large-Left-Module-Large-Ring M l3
        ( mul-Large-Left-Module-Large-Ring M r x)
    mul-raise-left-Large-Left-Module-Large-Ring =
      map-raise-left-sim-preserving-binary-map-Cumulative-Large-Set
        ( cumulative-large-set-Large-Ring R)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( sim-preserving-binary-map-mul-Large-Left-Module-Large-Ring M)

    mul-raise-right-Large-Left-Module-Large-Ring :
      {l1 l2 : Level} (l3 : Level)
      (r : type-Large-Ring R l1)
      (x : type-Large-Left-Module-Large-Ring M l2) →
      mul-Large-Left-Module-Large-Ring M
        ( r)
        ( raise-Large-Left-Module-Large-Ring M l3 x) ＝
      raise-Large-Left-Module-Large-Ring M l3
        ( mul-Large-Left-Module-Large-Ring M r x)
    mul-raise-right-Large-Left-Module-Large-Ring =
      map-raise-right-sim-preserving-binary-map-Cumulative-Large-Set
        ( cumulative-large-set-Large-Ring R)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( sim-preserving-binary-map-mul-Large-Left-Module-Large-Ring M)

    mul-raise-raise-Large-Left-Module-Large-Ring :
      {l1 l2 : Level} (l3 l4 : Level)
      (r : type-Large-Ring R l1)
      (x : type-Large-Left-Module-Large-Ring M l2) →
      mul-Large-Left-Module-Large-Ring M
        ( raise-Large-Ring R l3 r)
        ( raise-Large-Left-Module-Large-Ring M l4 x) ＝
      raise-Large-Left-Module-Large-Ring M
        ( l3 ⊔ l4)
        ( mul-Large-Left-Module-Large-Ring M r x)
    mul-raise-raise-Large-Left-Module-Large-Ring =
      map-raise-raise-sim-preserving-binary-map-Cumulative-Large-Set
        ( cumulative-large-set-Large-Ring R)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( cumulative-large-set-Large-Left-Module-Large-Ring M)
        ( sim-preserving-binary-map-mul-Large-Left-Module-Large-Ring M)
```

### Left unit laws of scalar multiplication

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  abstract
    sim-left-is-one-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level}
      (r : type-Large-Ring R l1)
      (x : type-Large-Left-Module-Large-Ring M l2) →
      is-one-Large-Ring R r →
      sim-Large-Left-Module-Large-Ring M
        ( mul-Large-Left-Module-Large-Ring M r x)
        ( x)
    sim-left-is-one-law-mul-Large-Left-Module-Large-Ring r x r~1 =
      tr
        ( sim-Large-Left-Module-Large-Ring M _)
        ( left-unit-law-mul-Large-Left-Module-Large-Ring M x)
        ( preserves-sim-right-mul-Large-Left-Module-Large-Ring M x r _ r~1)

    eq-left-is-one-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level}
      (r : type-Large-Ring R l1)
      (x : type-Large-Left-Module-Large-Ring M l2) →
      is-one-Large-Ring R r →
      mul-Large-Left-Module-Large-Ring M r x ＝
      raise-Large-Left-Module-Large-Ring M l1 x
    eq-left-is-one-law-mul-Large-Left-Module-Large-Ring r x r~1 =
      eq-raise-sim-Large-Left-Module-Large-Ring' M
        ( mul-Large-Left-Module-Large-Ring M r x)
        ( x)
        ( sim-left-is-one-law-mul-Large-Left-Module-Large-Ring r x r~1)

    left-raise-one-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level} (x : type-Large-Left-Module-Large-Ring M l2) →
      mul-Large-Left-Module-Large-Ring M (raise-one-Large-Ring R l1) x ＝
      raise-Large-Left-Module-Large-Ring M l1 x
    left-raise-one-law-mul-Large-Left-Module-Large-Ring x =
      eq-left-is-one-law-mul-Large-Left-Module-Large-Ring _ x
        ( is-one-raise-one-Large-Ring R _)

    left-mul-raise-one-leq-level-Large-Left-Module-Large-Ring :
      (l1 : Level) {l2 : Level}
      (x : type-Large-Left-Module-Large-Ring M (l1 ⊔ l2)) →
      mul-Large-Left-Module-Large-Ring M (raise-one-Large-Ring R l2) x ＝
      x
    left-mul-raise-one-leq-level-Large-Left-Module-Large-Ring l1 x =
      ( left-raise-one-law-mul-Large-Left-Module-Large-Ring x) ∙
      ( eq-raise-leq-level-Large-Left-Module-Large-Ring M l1 x)
```

### Zero laws of multiplication

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  (let _+R_ = add-Large-Ring R)
  (let _+M_ = add-Large-Left-Module-Large-Ring M)
  (let _*M_ = mul-Large-Left-Module-Large-Ring M)
  where

  abstract
    sim-left-is-zero-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level}
      (r : type-Large-Ring R l1)
      (x : type-Large-Left-Module-Large-Ring M l2) →
      is-zero-Large-Ring R r →
      is-zero-Large-Left-Module-Large-Ring M
        ( mul-Large-Left-Module-Large-Ring M r x)
    sim-left-is-zero-law-mul-Large-Left-Module-Large-Ring r x r~0 =
      is-zero-is-idempotent-Large-Ab
        ( large-ab-Large-Left-Module-Large-Ring M)
        ( mul-Large-Left-Module-Large-Ring M r x)
        ( equational-reasoning
          (r *M x) +M (r *M x)
          ＝ (r +R r) *M x
            by
              inv
                ( right-distributive-mul-add-Large-Left-Module-Large-Ring M
                  ( r)
                  ( r)
                  ( x))
          ＝ r *M x
            by
              ap
                ( _*M x)
                ( is-idempotent-is-zero-Large-Ab (large-ab-Large-Ring R) r r~0))

    sim-right-is-zero-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level}
      (r : type-Large-Ring R l1)
      (x : type-Large-Left-Module-Large-Ring M l2) →
      is-zero-Large-Left-Module-Large-Ring M x →
      is-zero-Large-Left-Module-Large-Ring M
        ( mul-Large-Left-Module-Large-Ring M r x)
    sim-right-is-zero-law-mul-Large-Left-Module-Large-Ring r x x~0 =
      is-zero-is-idempotent-Large-Ab
        ( large-ab-Large-Left-Module-Large-Ring M)
        ( mul-Large-Left-Module-Large-Ring M r x)
        ( equational-reasoning
          (r *M x) +M (r *M x)
          ＝ r *M (x +M x)
            by
              inv
                ( left-distributive-mul-add-Large-Left-Module-Large-Ring M
                  ( r)
                  ( x)
                  ( x))
          ＝ r *M x
            by
              ap
                ( r *M_)
                ( is-idempotent-is-zero-Large-Ab
                  ( large-ab-Large-Left-Module-Large-Ring M)
                  ( x)
                  ( x~0)))

    eq-left-is-zero-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level}
      (r : type-Large-Ring R l1)
      (x : type-Large-Left-Module-Large-Ring M l2) →
      is-zero-Large-Ring R r →
      mul-Large-Left-Module-Large-Ring M r x ＝
      raise-zero-Large-Left-Module-Large-Ring M (l1 ⊔ l2)
    eq-left-is-zero-law-mul-Large-Left-Module-Large-Ring r x r~0 =
      eq-raise-zero-is-zero-Large-Left-Module-Large-Ring M _
        ( sim-left-is-zero-law-mul-Large-Left-Module-Large-Ring r x r~0)

    eq-right-is-zero-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level}
      (r : type-Large-Ring R l1)
      (x : type-Large-Left-Module-Large-Ring M l2) →
      is-zero-Large-Left-Module-Large-Ring M x →
      mul-Large-Left-Module-Large-Ring M r x ＝
      raise-zero-Large-Left-Module-Large-Ring M (l1 ⊔ l2)
    eq-right-is-zero-law-mul-Large-Left-Module-Large-Ring r x x~0 =
      eq-raise-zero-is-zero-Large-Left-Module-Large-Ring M _
        ( sim-right-is-zero-law-mul-Large-Left-Module-Large-Ring r x x~0)

    left-raise-zero-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level}
      (x : type-Large-Left-Module-Large-Ring M l2) →
      mul-Large-Left-Module-Large-Ring M (raise-zero-Large-Ring R l1) x ＝
      raise-zero-Large-Left-Module-Large-Ring M (l1 ⊔ l2)
    left-raise-zero-law-mul-Large-Left-Module-Large-Ring x =
      eq-left-is-zero-law-mul-Large-Left-Module-Large-Ring
        ( raise-zero-Large-Ring R _)
        ( x)
        ( is-zero-raise-zero-Large-Ring R _)

    right-raise-zero-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level}
      (r : type-Large-Ring R l1) →
      mul-Large-Left-Module-Large-Ring M
        ( r)
        ( raise-zero-Large-Left-Module-Large-Ring M l2) ＝
      raise-zero-Large-Left-Module-Large-Ring M (l1 ⊔ l2)
    right-raise-zero-law-mul-Large-Left-Module-Large-Ring r =
      eq-right-is-zero-law-mul-Large-Left-Module-Large-Ring
        ( r)
        ( raise-zero-Large-Left-Module-Large-Ring M _)
        ( is-zero-raise-zero-Large-Left-Module-Large-Ring M _)
```

### Negative laws of multiplication

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  (let neg-R = neg-Large-Ring R)
  (let neg-M = neg-Large-Left-Module-Large-Ring M)
  (let _+R_ = add-Large-Ring R)
  (let _+M_ = add-Large-Left-Module-Large-Ring M)
  (let _*M_ = mul-Large-Left-Module-Large-Ring M)
  where

  abstract
    left-negative-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level}
      (r : type-Large-Ring R l1)
      (x : type-Large-Left-Module-Large-Ring M l2) →
      mul-Large-Left-Module-Large-Ring M (neg-Large-Ring R r) x ＝
      neg-Large-Left-Module-Large-Ring M
        ( mul-Large-Left-Module-Large-Ring M r x)
    left-negative-law-mul-Large-Left-Module-Large-Ring r x =
      unique-right-inv-Ab
        ( ab-Large-Ab (large-ab-Large-Left-Module-Large-Ring M) _)
        ( equational-reasoning
          (r *M x) +M (neg-R r *M x)
          ＝ (r +R neg-R r) *M x
            by
              inv
                ( right-distributive-mul-add-Large-Left-Module-Large-Ring M
                  ( r)
                  ( neg-R r)
                  ( x))
          ＝ raise-zero-Large-Left-Module-Large-Ring M _
            by
              eq-left-is-zero-law-mul-Large-Left-Module-Large-Ring M
                ( r +R neg-R r)
                ( x)
                ( sim-right-inverse-law-add-Large-Ring R r))

    right-negative-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level}
      (r : type-Large-Ring R l1)
      (x : type-Large-Left-Module-Large-Ring M l2) →
      mul-Large-Left-Module-Large-Ring M
        ( r)
        ( neg-Large-Left-Module-Large-Ring M x) ＝
      neg-Large-Left-Module-Large-Ring M
        ( mul-Large-Left-Module-Large-Ring M r x)
    right-negative-law-mul-Large-Left-Module-Large-Ring r x =
      unique-right-inv-Ab
        ( ab-Large-Ab (large-ab-Large-Left-Module-Large-Ring M) _)
        ( equational-reasoning
          (r *M x) +M (r *M neg-M x)
          ＝ r *M (x +M neg-M x)
            by
              inv
                ( left-distributive-mul-add-Large-Left-Module-Large-Ring M
                  ( r)
                  ( x)
                  ( neg-M x))
          ＝ raise-zero-Large-Left-Module-Large-Ring M _
            by
              eq-right-is-zero-law-mul-Large-Left-Module-Large-Ring M
                ( r)
                ( x +M neg-M x)
                ( sim-right-inverse-law-add-Large-Left-Module-Large-Ring M x))
```

### Multiplication by negative one is negation

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  (let neg-R = neg-Large-Ring R)
  (let neg-M = neg-Large-Left-Module-Large-Ring M)
  (let _+R_ = add-Large-Ring R)
  (let _+M_ = add-Large-Left-Module-Large-Ring M)
  (let _*M_ = mul-Large-Left-Module-Large-Ring M)
  where

  abstract
    neg-one-law-mul-Large-Left-Module-Large-Ring :
      {l : Level} (x : type-Large-Left-Module-Large-Ring M l) →
      mul-Large-Left-Module-Large-Ring M (neg-one-Large-Ring R) x ＝
      neg-Large-Left-Module-Large-Ring M x
    neg-one-law-mul-Large-Left-Module-Large-Ring x =
      ( left-negative-law-mul-Large-Left-Module-Large-Ring M _ x) ∙
      ( ap
        ( neg-Large-Left-Module-Large-Ring M)
        ( left-unit-law-mul-Large-Left-Module-Large-Ring M x))
```

### Any large ring is a large left module over itself

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (R : Large-Ring α β)
  where

  large-left-module-large-ring-Large-Ring :
    Large-Left-Module-Large-Ring α β R
  large-left-module-large-ring-Large-Ring =
    make-Large-Left-Module-Large-Ring
      ( large-ab-Large-Ring R)
      ( sim-preserving-binary-operator-mul-Large-Ring R)
      ( left-distributive-mul-add-Large-Ring R)
      ( right-distributive-mul-add-Large-Ring R)
      ( associative-mul-Large-Ring R)
      ( left-unit-law-mul-Large-Ring R)
```

### Small left modules from large left modules

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  left-module-ring-Large-Left-Module-Large-Ring :
    (l1 l2 : Level) → left-module-Ring (δ (l1 ⊔ l2)) (ring-Large-Ring R l1)
  left-module-ring-Large-Left-Module-Large-Ring l1 l2 =
    make-left-module-Ring
      ( ring-Large-Ring R l1)
      ( ab-Large-Ab (large-ab-Large-Left-Module-Large-Ring M) (l1 ⊔ l2))
      ( mul-Large-Left-Module-Large-Ring M)
      ( left-distributive-mul-add-Large-Left-Module-Large-Ring M)
      ( right-distributive-mul-add-Large-Left-Module-Large-Ring M)
      ( left-mul-raise-one-leq-level-Large-Left-Module-Large-Ring M l2)
      ( associative-mul-Large-Left-Module-Large-Ring M)
```

### The raise operation is a linear map

```agda
module _
  {α δ : Level → Level}
  {β γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  linear-map-raise-Large-Left-Module-Large-Ring :
    (l1 l2 l3 : Level) →
    linear-map-left-module-Ring
      ( ring-Large-Ring R l1)
      ( left-module-ring-Large-Left-Module-Large-Ring M l1 l2)
      ( left-module-ring-Large-Left-Module-Large-Ring M l1 (l2 ⊔ l3))
  linear-map-raise-Large-Left-Module-Large-Ring l1 l2 l3 =
    ( raise-Large-Left-Module-Large-Ring M l3 ,
      ( λ x y →
        inv (add-raise-raise-Large-Left-Module-Large-Ring M l3 l3 x y)) ,
      ( λ r x →
        inv (mul-raise-right-Large-Left-Module-Large-Ring M l3 r x)))
```
