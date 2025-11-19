# Large left modules over rings

```agda
module linear-algebra.large-left-modules-large-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.large-abelian-groups

open import linear-algebra.left-modules-rings

open import ring-theory.large-rings
```

</details>

## Idea

A {{#concept "large left module" Agda=Large-Left-Module-Large-Ring}} over a
[large ring](ring-theory.large-rings.md) `R` is a
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

  field
    large-ab-Large-Left-Module-Large-Ring : Large-Ab δ γ

  type-Large-Left-Module-Large-Ring : (l : Level) → UU (δ l)
  type-Large-Left-Module-Large-Ring =
    type-Large-Ab large-ab-Large-Left-Module-Large-Ring

  set-Large-Left-Module-Large-Ring : (l : Level) → Set (δ l)
  set-Large-Left-Module-Large-Ring =
    set-Large-Ab large-ab-Large-Left-Module-Large-Ring

  add-Large-Left-Module-Large-Ring :
    {l1 l2 : Level} →
    type-Large-Left-Module-Large-Ring l1 →
    type-Large-Left-Module-Large-Ring l2 →
    type-Large-Left-Module-Large-Ring (l1 ⊔ l2)
  add-Large-Left-Module-Large-Ring =
    add-Large-Ab large-ab-Large-Left-Module-Large-Ring

  neg-Large-Left-Module-Large-Ring :
    {l : Level} →
    type-Large-Left-Module-Large-Ring l → type-Large-Left-Module-Large-Ring l
  neg-Large-Left-Module-Large-Ring =
    neg-Large-Ab large-ab-Large-Left-Module-Large-Ring

  diff-Large-Left-Module-Large-Ring :
    {l1 l2 : Level} →
    type-Large-Left-Module-Large-Ring l1 →
    type-Large-Left-Module-Large-Ring l2 →
    type-Large-Left-Module-Large-Ring (l1 ⊔ l2)
  diff-Large-Left-Module-Large-Ring x y =
    add-Large-Left-Module-Large-Ring x (neg-Large-Left-Module-Large-Ring y)

  sim-prop-Large-Left-Module-Large-Ring :
    {l1 l2 : Level} →
    type-Large-Left-Module-Large-Ring l1 →
    type-Large-Left-Module-Large-Ring l2 →
    Prop (γ l1 l2)
  sim-prop-Large-Left-Module-Large-Ring =
    sim-prop-Large-Ab large-ab-Large-Left-Module-Large-Ring

  sim-Large-Left-Module-Large-Ring :
    {l1 l2 : Level} →
    type-Large-Left-Module-Large-Ring l1 →
    type-Large-Left-Module-Large-Ring l2 →
    UU (γ l1 l2)
  sim-Large-Left-Module-Large-Ring =
    sim-Large-Ab large-ab-Large-Left-Module-Large-Ring

  raise-Large-Left-Module-Large-Ring :
    {l0 : Level} (l : Level) →
    type-Large-Left-Module-Large-Ring l0 →
    type-Large-Left-Module-Large-Ring (l0 ⊔ l)
  raise-Large-Left-Module-Large-Ring =
    raise-Large-Ab large-ab-Large-Left-Module-Large-Ring

  zero-Large-Left-Module-Large-Ring : type-Large-Left-Module-Large-Ring lzero
  zero-Large-Left-Module-Large-Ring =
    zero-Large-Ab large-ab-Large-Left-Module-Large-Ring

  raise-zero-Large-Left-Module-Large-Ring :
    (l : Level) → type-Large-Left-Module-Large-Ring l
  raise-zero-Large-Left-Module-Large-Ring =
    raise-zero-Large-Ab large-ab-Large-Left-Module-Large-Ring

  left-unit-law-add-Large-Left-Module-Large-Ring :
    {l : Level} (x : type-Large-Left-Module-Large-Ring l) →
    add-Large-Left-Module-Large-Ring
      ( zero-Large-Left-Module-Large-Ring)
      ( x) ＝
    x
  left-unit-law-add-Large-Left-Module-Large-Ring =
    left-unit-law-add-Large-Ab large-ab-Large-Left-Module-Large-Ring

  right-unit-law-add-Large-Left-Module-Large-Ring :
    {l : Level} (x : type-Large-Left-Module-Large-Ring l) →
    add-Large-Left-Module-Large-Ring
      ( x)
      ( zero-Large-Left-Module-Large-Ring) ＝
    x
  right-unit-law-add-Large-Left-Module-Large-Ring =
    right-unit-law-add-Large-Ab large-ab-Large-Left-Module-Large-Ring

  left-inverse-law-add-Large-Left-Module-Large-Ring :
    {l : Level} (x : type-Large-Left-Module-Large-Ring l) →
    add-Large-Left-Module-Large-Ring (neg-Large-Left-Module-Large-Ring x) x ＝
    raise-zero-Large-Left-Module-Large-Ring l
  left-inverse-law-add-Large-Left-Module-Large-Ring =
    left-inverse-law-add-Large-Ab large-ab-Large-Left-Module-Large-Ring

  right-inverse-law-add-Large-Left-Module-Large-Ring :
    {l : Level} (x : type-Large-Left-Module-Large-Ring l) →
    add-Large-Left-Module-Large-Ring x (neg-Large-Left-Module-Large-Ring x) ＝
    raise-zero-Large-Left-Module-Large-Ring l
  right-inverse-law-add-Large-Left-Module-Large-Ring =
    right-inverse-law-add-Large-Ab large-ab-Large-Left-Module-Large-Ring

  commutative-add-Large-Left-Module-Large-Ring :
    {l1 l2 : Level} →
    (x : type-Large-Left-Module-Large-Ring l1) →
    (y : type-Large-Left-Module-Large-Ring l2) →
    add-Large-Left-Module-Large-Ring x y ＝
    add-Large-Left-Module-Large-Ring y x
  commutative-add-Large-Left-Module-Large-Ring =
    commutative-add-Large-Ab large-ab-Large-Left-Module-Large-Ring

  unique-right-neg-Large-Left-Module-Large-Ring :
    {l1 l2 : Level} →
    (x : type-Large-Left-Module-Large-Ring l1) →
    (y : type-Large-Left-Module-Large-Ring l2) →
    ( add-Large-Left-Module-Large-Ring x y ＝
      raise-zero-Large-Left-Module-Large-Ring (l1 ⊔ l2)) →
    sim-Large-Left-Module-Large-Ring
      ( y)
      ( neg-Large-Left-Module-Large-Ring x)
  unique-right-neg-Large-Left-Module-Large-Ring =
    unique-right-neg-Large-Ab large-ab-Large-Left-Module-Large-Ring

  refl-sim-Large-Left-Module-Large-Ring :
    {l : Level} (x : type-Large-Left-Module-Large-Ring l) →
    sim-Large-Left-Module-Large-Ring x x
  refl-sim-Large-Left-Module-Large-Ring =
    refl-sim-Large-Ab large-ab-Large-Left-Module-Large-Ring

  eq-sim-Large-Left-Module-Large-Ring :
    {l : Level} {x y : type-Large-Left-Module-Large-Ring l} →
    sim-Large-Left-Module-Large-Ring x y → x ＝ y
  eq-sim-Large-Left-Module-Large-Ring =
    eq-sim-Large-Ab large-ab-Large-Left-Module-Large-Ring

  sim-eq-Large-Left-Module-Large-Ring :
    {l : Level} {x y : type-Large-Left-Module-Large-Ring l} →
    x ＝ y → sim-Large-Left-Module-Large-Ring x y
  sim-eq-Large-Left-Module-Large-Ring =
    sim-eq-Large-Ab large-ab-Large-Left-Module-Large-Ring

  sim-raise-Large-Left-Module-Large-Ring :
    {l0 : Level} (l : Level) (x : type-Large-Left-Module-Large-Ring l0) →
    sim-Large-Left-Module-Large-Ring x (raise-Large-Left-Module-Large-Ring l x)
  sim-raise-Large-Left-Module-Large-Ring =
    sim-raise-Large-Ab large-ab-Large-Left-Module-Large-Ring

  sim-raise-Large-Left-Module-Large-Ring' :
    {l0 : Level} (l : Level) (x : type-Large-Left-Module-Large-Ring l0) →
    sim-Large-Left-Module-Large-Ring (raise-Large-Left-Module-Large-Ring l x) x
  sim-raise-Large-Left-Module-Large-Ring' =
    sim-raise-Large-Ab' large-ab-Large-Left-Module-Large-Ring

  raise-raise-Large-Left-Module-Large-Ring :
    {l1 l2 l3 : Level} →
    (x : type-Large-Left-Module-Large-Ring l1) →
    raise-Large-Left-Module-Large-Ring
      ( l2)
      ( raise-Large-Left-Module-Large-Ring l3 x) ＝
    raise-Large-Left-Module-Large-Ring (l2 ⊔ l3) x
  raise-raise-Large-Left-Module-Large-Ring =
    raise-raise-Large-Ab large-ab-Large-Left-Module-Large-Ring

  eq-raise-Large-Left-Module-Large-Ring :
    (l1 : Level) {l2 : Level} →
    (x : type-Large-Left-Module-Large-Ring (l1 ⊔ l2)) →
    raise-Large-Left-Module-Large-Ring l2 x ＝ x
  eq-raise-Large-Left-Module-Large-Ring =
    eq-raise-Large-Ab large-ab-Large-Left-Module-Large-Ring

  field
    mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level} →
      type-Large-Ring R l1 →
      type-Large-Left-Module-Large-Ring l2 →
      type-Large-Left-Module-Large-Ring (l1 ⊔ l2)

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

    preserves-sim-mul-Large-Left-Module-Ring :
      {l1 l2 l3 l4 : Level} →
      {a : type-Large-Ring R l1} {b : type-Large-Ring R l2} →
      sim-Large-Ring R a b →
      {x : type-Large-Left-Module-Large-Ring l3} →
      {y : type-Large-Left-Module-Large-Ring l4} →
      sim-Large-Left-Module-Large-Ring x y →
      sim-Large-Left-Module-Large-Ring
        ( mul-Large-Left-Module-Large-Ring a x)
        ( mul-Large-Left-Module-Large-Ring b y)

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

### The raised left unit law

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {δ : Level → Level}
  {γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  abstract
    left-raise-unit-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level} (x : type-Large-Left-Module-Large-Ring M l2) →
      mul-Large-Left-Module-Large-Ring M (raise-one-Large-Ring R l1) x ＝
      raise-Large-Left-Module-Large-Ring M l1 x
    left-raise-unit-law-mul-Large-Left-Module-Large-Ring {l1} {l2} x =
      let
        open similarity-reasoning-Large-Left-Module-Large-Ring M
      in
        eq-sim-Large-Left-Module-Large-Ring M
          ( similarity-reasoning
            mul-Large-Left-Module-Large-Ring M (raise-one-Large-Ring R l1) x
            ~ mul-Large-Left-Module-Large-Ring M (one-Large-Ring R) x
              by
                preserves-sim-mul-Large-Left-Module-Ring M
                  ( sim-raise-Large-Ring' R _ _)
                  ( refl-sim-Large-Left-Module-Large-Ring M x)
            ~ x
              by
                sim-eq-Large-Left-Module-Large-Ring M
                  ( left-unit-law-mul-Large-Left-Module-Large-Ring M x)
            ~ raise-Large-Left-Module-Large-Ring M l1 x
              by sim-raise-Large-Left-Module-Large-Ring M l1 x)
```

### Zero laws of multiplication

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {δ : Level → Level}
  {γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  abstract
    left-zero-law-mul-Large-Left-Module-Large-Ring :
      {l : Level} →
      (x : type-Large-Left-Module-Large-Ring M l) →
      mul-Large-Left-Module-Large-Ring M (zero-Large-Ring R) x ＝
      raise-zero-Large-Left-Module-Large-Ring M l
    left-zero-law-mul-Large-Left-Module-Large-Ring x =
      eq-zero-is-idempotent-add-Large-Ab
        ( large-ab-Large-Left-Module-Large-Ring M)
        ( _)
        ( equational-reasoning
          add-Large-Left-Module-Large-Ring M
            ( mul-Large-Left-Module-Large-Ring M (zero-Large-Ring R) x)
            ( mul-Large-Left-Module-Large-Ring M (zero-Large-Ring R) x)
          ＝
            mul-Large-Left-Module-Large-Ring M
              ( add-Large-Ring R (zero-Large-Ring R) (zero-Large-Ring R))
              ( x)
            by
              inv
                ( right-distributive-mul-add-Large-Left-Module-Large-Ring M
                  ( _)
                  ( _)
                  ( _))
          ＝ mul-Large-Left-Module-Large-Ring M (zero-Large-Ring R) x
            by
              ap-mul-Large-Left-Module-Large-Ring M
                ( left-unit-law-add-Large-Ring R _)
                ( refl))

    left-raise-zero-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level} →
      (x : type-Large-Left-Module-Large-Ring M l2) →
      mul-Large-Left-Module-Large-Ring M (raise-zero-Large-Ring R l1) x ＝
      raise-zero-Large-Left-Module-Large-Ring M (l1 ⊔ l2)
    left-raise-zero-law-mul-Large-Left-Module-Large-Ring {l1} {l2} x =
      let
        open similarity-reasoning-Large-Left-Module-Large-Ring M
      in
        eq-sim-Large-Left-Module-Large-Ring M
          ( similarity-reasoning
            mul-Large-Left-Module-Large-Ring M (raise-zero-Large-Ring R l1) x
            ~ mul-Large-Left-Module-Large-Ring M (zero-Large-Ring R) x
              by
                preserves-sim-mul-Large-Left-Module-Ring M
                  ( sim-raise-Large-Ring' R _ _)
                  ( refl-sim-Large-Left-Module-Large-Ring M x)
            ~ raise-zero-Large-Left-Module-Large-Ring M l2
              by
                sim-eq-Large-Left-Module-Large-Ring M
                  ( left-zero-law-mul-Large-Left-Module-Large-Ring x)
            ~ raise-Large-Left-Module-Large-Ring M
                ( l1)
                ( raise-zero-Large-Left-Module-Large-Ring M l2)
              by sim-raise-Large-Left-Module-Large-Ring M _ _
            ~ raise-zero-Large-Left-Module-Large-Ring M (l1 ⊔ l2)
              by
                sim-eq-Large-Left-Module-Large-Ring M
                  ( raise-raise-Large-Left-Module-Large-Ring M _))

    right-zero-law-mul-Large-Left-Module-Large-Ring :
      {l : Level} →
      (a : type-Large-Ring R l) →
      mul-Large-Left-Module-Large-Ring M
        ( a)
        ( zero-Large-Left-Module-Large-Ring M) ＝
      raise-zero-Large-Left-Module-Large-Ring M l
    right-zero-law-mul-Large-Left-Module-Large-Ring a =
      eq-zero-is-idempotent-add-Large-Ab
        ( large-ab-Large-Left-Module-Large-Ring M)
        ( _)
        ( equational-reasoning
          add-Large-Left-Module-Large-Ring M
            ( mul-Large-Left-Module-Large-Ring M
              ( a)
              ( zero-Large-Left-Module-Large-Ring M))
            ( mul-Large-Left-Module-Large-Ring M
              ( a)
              ( zero-Large-Left-Module-Large-Ring M))
          ＝
            mul-Large-Left-Module-Large-Ring M
              ( a)
              ( add-Large-Left-Module-Large-Ring M
                ( zero-Large-Left-Module-Large-Ring M)
                ( zero-Large-Left-Module-Large-Ring M))
            by
              inv
                ( left-distributive-mul-add-Large-Left-Module-Large-Ring M
                  ( _)
                  ( _)
                  ( _))
          ＝
            mul-Large-Left-Module-Large-Ring M
              ( a)
              ( zero-Large-Left-Module-Large-Ring M)
            by
              ap-mul-Large-Left-Module-Large-Ring M
                ( refl)
                ( left-unit-law-add-Large-Left-Module-Large-Ring M _))

    right-raise-zero-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level} →
      (a : type-Large-Ring R l1) →
      mul-Large-Left-Module-Large-Ring M
        ( a)
        ( raise-zero-Large-Left-Module-Large-Ring M l2) ＝
      raise-zero-Large-Left-Module-Large-Ring M (l1 ⊔ l2)
    right-raise-zero-law-mul-Large-Left-Module-Large-Ring {l1} {l2} a =
      let
        open similarity-reasoning-Large-Left-Module-Large-Ring M
      in
        eq-sim-Large-Left-Module-Large-Ring M
          ( similarity-reasoning
            mul-Large-Left-Module-Large-Ring M
              ( a)
              ( raise-zero-Large-Left-Module-Large-Ring M l2)
            ~ mul-Large-Left-Module-Large-Ring M
                ( a)
                ( zero-Large-Left-Module-Large-Ring M)
              by
                preserves-sim-mul-Large-Left-Module-Ring M
                  ( refl-sim-Large-Ring R a)
                  ( sim-raise-Large-Left-Module-Large-Ring' M _ _)
            ~ raise-zero-Large-Left-Module-Large-Ring M l1
              by
                sim-eq-Large-Left-Module-Large-Ring M
                  ( right-zero-law-mul-Large-Left-Module-Large-Ring a)
            ~ raise-Large-Left-Module-Large-Ring M l2
                ( raise-zero-Large-Left-Module-Large-Ring M l1)
              by sim-raise-Large-Left-Module-Large-Ring M _ _
            ~ raise-zero-Large-Left-Module-Large-Ring M (l1 ⊔ l2)
              by
                sim-eq-Large-Left-Module-Large-Ring M
                  ( raise-raise-Large-Left-Module-Large-Ring M _))
```

### Negative laws of multiplication

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {δ : Level → Level}
  {γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  abstract
    left-negative-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level} →
      (a : type-Large-Ring R l1) →
      (x : type-Large-Left-Module-Large-Ring M l2) →
      mul-Large-Left-Module-Large-Ring M (neg-Large-Ring R a) x ＝
      neg-Large-Left-Module-Large-Ring M
        ( mul-Large-Left-Module-Large-Ring M a x)
    left-negative-law-mul-Large-Left-Module-Large-Ring {l1} {l2} a x =
      eq-sim-Large-Left-Module-Large-Ring M
        ( unique-right-neg-Large-Left-Module-Large-Ring M _ _
          ( equational-reasoning
            add-Large-Left-Module-Large-Ring M
              ( mul-Large-Left-Module-Large-Ring M a x)
              ( mul-Large-Left-Module-Large-Ring M (neg-Large-Ring R a) x)
            ＝
              mul-Large-Left-Module-Large-Ring M
                ( add-Large-Ring R a (neg-Large-Ring R a))
                ( x)
              by
                inv
                  ( right-distributive-mul-add-Large-Left-Module-Large-Ring M
                    ( _)
                    ( _)
                    ( _))
            ＝
              mul-Large-Left-Module-Large-Ring M
                ( raise-zero-Large-Ring R l1)
                ( x)
              by
                ap-mul-Large-Left-Module-Large-Ring M
                  ( right-inverse-law-add-Large-Ring R a)
                  ( refl)
            ＝ raise-zero-Large-Left-Module-Large-Ring M (l1 ⊔ l2)
              by left-raise-zero-law-mul-Large-Left-Module-Large-Ring M _))

    right-negative-law-mul-Large-Left-Module-Large-Ring :
      {l1 l2 : Level} →
      (a : type-Large-Ring R l1) →
      (x : type-Large-Left-Module-Large-Ring M l2) →
      mul-Large-Left-Module-Large-Ring M
        ( a)
        ( neg-Large-Left-Module-Large-Ring M x) ＝
      neg-Large-Left-Module-Large-Ring M
        ( mul-Large-Left-Module-Large-Ring M a x)
    right-negative-law-mul-Large-Left-Module-Large-Ring {l1} {l2} a x =
      eq-sim-Large-Left-Module-Large-Ring M
        ( unique-right-neg-Large-Left-Module-Large-Ring M _ _
          ( equational-reasoning
            add-Large-Left-Module-Large-Ring M
              ( mul-Large-Left-Module-Large-Ring M a x)
              ( mul-Large-Left-Module-Large-Ring M a
                ( neg-Large-Left-Module-Large-Ring M x))
            ＝
              mul-Large-Left-Module-Large-Ring M
                ( a)
                ( add-Large-Left-Module-Large-Ring M
                  ( x)
                  ( neg-Large-Left-Module-Large-Ring M x))
              by
                inv
                  ( left-distributive-mul-add-Large-Left-Module-Large-Ring M
                    ( _)
                    ( _)
                    ( _))
            ＝
              mul-Large-Left-Module-Large-Ring M
                ( a)
                ( raise-zero-Large-Left-Module-Large-Ring M l2)
              by
                ap-mul-Large-Left-Module-Large-Ring M
                  ( refl)
                  ( right-inverse-law-add-Large-Left-Module-Large-Ring M x)
            ＝ raise-zero-Large-Left-Module-Large-Ring M (l1 ⊔ l2)
              by right-raise-zero-law-mul-Large-Left-Module-Large-Ring M a))
```

### Multiplication by negative one is negation

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {δ : Level → Level}
  {γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  abstract
    mul-neg-one-Large-Left-Module-Large-Ring :
      {l : Level} →
      (x : type-Large-Left-Module-Large-Ring M l) →
      mul-Large-Left-Module-Large-Ring M
        ( neg-Large-Ring R (one-Large-Ring R))
        ( x) ＝
      neg-Large-Left-Module-Large-Ring M x
    mul-neg-one-Large-Left-Module-Large-Ring x =
      equational-reasoning
        mul-Large-Left-Module-Large-Ring M
          ( neg-Large-Ring R (one-Large-Ring R))
          ( x)
        ＝ neg-Large-Left-Module-Large-Ring M
            ( mul-Large-Left-Module-Large-Ring M (one-Large-Ring R) x)
          by left-negative-law-mul-Large-Left-Module-Large-Ring M _ _
        ＝ neg-Large-Left-Module-Large-Ring M x
          by
            ap
              ( neg-Large-Left-Module-Large-Ring M)
              ( left-unit-law-mul-Large-Left-Module-Large-Ring M x)
```

## Properties

### Small left modules from large left modules

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {δ : Level → Level}
  {γ : Level → Level → Level}
  {R : Large-Ring α β}
  (M : Large-Left-Module-Large-Ring δ γ R)
  where

  left-module-ring-Large-Left-Module-Large-Ring :
    (l1 l2 : Level) →
    left-module-Ring
      ( δ (l1 ⊔ l2))
      ( ring-Large-Ring R l1)
  left-module-ring-Large-Left-Module-Large-Ring l1 l2 =
    let
      open similarity-reasoning-Large-Left-Module-Large-Ring M
    in
      make-left-module-Ring
        ( ring-Large-Ring R l1)
        ( ab-Large-Ab (large-ab-Large-Left-Module-Large-Ring M) (l1 ⊔ l2))
        ( mul-Large-Left-Module-Large-Ring M)
        ( left-distributive-mul-add-Large-Left-Module-Large-Ring M)
        ( right-distributive-mul-add-Large-Left-Module-Large-Ring M)
        ( λ x →
          ( left-raise-unit-law-mul-Large-Left-Module-Large-Ring M x) ∙
          ( eq-raise-Large-Left-Module-Large-Ring M l2 x))
        ( associative-mul-Large-Left-Module-Large-Ring M)
```
