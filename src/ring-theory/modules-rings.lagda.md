# Modules over rings

```agda
module ring-theory.modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.addition-homomorphisms-abelian-groups
open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.homomorphisms-abelian-groups

open import ring-theory.homomorphisms-rings
open import ring-theory.opposite-rings
open import ring-theory.rings
```

</details>

## Idea

A (left) module `M` over a ring `R` consists of an abelian group `M` equipped
with an action `R → M → M` such

```text
  r(x+y) = rx + ry
      r0 = 0
   r(-x) = -(rx)
  (r+s)x = rx + sx
      0x = 0
   (-r)x = -(rx)
   (sr)x = s(rx)
      1x = x
```

In other words, a left module `M` over a ring `R` consists of an abelian group
`M` equipped with a ring homomorphism `R → endomorphism-ring-Ab M`. A right
module over `R` consists of an abelian group `M` equipped with a ring
homomorphism `R → opposite-Ring (endomorphism-ring-Ab M)`.

## Definitions

### Left modules over rings

```agda
left-module-Ring :
  {l1 : Level} (l2 : Level) (R : Ring l1) → UU (l1 ⊔ lsuc l2)
left-module-Ring l2 R =
  Σ (Ab l2) (λ A → hom-Ring R (endomorphism-ring-Ab A))

module _
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R)
  where

  ab-left-module-Ring : Ab l2
  ab-left-module-Ring = pr1 M

  set-left-module-Ring : Set l2
  set-left-module-Ring = set-Ab ab-left-module-Ring

  type-left-module-Ring : UU l2
  type-left-module-Ring = type-Ab ab-left-module-Ring

  add-left-module-Ring :
    (x y : type-left-module-Ring) → type-left-module-Ring
  add-left-module-Ring = add-Ab ab-left-module-Ring

  zero-left-module-Ring : type-left-module-Ring
  zero-left-module-Ring = zero-Ab ab-left-module-Ring

  is-zero-prop-left-module-Ring : type-left-module-Ring → Prop l2
  is-zero-prop-left-module-Ring = is-zero-prop-Ab ab-left-module-Ring

  is-zero-left-module-Ring : type-left-module-Ring → UU l2
  is-zero-left-module-Ring = is-zero-Ab ab-left-module-Ring

  neg-left-module-Ring : type-left-module-Ring → type-left-module-Ring
  neg-left-module-Ring = neg-Ab ab-left-module-Ring

  associative-add-left-module-Ring :
    (x y z : type-left-module-Ring) →
    Id
      ( add-left-module-Ring (add-left-module-Ring x y) z)
      ( add-left-module-Ring x (add-left-module-Ring y z))
  associative-add-left-module-Ring =
    associative-add-Ab ab-left-module-Ring

  left-unit-law-add-left-module-Ring :
    (x : type-left-module-Ring) →
    Id (add-left-module-Ring zero-left-module-Ring x) x
  left-unit-law-add-left-module-Ring =
    left-unit-law-add-Ab ab-left-module-Ring

  right-unit-law-add-left-module-Ring :
    (x : type-left-module-Ring) →
    Id (add-left-module-Ring x zero-left-module-Ring) x
  right-unit-law-add-left-module-Ring =
    right-unit-law-add-Ab ab-left-module-Ring

  left-inverse-law-add-left-module-Ring :
    (x : type-left-module-Ring) →
    Id
      ( add-left-module-Ring (neg-left-module-Ring x) x)
      ( zero-left-module-Ring)
  left-inverse-law-add-left-module-Ring =
    left-inverse-law-add-Ab ab-left-module-Ring

  right-inverse-law-add-left-module-Ring :
    (x : type-left-module-Ring) →
    Id
      ( add-left-module-Ring x (neg-left-module-Ring x))
      ( zero-left-module-Ring)
  right-inverse-law-add-left-module-Ring =
    right-inverse-law-add-Ab ab-left-module-Ring

  endomorphism-ring-ab-left-module-Ring : Ring l2
  endomorphism-ring-ab-left-module-Ring =
    endomorphism-ring-Ab ab-left-module-Ring

  mul-hom-left-module-Ring :
    hom-Ring R endomorphism-ring-ab-left-module-Ring
  mul-hom-left-module-Ring = pr2 M

  mul-left-module-Ring :
    type-Ring R → type-left-module-Ring → type-left-module-Ring
  mul-left-module-Ring x =
    map-hom-Ab
      ( ab-left-module-Ring)
      ( ab-left-module-Ring)
      ( map-hom-Ring R
        ( endomorphism-ring-Ab ab-left-module-Ring)
        ( mul-hom-left-module-Ring)
        ( x))

  abstract
    left-unit-law-mul-left-module-Ring :
      (x : type-left-module-Ring) →
      Id ( mul-left-module-Ring (one-Ring R) x) x
    left-unit-law-mul-left-module-Ring =
      htpy-eq-hom-Ab
        ( ab-left-module-Ring)
        ( ab-left-module-Ring)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring)
          ( mul-hom-left-module-Ring)
          ( one-Ring R))
        ( id-hom-Ab ab-left-module-Ring)
        ( preserves-one-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring)
          ( mul-hom-left-module-Ring))

    left-distributive-mul-add-left-module-Ring :
      (r : type-Ring R) (x y : type-left-module-Ring) →
      Id
        ( mul-left-module-Ring r (add-left-module-Ring x y))
        ( add-left-module-Ring
          ( mul-left-module-Ring r x)
          ( mul-left-module-Ring r y))
    left-distributive-mul-add-left-module-Ring r x y =
      preserves-add-hom-Ab
        ( ab-left-module-Ring)
        ( ab-left-module-Ring)
        ( map-hom-Ring R
            endomorphism-ring-ab-left-module-Ring
            mul-hom-left-module-Ring
            r)

    right-distributive-mul-add-left-module-Ring :
      (r s : type-Ring R) (x : type-left-module-Ring) →
      Id
        ( mul-left-module-Ring (add-Ring R r s) x)
        ( add-left-module-Ring
          ( mul-left-module-Ring r x)
          ( mul-left-module-Ring s x))
    right-distributive-mul-add-left-module-Ring r s =
      htpy-eq-hom-Ab
        ( ab-left-module-Ring)
        ( ab-left-module-Ring)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring)
          ( mul-hom-left-module-Ring)
          ( add-Ring R r s))
        ( add-hom-Ab
          ( ab-left-module-Ring)
          ( ab-left-module-Ring)
          ( map-hom-Ring R
            ( endomorphism-ring-ab-left-module-Ring)
            ( mul-hom-left-module-Ring)
            ( r))
          ( map-hom-Ring R
            ( endomorphism-ring-ab-left-module-Ring)
            ( mul-hom-left-module-Ring)
            ( s)))
        ( preserves-add-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring)
          ( mul-hom-left-module-Ring))

    associative-mul-left-module-Ring :
      (r s : type-Ring R) (x : type-left-module-Ring) →
      Id
        ( mul-left-module-Ring (mul-Ring R r s) x)
        ( mul-left-module-Ring r (mul-left-module-Ring s x))
    associative-mul-left-module-Ring r s =
      htpy-eq-hom-Ab
        ( ab-left-module-Ring)
        ( ab-left-module-Ring)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring)
          ( mul-hom-left-module-Ring)
          ( mul-Ring R r s))
        ( comp-hom-Ab
          ( ab-left-module-Ring)
          ( ab-left-module-Ring)
          ( ab-left-module-Ring)
          ( map-hom-Ring R
            ( endomorphism-ring-ab-left-module-Ring)
            ( mul-hom-left-module-Ring)
            ( r))
          ( map-hom-Ring R
            ( endomorphism-ring-ab-left-module-Ring)
            ( mul-hom-left-module-Ring)
            ( s)))
        ( preserves-mul-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring)
          ( mul-hom-left-module-Ring))

    left-zero-law-mul-left-module-Ring :
      (x : type-left-module-Ring) →
      Id ( mul-left-module-Ring (zero-Ring R) x) zero-left-module-Ring
    left-zero-law-mul-left-module-Ring =
      htpy-eq-hom-Ab
        ( ab-left-module-Ring)
        ( ab-left-module-Ring)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring)
          ( mul-hom-left-module-Ring)
          ( zero-Ring R))
        ( zero-hom-Ab ab-left-module-Ring ab-left-module-Ring)
        ( preserves-zero-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring)
          ( mul-hom-left-module-Ring))

    right-zero-law-mul-left-module-Ring :
      (r : type-Ring R) →
      Id ( mul-left-module-Ring r zero-left-module-Ring) zero-left-module-Ring
    right-zero-law-mul-left-module-Ring r =
      preserves-zero-hom-Ab
        ( ab-left-module-Ring)
        ( ab-left-module-Ring)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring)
          ( mul-hom-left-module-Ring)
          ( r))

    left-negative-law-mul-left-module-Ring :
      (r : type-Ring R) (x : type-left-module-Ring) →
      Id
        ( mul-left-module-Ring (neg-Ring R r) x)
        ( neg-left-module-Ring (mul-left-module-Ring r x))
    left-negative-law-mul-left-module-Ring r =
      htpy-eq-hom-Ab
        ( ab-left-module-Ring)
        ( ab-left-module-Ring)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring)
          ( mul-hom-left-module-Ring)
          ( neg-Ring R r))
        ( neg-hom-Ab
          ( ab-left-module-Ring)
          ( ab-left-module-Ring)
          ( map-hom-Ring R
            ( endomorphism-ring-ab-left-module-Ring)
            ( mul-hom-left-module-Ring)
            ( r)))
        ( preserves-neg-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring)
          ( mul-hom-left-module-Ring))

    right-negative-law-mul-left-module-Ring :
      (r : type-Ring R) (x : type-left-module-Ring) →
      Id
        ( mul-left-module-Ring r (neg-left-module-Ring x))
        ( neg-left-module-Ring (mul-left-module-Ring r x))
    right-negative-law-mul-left-module-Ring r x =
      preserves-negatives-hom-Ab
        ( ab-left-module-Ring)
        ( ab-left-module-Ring)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring)
          ( mul-hom-left-module-Ring)
          ( r))
```

### Right modules over rings

```agda
right-module-Ring :
  {l1 : Level} (l2 : Level) (R : Ring l1) → UU (l1 ⊔ lsuc l2)
right-module-Ring l2 R =
  Σ (Ab l2) (λ A → hom-Ring R (op-Ring (endomorphism-ring-Ab A)))

module _
  {l1 l2 : Level} (R : Ring l1) (M : right-module-Ring l2 R)
  where

  ab-right-module-Ring : Ab l2
  ab-right-module-Ring = pr1 M

  set-right-module-Ring : Set l2
  set-right-module-Ring = set-Ab ab-right-module-Ring

  type-right-module-Ring : UU l2
  type-right-module-Ring = type-Ab ab-right-module-Ring

  add-right-module-Ring :
    (x y : type-right-module-Ring) → type-right-module-Ring
  add-right-module-Ring = add-Ab ab-right-module-Ring

  zero-right-module-Ring : type-right-module-Ring
  zero-right-module-Ring = zero-Ab ab-right-module-Ring

  neg-right-module-Ring : type-right-module-Ring → type-right-module-Ring
  neg-right-module-Ring = neg-Ab ab-right-module-Ring

  associative-add-right-module-Ring :
    (x y z : type-right-module-Ring) →
    Id
      ( add-right-module-Ring (add-right-module-Ring x y) z)
      ( add-right-module-Ring x (add-right-module-Ring y z))
  associative-add-right-module-Ring =
    associative-add-Ab ab-right-module-Ring

  left-unit-law-add-right-module-Ring :
    (x : type-right-module-Ring) →
    Id (add-right-module-Ring zero-right-module-Ring x) x
  left-unit-law-add-right-module-Ring =
    left-unit-law-add-Ab ab-right-module-Ring

  right-unit-law-add-right-module-Ring :
    (x : type-right-module-Ring) →
    Id (add-right-module-Ring x zero-right-module-Ring) x
  right-unit-law-add-right-module-Ring =
    right-unit-law-add-Ab ab-right-module-Ring

  left-inverse-law-add-right-module-Ring :
    (x : type-right-module-Ring) →
    Id
      ( add-right-module-Ring (neg-right-module-Ring x) x)
      ( zero-right-module-Ring)
  left-inverse-law-add-right-module-Ring =
    left-inverse-law-add-Ab ab-right-module-Ring

  right-inverse-law-add-right-module-Ring :
    (x : type-right-module-Ring) →
    Id
      ( add-right-module-Ring x (neg-right-module-Ring x))
      ( zero-right-module-Ring)
  right-inverse-law-add-right-module-Ring =
    right-inverse-law-add-Ab ab-right-module-Ring

  endomorphism-ring-ab-right-module-Ring : Ring l2
  endomorphism-ring-ab-right-module-Ring =
    endomorphism-ring-Ab ab-right-module-Ring

  mul-hom-right-module-Ring :
    hom-Ring R (op-Ring endomorphism-ring-ab-right-module-Ring)
  mul-hom-right-module-Ring = pr2 M

  mul-right-module-Ring :
    type-Ring R → type-right-module-Ring → type-right-module-Ring
  mul-right-module-Ring x =
    map-hom-Ab
      ( ab-right-module-Ring)
      ( ab-right-module-Ring)
      ( map-hom-Ring R
        ( op-Ring endomorphism-ring-ab-right-module-Ring)
        ( mul-hom-right-module-Ring)
        ( x))

  left-unit-law-mul-right-module-Ring :
    (x : type-right-module-Ring) →
    Id ( mul-right-module-Ring (one-Ring R) x) x
  left-unit-law-mul-right-module-Ring =
    htpy-eq-hom-Ab
      ( ab-right-module-Ring)
      ( ab-right-module-Ring)
      ( map-hom-Ring R
        ( op-Ring endomorphism-ring-ab-right-module-Ring)
        ( mul-hom-right-module-Ring)
        ( one-Ring R))
      ( id-hom-Ab ab-right-module-Ring)
      ( preserves-one-hom-Ring R
        ( op-Ring endomorphism-ring-ab-right-module-Ring)
        ( mul-hom-right-module-Ring))

  left-distributive-mul-add-right-module-Ring :
    (r : type-Ring R) (x y : type-right-module-Ring) →
    Id
      ( mul-right-module-Ring r (add-right-module-Ring x y))
      ( add-right-module-Ring
        ( mul-right-module-Ring r x)
        ( mul-right-module-Ring r y))
  left-distributive-mul-add-right-module-Ring r x y =
    preserves-add-hom-Ab
      ( ab-right-module-Ring)
      ( ab-right-module-Ring)
      ( map-hom-Ring R
        ( op-Ring endomorphism-ring-ab-right-module-Ring)
        ( mul-hom-right-module-Ring)
        ( r))

  right-distributive-mul-add-right-module-Ring :
    (r s : type-Ring R) (x : type-right-module-Ring) →
    Id
      ( mul-right-module-Ring (add-Ring R r s) x)
      ( add-right-module-Ring
        ( mul-right-module-Ring r x)
        ( mul-right-module-Ring s x))
  right-distributive-mul-add-right-module-Ring r s =
    htpy-eq-hom-Ab
      ( ab-right-module-Ring)
      ( ab-right-module-Ring)
      ( map-hom-Ring R
        ( op-Ring endomorphism-ring-ab-right-module-Ring)
        ( mul-hom-right-module-Ring)
        ( add-Ring R r s))
      ( add-hom-Ab
        ( ab-right-module-Ring)
        ( ab-right-module-Ring)
        ( map-hom-Ring R
          ( op-Ring endomorphism-ring-ab-right-module-Ring)
          ( mul-hom-right-module-Ring)
          ( r))
        ( map-hom-Ring R
          ( op-Ring endomorphism-ring-ab-right-module-Ring)
          ( mul-hom-right-module-Ring)
          ( s)))
      ( preserves-add-hom-Ring R
        ( op-Ring endomorphism-ring-ab-right-module-Ring)
        ( mul-hom-right-module-Ring))

  associative-mul-right-module-Ring :
    (r s : type-Ring R) (x : type-right-module-Ring) →
    Id
      ( mul-right-module-Ring (mul-Ring R r s) x)
      ( mul-right-module-Ring s (mul-right-module-Ring r x))
  associative-mul-right-module-Ring r s =
    htpy-eq-hom-Ab
      ( ab-right-module-Ring)
      ( ab-right-module-Ring)
      ( map-hom-Ring R
        ( op-Ring endomorphism-ring-ab-right-module-Ring)
        ( mul-hom-right-module-Ring)
        ( mul-Ring R r s))
      ( comp-hom-Ab
        ( ab-right-module-Ring)
        ( ab-right-module-Ring)
        ( ab-right-module-Ring)
        ( map-hom-Ring R
          ( op-Ring endomorphism-ring-ab-right-module-Ring)
          ( mul-hom-right-module-Ring)
          ( s))
        ( map-hom-Ring R
          ( op-Ring endomorphism-ring-ab-right-module-Ring)
          ( mul-hom-right-module-Ring)
          ( r)))
      ( preserves-mul-hom-Ring R
        ( op-Ring endomorphism-ring-ab-right-module-Ring)
        ( mul-hom-right-module-Ring))

  left-zero-law-mul-right-module-Ring :
    (x : type-right-module-Ring) →
    Id ( mul-right-module-Ring (zero-Ring R) x) zero-right-module-Ring
  left-zero-law-mul-right-module-Ring =
    htpy-eq-hom-Ab
      ( ab-right-module-Ring)
      ( ab-right-module-Ring)
      ( map-hom-Ring R
        ( op-Ring endomorphism-ring-ab-right-module-Ring)
        ( mul-hom-right-module-Ring)
        ( zero-Ring R))
      ( zero-hom-Ab ab-right-module-Ring ab-right-module-Ring)
      ( preserves-zero-hom-Ring R
        ( op-Ring endomorphism-ring-ab-right-module-Ring)
        ( mul-hom-right-module-Ring))

  right-zero-law-mul-right-module-Ring :
    (r : type-Ring R) →
    Id ( mul-right-module-Ring r zero-right-module-Ring) zero-right-module-Ring
  right-zero-law-mul-right-module-Ring r =
    preserves-zero-hom-Ab
      ( ab-right-module-Ring)
      ( ab-right-module-Ring)
      ( map-hom-Ring R
        ( op-Ring endomorphism-ring-ab-right-module-Ring)
        ( mul-hom-right-module-Ring)
        ( r))

  left-negative-law-mul-right-module-Ring :
    (r : type-Ring R) (x : type-right-module-Ring) →
    Id
      ( mul-right-module-Ring (neg-Ring R r) x)
      ( neg-right-module-Ring (mul-right-module-Ring r x))
  left-negative-law-mul-right-module-Ring r =
    htpy-eq-hom-Ab
      ( ab-right-module-Ring)
      ( ab-right-module-Ring)
      ( map-hom-Ring R
        ( op-Ring endomorphism-ring-ab-right-module-Ring)
        ( mul-hom-right-module-Ring)
        ( neg-Ring R r))
      ( neg-hom-Ab
        ( ab-right-module-Ring)
        ( ab-right-module-Ring)
        ( map-hom-Ring R
          ( op-Ring endomorphism-ring-ab-right-module-Ring)
          ( mul-hom-right-module-Ring)
          ( r)))
      ( preserves-neg-hom-Ring R
        ( op-Ring endomorphism-ring-ab-right-module-Ring)
        ( mul-hom-right-module-Ring))

  right-negative-law-mul-right-module-Ring :
    (r : type-Ring R) (x : type-right-module-Ring) →
    Id
      ( mul-right-module-Ring r (neg-right-module-Ring x))
      ( neg-right-module-Ring (mul-right-module-Ring r x))
  right-negative-law-mul-right-module-Ring r x =
    preserves-negatives-hom-Ab
      ( ab-right-module-Ring)
      ( ab-right-module-Ring)
      ( map-hom-Ring R
        ( op-Ring endomorphism-ring-ab-right-module-Ring)
        ( mul-hom-right-module-Ring)
        ( r))
```

### Properties

#### Multiplying by the negation of the one of the ring is negation

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R)
  where

  abstract
    mul-neg-one-left-module-Ring :
      (x : type-left-module-Ring R M) →
      mul-left-module-Ring R M (neg-Ring R (one-Ring R)) x ＝
      neg-left-module-Ring R M x
    mul-neg-one-left-module-Ring x =
      left-negative-law-mul-left-module-Ring R M _ _ ∙
      ap (neg-left-module-Ring R M) (left-unit-law-mul-left-module-Ring R M x)
```
