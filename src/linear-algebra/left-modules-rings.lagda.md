# Left modules over rings

```agda
module linear-algebra.left-modules-rings where
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

A
{{#concept "left module" WD="left module" WDID="Q120721996" Agda=left-module-Ring}}
`M` over a [ring](ring-theory.rings.md) `R` consists of an
[abelian group](group-theory.abelian-groups.md) `M` equipped with an action
`R → M → M` such that

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

Equivalently, a left module `M` over a ring `R` consists of an abelian group `M`
equipped with a ring homomorphism `R → endomorphism-ring-Ab M`.

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
```

## Properties

### Associativity of addition

```agda
  associative-add-left-module-Ring :
    (x y z : type-left-module-Ring) →
    Id
      ( add-left-module-Ring (add-left-module-Ring x y) z)
      ( add-left-module-Ring x (add-left-module-Ring y z))
  associative-add-left-module-Ring =
    associative-add-Ab ab-left-module-Ring
```

### Unit laws for addition

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R)
  where

  left-unit-law-add-left-module-Ring :
    (x : type-left-module-Ring R M) →
    Id (add-left-module-Ring R M (zero-left-module-Ring R M) x) x
  left-unit-law-add-left-module-Ring =
    left-unit-law-add-Ab (ab-left-module-Ring R M)

  right-unit-law-add-left-module-Ring :
    (x : type-left-module-Ring R M) →
    Id (add-left-module-Ring R M x (zero-left-module-Ring R M)) x
  right-unit-law-add-left-module-Ring =
    right-unit-law-add-Ab (ab-left-module-Ring R M)
```

### Inverse laws for addition

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R)
  where

  left-inverse-law-add-left-module-Ring :
    (x : type-left-module-Ring R M) →
    Id
      ( add-left-module-Ring R M (neg-left-module-Ring R M x) x)
      ( zero-left-module-Ring R M)
  left-inverse-law-add-left-module-Ring =
    left-inverse-law-add-Ab (ab-left-module-Ring R M)

  right-inverse-law-add-left-module-Ring :
    (x : type-left-module-Ring R M) →
    Id
      ( add-left-module-Ring R M x (neg-left-module-Ring R M x))
      ( zero-left-module-Ring R M)
  right-inverse-law-add-left-module-Ring =
    right-inverse-law-add-Ab (ab-left-module-Ring R M)
```

### Unit laws for multiplication

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R)
  where

  abstract
    left-unit-law-mul-left-module-Ring :
      (x : type-left-module-Ring R M) →
      Id ( mul-left-module-Ring R M (one-Ring R) x) x
    left-unit-law-mul-left-module-Ring =
      htpy-eq-hom-Ab
        ( ab-left-module-Ring R M)
        ( ab-left-module-Ring R M)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring R M)
          ( mul-hom-left-module-Ring R M)
          ( one-Ring R))
        ( id-hom-Ab (ab-left-module-Ring R M))
        ( preserves-one-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring R M)
          ( mul-hom-left-module-Ring R M))
```

### Distributive law for multiplication and addition

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R)
  where

  abstract
    left-distributive-mul-add-left-module-Ring :
      (r : type-Ring R) (x y : type-left-module-Ring R M) →
      Id
        ( mul-left-module-Ring R M r (add-left-module-Ring R M x y))
        ( add-left-module-Ring R M
          ( mul-left-module-Ring R M r x)
          ( mul-left-module-Ring R M r y))
    left-distributive-mul-add-left-module-Ring r x y =
      preserves-add-hom-Ab
        ( ab-left-module-Ring R M)
        ( ab-left-module-Ring R M)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring R M)
          ( mul-hom-left-module-Ring R M)
          ( r))

    right-distributive-mul-add-left-module-Ring :
      (r s : type-Ring R) (x : type-left-module-Ring R M) →
      Id
        ( mul-left-module-Ring R M (add-Ring R r s) x)
        ( add-left-module-Ring R M
          ( mul-left-module-Ring R M r x)
          ( mul-left-module-Ring R M s x))
    right-distributive-mul-add-left-module-Ring r s =
      htpy-eq-hom-Ab
        ( ab-left-module-Ring R M)
        ( ab-left-module-Ring R M)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring R M)
          ( mul-hom-left-module-Ring R M)
          ( add-Ring R r s))
        ( add-hom-Ab
          ( ab-left-module-Ring R M)
          ( ab-left-module-Ring R M)
          ( map-hom-Ring R
            ( endomorphism-ring-ab-left-module-Ring R M)
            ( mul-hom-left-module-Ring R M)
            ( r))
          ( map-hom-Ring R
            ( endomorphism-ring-ab-left-module-Ring R M)
            ( mul-hom-left-module-Ring R M)
            ( s)))
        ( preserves-add-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring R M)
          ( mul-hom-left-module-Ring R M))
```

### Associativity laws for multiplication

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R)
  where

  abstract
    associative-mul-left-module-Ring :
      (r s : type-Ring R) (x : type-left-module-Ring R M) →
      Id
        ( mul-left-module-Ring R M (mul-Ring R r s) x)
        ( mul-left-module-Ring R M r (mul-left-module-Ring R M s x))
    associative-mul-left-module-Ring r s =
      htpy-eq-hom-Ab
        ( ab-left-module-Ring R M)
        ( ab-left-module-Ring R M)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring R M)
          ( mul-hom-left-module-Ring R M)
          ( mul-Ring R r s))
        ( comp-hom-Ab
          ( ab-left-module-Ring R M)
          ( ab-left-module-Ring R M)
          ( ab-left-module-Ring R M)
          ( map-hom-Ring R
            ( endomorphism-ring-ab-left-module-Ring R M)
            ( mul-hom-left-module-Ring R M)
            ( r))
          ( map-hom-Ring R
            ( endomorphism-ring-ab-left-module-Ring R M)
            ( mul-hom-left-module-Ring R M)
            ( s)))
        ( preserves-mul-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring R M)
          ( mul-hom-left-module-Ring R M))
```

### Zero laws for multiplication

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R)
  where

  abstract
    left-zero-law-mul-left-module-Ring :
      (x : type-left-module-Ring R M) →
      Id ( mul-left-module-Ring R M (zero-Ring R) x) (zero-left-module-Ring R M)
    left-zero-law-mul-left-module-Ring =
      htpy-eq-hom-Ab
        ( ab-left-module-Ring R M)
        ( ab-left-module-Ring R M)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring R M)
          ( mul-hom-left-module-Ring R M)
          ( zero-Ring R))
        ( zero-hom-Ab (ab-left-module-Ring R M) (ab-left-module-Ring R M))
        ( preserves-zero-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring R M)
          ( mul-hom-left-module-Ring R M))

    right-zero-law-mul-left-module-Ring :
      (r : type-Ring R) →
      Id
        ( mul-left-module-Ring R M r (zero-left-module-Ring R M))
        ( zero-left-module-Ring R M)
    right-zero-law-mul-left-module-Ring r =
      preserves-zero-hom-Ab
        ( ab-left-module-Ring R M)
        ( ab-left-module-Ring R M)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring R M)
          ( mul-hom-left-module-Ring R M)
          ( r))
```

### Negative laws for multiplication

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (M : left-module-Ring l2 R)
  where

  abstract
    left-negative-law-mul-left-module-Ring :
      (r : type-Ring R) (x : type-left-module-Ring R M) →
      Id
        ( mul-left-module-Ring R M (neg-Ring R r) x)
        ( neg-left-module-Ring R M (mul-left-module-Ring R M r x))
    left-negative-law-mul-left-module-Ring r =
      htpy-eq-hom-Ab
        ( ab-left-module-Ring R M)
        ( ab-left-module-Ring R M)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring R M)
          ( mul-hom-left-module-Ring R M)
          ( neg-Ring R r))
        ( neg-hom-Ab
          ( ab-left-module-Ring R M)
          ( ab-left-module-Ring R M)
          ( map-hom-Ring R
            ( endomorphism-ring-ab-left-module-Ring R M)
            ( mul-hom-left-module-Ring R M)
            ( r)))
        ( preserves-neg-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring R M)
          ( mul-hom-left-module-Ring R M))

    right-negative-law-mul-left-module-Ring :
      (r : type-Ring R) (x : type-left-module-Ring R M) →
      Id
        ( mul-left-module-Ring R M r (neg-left-module-Ring R M x))
        ( neg-left-module-Ring R M (mul-left-module-Ring R M r x))
    right-negative-law-mul-left-module-Ring r x =
      preserves-negatives-hom-Ab
        ( ab-left-module-Ring R M)
        ( ab-left-module-Ring R M)
        ( map-hom-Ring R
          ( endomorphism-ring-ab-left-module-Ring R M)
          ( mul-hom-left-module-Ring R M)
          ( r))
```

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
