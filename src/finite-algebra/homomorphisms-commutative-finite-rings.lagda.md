# Homomorphisms of commutative finite rings

```agda
module finite-algebra.homomorphisms-commutative-finite-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.homomorphisms-commutative-rings
open import commutative-algebra.homomorphisms-commutative-semirings

open import finite-algebra.commutative-finite-rings

open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-monoids

open import ring-theory.homomorphisms-rings
```

</details>

## Idea

A
{{#concept "homomorphism" Disambiguation="of commutative finite rings" Agda=hom-Finite-Commutative-Ring}}
of [commutative finite rings](finite-algebra.commutative-finite-rings.md) is a
[homomorphism](ring-theory.homomorphisms-rings.md) between their underlying
[rings](ring-theory.rings.md).

## Definition

### The predicate of being a ring homomorphism

```agda
module _
  {l1 l2 : Level}
  (A : Finite-Commutative-Ring l1) (B : Finite-Commutative-Ring l2)
  where

  is-commutative-finite-ring-homomorphism-hom-Ab-Prop :
    hom-Ab (ab-Finite-Commutative-Ring A) (ab-Finite-Commutative-Ring B) →
    Prop (l1 ⊔ l2)
  is-commutative-finite-ring-homomorphism-hom-Ab-Prop =
    is-ring-homomorphism-hom-Ab-Prop
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)

  is-commutative-finite-ring-homomorphism-hom-Ab :
    hom-Ab (ab-Finite-Commutative-Ring A) (ab-Finite-Commutative-Ring B) →
    UU (l1 ⊔ l2)
  is-commutative-finite-ring-homomorphism-hom-Ab =
    is-ring-homomorphism-hom-Ab
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)

  is-prop-is-commutative-finite-ring-homomorphism-hom-Ab :
    (f : hom-Ab (ab-Finite-Commutative-Ring A) (ab-Finite-Commutative-Ring B)) →
    is-prop
      ( is-commutative-ring-homomorphism-hom-Ab
        ( commutative-ring-Finite-Commutative-Ring A)
        ( commutative-ring-Finite-Commutative-Ring B)
        ( f))
  is-prop-is-commutative-finite-ring-homomorphism-hom-Ab =
    is-prop-is-ring-homomorphism-hom-Ab
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
```

```agda
module _
  {l1 l2 : Level}
  (A : Finite-Commutative-Ring l1) (B : Finite-Commutative-Ring l2)
  where

  hom-set-Finite-Commutative-Ring : Set (l1 ⊔ l2)
  hom-set-Finite-Commutative-Ring =
    hom-set-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)

  hom-Finite-Commutative-Ring : UU (l1 ⊔ l2)
  hom-Finite-Commutative-Ring =
    hom-Ring (ring-Finite-Commutative-Ring A) (ring-Finite-Commutative-Ring B)

  is-set-hom-Finite-Commutative-Ring : is-set hom-Finite-Commutative-Ring
  is-set-hom-Finite-Commutative-Ring =
    is-set-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)

  module _
    (f : hom-Finite-Commutative-Ring)
    where

    hom-ab-hom-Finite-Commutative-Ring :
      hom-Ab (ab-Finite-Commutative-Ring A) (ab-Finite-Commutative-Ring B)
    hom-ab-hom-Finite-Commutative-Ring =
      hom-ab-hom-Ring
        ( ring-Finite-Commutative-Ring A)
        ( ring-Finite-Commutative-Ring B)
        ( f)

    hom-multiplicative-monoid-hom-Finite-Commutative-Ring :
      hom-Monoid
        ( multiplicative-monoid-Finite-Commutative-Ring A)
        ( multiplicative-monoid-Finite-Commutative-Ring B)
    hom-multiplicative-monoid-hom-Finite-Commutative-Ring =
      hom-multiplicative-monoid-hom-Ring
        ( ring-Finite-Commutative-Ring A)
        ( ring-Finite-Commutative-Ring B)
        ( f)

    map-hom-Finite-Commutative-Ring :
      type-Finite-Commutative-Ring A → type-Finite-Commutative-Ring B
    map-hom-Finite-Commutative-Ring =
      map-hom-Ring
        ( ring-Finite-Commutative-Ring A)
        ( ring-Finite-Commutative-Ring B)
        ( f)

    preserves-add-hom-Finite-Commutative-Ring :
      preserves-add-Ab
        ( ab-Finite-Commutative-Ring A)
        ( ab-Finite-Commutative-Ring B)
        ( map-hom-Finite-Commutative-Ring)
    preserves-add-hom-Finite-Commutative-Ring =
      preserves-add-hom-Ring
        ( ring-Finite-Commutative-Ring A)
        ( ring-Finite-Commutative-Ring B)
        ( f)

    preserves-zero-hom-Finite-Commutative-Ring :
      preserves-zero-Ab
        ( ab-Finite-Commutative-Ring A)
        ( ab-Finite-Commutative-Ring B)
        ( map-hom-Finite-Commutative-Ring)
    preserves-zero-hom-Finite-Commutative-Ring =
      preserves-zero-hom-Ring
        ( ring-Finite-Commutative-Ring A)
        ( ring-Finite-Commutative-Ring B)
        ( f)

    preserves-neg-hom-Finite-Commutative-Ring :
      preserves-negatives-Ab
        ( ab-Finite-Commutative-Ring A)
        ( ab-Finite-Commutative-Ring B)
        ( map-hom-Finite-Commutative-Ring)
    preserves-neg-hom-Finite-Commutative-Ring =
      preserves-neg-hom-Ring
        ( ring-Finite-Commutative-Ring A)
        ( ring-Finite-Commutative-Ring B)
        ( f)

    preserves-mul-hom-Finite-Commutative-Ring :
      preserves-mul-hom-Ab
        ( ring-Finite-Commutative-Ring A)
        ( ring-Finite-Commutative-Ring B)
        ( hom-ab-hom-Finite-Commutative-Ring)
    preserves-mul-hom-Finite-Commutative-Ring =
      preserves-mul-hom-Ring
        ( ring-Finite-Commutative-Ring A)
        ( ring-Finite-Commutative-Ring B)
        ( f)

    preserves-one-hom-Finite-Commutative-Ring :
      preserves-unit-hom-Ab
        ( ring-Finite-Commutative-Ring A)
        ( ring-Finite-Commutative-Ring B)
        ( hom-ab-hom-Finite-Commutative-Ring)
    preserves-one-hom-Finite-Commutative-Ring =
      preserves-one-hom-Ring
        ( ring-Finite-Commutative-Ring A)
        ( ring-Finite-Commutative-Ring B)
        ( f)

    is-commutative-ring-homomorphism-hom-Finite-Commutative-Ring :
      is-commutative-ring-homomorphism-hom-Ab
        ( commutative-ring-Finite-Commutative-Ring A)
        ( commutative-ring-Finite-Commutative-Ring B)
        ( hom-ab-hom-Finite-Commutative-Ring)
    is-commutative-ring-homomorphism-hom-Finite-Commutative-Ring =
      is-ring-homomorphism-hom-Ring
        ( ring-Finite-Commutative-Ring A)
        ( ring-Finite-Commutative-Ring B)
        ( f)

    hom-commutative-semiring-hom-Finite-Commutative-Ring :
      hom-Commutative-Semiring
        ( commutative-semiring-Finite-Commutative-Ring A)
        ( commutative-semiring-Finite-Commutative-Ring B)
    hom-commutative-semiring-hom-Finite-Commutative-Ring =
      hom-semiring-hom-Ring
        ( ring-Finite-Commutative-Ring A)
        ( ring-Finite-Commutative-Ring B)
        ( f)
```

### The identity homomorphism of commutative rings

```agda
module _
  {l : Level} (A : Finite-Commutative-Ring l)
  where

  preserves-mul-id-hom-Finite-Commutative-Ring :
    preserves-mul-hom-Ab
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring A)
      ( id-hom-Ab (ab-Finite-Commutative-Ring A))
  preserves-mul-id-hom-Finite-Commutative-Ring =
    preserves-mul-id-hom-Ring (ring-Finite-Commutative-Ring A)

  preserves-unit-id-hom-Finite-Commutative-Ring :
    preserves-unit-hom-Ab
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring A)
      ( id-hom-Ab (ab-Finite-Commutative-Ring A))
  preserves-unit-id-hom-Finite-Commutative-Ring =
    preserves-unit-id-hom-Ring (ring-Finite-Commutative-Ring A)

  is-ring-homomorphism-id-hom-Finite-Commutative-Ring :
    is-ring-homomorphism-hom-Ab
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring A)
      ( id-hom-Ab (ab-Finite-Commutative-Ring A))
  is-ring-homomorphism-id-hom-Finite-Commutative-Ring =
    is-ring-homomorphism-id-hom-Ring (ring-Finite-Commutative-Ring A)

  id-hom-Finite-Commutative-Ring : hom-Finite-Commutative-Ring A A
  id-hom-Finite-Commutative-Ring = id-hom-Ring (ring-Finite-Commutative-Ring A)
```

### Composition of commutative ring homomorphisms

```agda
module _
  {l1 l2 l3 : Level}
  (A : Finite-Commutative-Ring l1)
  (B : Finite-Commutative-Ring l2)
  (C : Finite-Commutative-Ring l3)
  (g : hom-Finite-Commutative-Ring B C)
  (f : hom-Finite-Commutative-Ring A B)
  where

  hom-ab-comp-hom-Finite-Commutative-Ring :
    hom-Ab (ab-Finite-Commutative-Ring A) (ab-Finite-Commutative-Ring C)
  hom-ab-comp-hom-Finite-Commutative-Ring =
    hom-ab-comp-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
      ( ring-Finite-Commutative-Ring C)
      ( g)
      ( f)

  hom-multiplicative-monoid-comp-hom-Finite-Commutative-Ring :
    hom-Monoid
      ( multiplicative-monoid-Finite-Commutative-Ring A)
      ( multiplicative-monoid-Finite-Commutative-Ring C)
  hom-multiplicative-monoid-comp-hom-Finite-Commutative-Ring =
    hom-multiplicative-monoid-comp-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
      ( ring-Finite-Commutative-Ring C)
      ( g)
      ( f)

  preserves-mul-comp-hom-Finite-Commutative-Ring :
    preserves-mul-hom-Ab
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring C)
      ( hom-ab-comp-hom-Finite-Commutative-Ring)
  preserves-mul-comp-hom-Finite-Commutative-Ring =
    preserves-mul-comp-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
      ( ring-Finite-Commutative-Ring C)
      ( g)
      ( f)

  preserves-unit-comp-hom-Finite-Commutative-Ring :
    preserves-unit-hom-Ab
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring C)
      ( hom-ab-comp-hom-Finite-Commutative-Ring)
  preserves-unit-comp-hom-Finite-Commutative-Ring =
    preserves-unit-comp-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
      ( ring-Finite-Commutative-Ring C)
      ( g)
      ( f)

  is-commutative-ring-homomorphism-comp-hom-Finite-Commutative-Ring :
    is-commutative-ring-homomorphism-hom-Ab
      ( commutative-ring-Finite-Commutative-Ring A)
      ( commutative-ring-Finite-Commutative-Ring C)
      ( hom-ab-comp-hom-Finite-Commutative-Ring)
  is-commutative-ring-homomorphism-comp-hom-Finite-Commutative-Ring =
    is-ring-homomorphism-comp-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
      ( ring-Finite-Commutative-Ring C)
      ( g)
      ( f)

  comp-hom-Finite-Commutative-Ring : hom-Finite-Commutative-Ring A C
  comp-hom-Finite-Commutative-Ring =
    comp-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
      ( ring-Finite-Commutative-Ring C)
      ( g)
      ( f)
```

### Homotopies of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level}
  (A : Finite-Commutative-Ring l1) (B : Finite-Commutative-Ring l2)
  where

  htpy-hom-Finite-Commutative-Ring :
    hom-Finite-Commutative-Ring A B → hom-Finite-Commutative-Ring A B →
    UU (l1 ⊔ l2)
  htpy-hom-Finite-Commutative-Ring =
    htpy-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)

  refl-htpy-hom-Finite-Commutative-Ring :
    (f : hom-Finite-Commutative-Ring A B) → htpy-hom-Finite-Commutative-Ring f f
  refl-htpy-hom-Finite-Commutative-Ring =
    refl-htpy-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
```

## Properties

### Homotopies characterize identifications of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level}
  (A : Finite-Commutative-Ring l1) (B : Finite-Commutative-Ring l2)
  (f : hom-Finite-Commutative-Ring A B)
  where

  htpy-eq-hom-Finite-Commutative-Ring :
    (g : hom-Finite-Commutative-Ring A B) →
    (f ＝ g) → htpy-hom-Finite-Commutative-Ring A B f g
  htpy-eq-hom-Finite-Commutative-Ring =
    htpy-eq-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
      ( f)

  is-torsorial-htpy-hom-Finite-Commutative-Ring :
    is-torsorial (htpy-hom-Finite-Commutative-Ring A B f)
  is-torsorial-htpy-hom-Finite-Commutative-Ring =
    is-torsorial-htpy-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
      ( f)

  is-equiv-htpy-eq-hom-Finite-Commutative-Ring :
    (g : hom-Finite-Commutative-Ring A B) →
    is-equiv (htpy-eq-hom-Finite-Commutative-Ring g)
  is-equiv-htpy-eq-hom-Finite-Commutative-Ring =
    is-equiv-htpy-eq-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
      ( f)

  extensionality-hom-Finite-Commutative-Ring :
    (g : hom-Finite-Commutative-Ring A B) →
    (f ＝ g) ≃ htpy-hom-Finite-Commutative-Ring A B f g
  extensionality-hom-Finite-Commutative-Ring =
    extensionality-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
      ( f)

  eq-htpy-hom-Finite-Commutative-Ring :
    (g : hom-Finite-Commutative-Ring A B) →
    htpy-hom-Finite-Commutative-Ring A B f g → f ＝ g
  eq-htpy-hom-Finite-Commutative-Ring =
    eq-htpy-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
      ( f)
```

### Associativity of composition of ring homomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Finite-Commutative-Ring l1)
  (B : Finite-Commutative-Ring l2)
  (C : Finite-Commutative-Ring l3)
  (D : Finite-Commutative-Ring l4)
  (h : hom-Finite-Commutative-Ring C D)
  (g : hom-Finite-Commutative-Ring B C)
  (f : hom-Finite-Commutative-Ring A B)
  where

  associative-comp-hom-Finite-Commutative-Ring :
    comp-hom-Finite-Commutative-Ring A B D
      ( comp-hom-Finite-Commutative-Ring B C D h g)
      ( f) ＝
    comp-hom-Finite-Commutative-Ring A C D
      ( h)
      ( comp-hom-Finite-Commutative-Ring A B C g f)
  associative-comp-hom-Finite-Commutative-Ring =
    associative-comp-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
      ( ring-Finite-Commutative-Ring C)
      ( ring-Finite-Commutative-Ring D)
      ( h)
      ( g)
      ( f)
```

### Unit laws for composition of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level}
  (A : Finite-Commutative-Ring l1)
  (B : Finite-Commutative-Ring l2)
  (f : hom-Finite-Commutative-Ring A B)
  where

  left-unit-law-comp-hom-Finite-Commutative-Ring :
    comp-hom-Finite-Commutative-Ring A B B
      ( id-hom-Finite-Commutative-Ring B)
      ( f) ＝
    f
  left-unit-law-comp-hom-Finite-Commutative-Ring =
    left-unit-law-comp-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
      ( f)

  right-unit-law-comp-hom-Finite-Commutative-Ring :
    comp-hom-Finite-Commutative-Ring A A B
      ( f)
      ( id-hom-Finite-Commutative-Ring A) ＝
    f
  right-unit-law-comp-hom-Finite-Commutative-Ring =
    right-unit-law-comp-hom-Ring
      ( ring-Finite-Commutative-Ring A)
      ( ring-Finite-Commutative-Ring B)
      ( f)
```
