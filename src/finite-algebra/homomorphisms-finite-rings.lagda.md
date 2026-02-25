# Homomorphisms of finite rings

```agda
module finite-algebra.homomorphisms-finite-rings where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.finite-rings

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

{{#concept "Finite ring homomorphisms" Agda=hom-Finite-Ring}} are maps between
[finite rings](finite-algebra.finite-rings.md) that preserve the ring structure.

## Definitions

```agda
module _
  {l1 l2 : Level} (A : Finite-Ring l1) (B : Finite-Ring l2)
  where

  is-finite-ring-homomorphism-hom-Ab-Prop :
    hom-Ab (ab-Finite-Ring A) (ab-Finite-Ring B) → Prop (l1 ⊔ l2)
  is-finite-ring-homomorphism-hom-Ab-Prop =
    is-ring-homomorphism-hom-Ab-Prop
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)

  is-finite-ring-homomorphism-hom-Ab :
    hom-Ab (ab-Finite-Ring A) (ab-Finite-Ring B) → UU (l1 ⊔ l2)
  is-finite-ring-homomorphism-hom-Ab =
    is-ring-homomorphism-hom-Ab
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)

  is-prop-is-finite-ring-homomorphism-hom-Ab :
    (f : hom-Ab (ab-Finite-Ring A) (ab-Finite-Ring B)) →
    is-prop (is-finite-ring-homomorphism-hom-Ab f)
  is-prop-is-finite-ring-homomorphism-hom-Ab =
    is-prop-is-ring-homomorphism-hom-Ab
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
```

```agda
module _
  {l1 l2 : Level} (A : Finite-Ring l1) (B : Finite-Ring l2)
  where

  hom-set-Finite-Ring : Set (l1 ⊔ l2)
  hom-set-Finite-Ring =
    hom-set-Ring (ring-Finite-Ring A) (ring-Finite-Ring B)

  hom-Finite-Ring : UU (l1 ⊔ l2)
  hom-Finite-Ring =
    hom-Ring (ring-Finite-Ring A) (ring-Finite-Ring B)

  is-set-hom-Finite-Ring : is-set hom-Finite-Ring
  is-set-hom-Finite-Ring =
    is-set-hom-Ring (ring-Finite-Ring A) (ring-Finite-Ring B)

  module _
    (f : hom-Finite-Ring)
    where

    hom-ab-hom-Finite-Ring :
      hom-Ab (ab-Finite-Ring A) (ab-Finite-Ring B)
    hom-ab-hom-Finite-Ring =
      hom-ab-hom-Ring (ring-Finite-Ring A) (ring-Finite-Ring B) f

    hom-multiplicative-monoid-hom-Finite-Ring :
      hom-Monoid
        ( multiplicative-monoid-Finite-Ring A)
        ( multiplicative-monoid-Finite-Ring B)
    hom-multiplicative-monoid-hom-Finite-Ring =
      hom-multiplicative-monoid-hom-Ring
        ( ring-Finite-Ring A)
        ( ring-Finite-Ring B)
        ( f)

    map-hom-Finite-Ring : type-Finite-Ring A → type-Finite-Ring B
    map-hom-Finite-Ring =
      map-hom-Ring
        ( ring-Finite-Ring A)
        ( ring-Finite-Ring B)
        ( f)

    preserves-add-hom-Finite-Ring :
      preserves-add-Ab
        ( ab-Finite-Ring A)
        ( ab-Finite-Ring B)
        ( map-hom-Finite-Ring)
    preserves-add-hom-Finite-Ring =
      preserves-add-hom-Ring
        ( ring-Finite-Ring A)
        ( ring-Finite-Ring B)
        ( f)

    preserves-zero-hom-Finite-Ring :
      preserves-zero-Ab
        ( ab-Finite-Ring A)
        ( ab-Finite-Ring B)
        ( map-hom-Finite-Ring)
    preserves-zero-hom-Finite-Ring =
      preserves-zero-hom-Ring
        ( ring-Finite-Ring A)
        ( ring-Finite-Ring B)
        ( f)

    preserves-neg-hom-Finite-Ring :
      preserves-negatives-Ab
        ( ab-Finite-Ring A)
        ( ab-Finite-Ring B)
        ( map-hom-Finite-Ring)
    preserves-neg-hom-Finite-Ring =
      preserves-neg-hom-Ring
        ( ring-Finite-Ring A)
        ( ring-Finite-Ring B)
        ( f)

    preserves-mul-hom-Finite-Ring :
      preserves-mul-hom-Ab
        ( ring-Finite-Ring A)
        ( ring-Finite-Ring B)
        ( hom-ab-hom-Finite-Ring)
    preserves-mul-hom-Finite-Ring =
      preserves-mul-hom-Ring
        ( ring-Finite-Ring A)
        ( ring-Finite-Ring B)
        ( f)

    preserves-one-hom-Finite-Ring :
      preserves-unit-hom-Ab
        ( ring-Finite-Ring A)
        ( ring-Finite-Ring B)
        ( hom-ab-hom-Finite-Ring)
    preserves-one-hom-Finite-Ring =
      preserves-one-hom-Ring
        ( ring-Finite-Ring A)
        ( ring-Finite-Ring B)
        ( f)

    is-finite-ring-homomorphism-hom-Finite-Ring :
      is-finite-ring-homomorphism-hom-Ab A B hom-ab-hom-Finite-Ring
    is-finite-ring-homomorphism-hom-Finite-Ring =
      is-ring-homomorphism-hom-Ring
        ( ring-Finite-Ring A)
        ( ring-Finite-Ring B)
        ( f)
```

### The identity homomorphism of commutative rings

```agda
module _
  {l : Level} (A : Finite-Ring l)
  where

  preserves-mul-id-hom-Finite-Ring :
    preserves-mul-hom-Ab
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring A)
      ( id-hom-Ab (ab-Finite-Ring A))
  preserves-mul-id-hom-Finite-Ring =
    preserves-mul-id-hom-Ring (ring-Finite-Ring A)

  preserves-unit-id-hom-Finite-Ring :
    preserves-unit-hom-Ab
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring A)
      ( id-hom-Ab (ab-Finite-Ring A))
  preserves-unit-id-hom-Finite-Ring =
    preserves-unit-id-hom-Ring (ring-Finite-Ring A)

  is-ring-homomorphism-id-hom-Finite-Ring :
    is-ring-homomorphism-hom-Ab
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring A)
      ( id-hom-Ab (ab-Finite-Ring A))
  is-ring-homomorphism-id-hom-Finite-Ring =
    is-ring-homomorphism-id-hom-Ring (ring-Finite-Ring A)

  id-hom-Finite-Ring : hom-Finite-Ring A A
  id-hom-Finite-Ring = id-hom-Ring (ring-Finite-Ring A)
```

### Composition of commutative ring homomorphisms

```agda
module _
  {l1 l2 l3 : Level}
  (A : Finite-Ring l1) (B : Finite-Ring l2) (C : Finite-Ring l3)
  (g : hom-Finite-Ring B C) (f : hom-Finite-Ring A B)
  where

  hom-ab-comp-hom-Finite-Ring :
    hom-Ab (ab-Finite-Ring A) (ab-Finite-Ring C)
  hom-ab-comp-hom-Finite-Ring =
    hom-ab-comp-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
      ( ring-Finite-Ring C)
      ( g)
      ( f)

  hom-multiplicative-monoid-comp-hom-Finite-Ring :
    hom-Monoid
      ( multiplicative-monoid-Finite-Ring A)
      ( multiplicative-monoid-Finite-Ring C)
  hom-multiplicative-monoid-comp-hom-Finite-Ring =
    hom-multiplicative-monoid-comp-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
      ( ring-Finite-Ring C)
      ( g)
      ( f)

  preserves-mul-comp-hom-Finite-Ring :
    preserves-mul-hom-Ab
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring C)
      ( hom-ab-comp-hom-Finite-Ring)
  preserves-mul-comp-hom-Finite-Ring =
    preserves-mul-comp-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
      ( ring-Finite-Ring C)
      ( g)
      ( f)

  preserves-unit-comp-hom-Finite-Ring :
    preserves-unit-hom-Ab
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring C)
      ( hom-ab-comp-hom-Finite-Ring)
  preserves-unit-comp-hom-Finite-Ring =
    preserves-unit-comp-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
      ( ring-Finite-Ring C)
      ( g)
      ( f)

  is-finite-ring-homomorphism-comp-hom-Finite-Ring :
    is-finite-ring-homomorphism-hom-Ab A C
      ( hom-ab-comp-hom-Finite-Ring)
  is-finite-ring-homomorphism-comp-hom-Finite-Ring =
    is-ring-homomorphism-comp-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
      ( ring-Finite-Ring C)
      ( g)
      ( f)

  comp-hom-Finite-Ring : hom-Finite-Ring A C
  comp-hom-Finite-Ring =
    comp-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
      ( ring-Finite-Ring C)
      ( g)
      ( f)
```

### Homotopies of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level} (A : Finite-Ring l1) (B : Finite-Ring l2)
  where

  htpy-hom-Finite-Ring :
    hom-Finite-Ring A B → hom-Finite-Ring A B → UU (l1 ⊔ l2)
  htpy-hom-Finite-Ring =
    htpy-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)

  refl-htpy-hom-Finite-Ring :
    (f : hom-Finite-Ring A B) → htpy-hom-Finite-Ring f f
  refl-htpy-hom-Finite-Ring =
    refl-htpy-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
```

## Properties

### Homotopies characterize identifications of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level}
  (A : Finite-Ring l1) (B : Finite-Ring l2)
  (f : hom-Finite-Ring A B)
  where

  htpy-eq-hom-Finite-Ring :
    (g : hom-Finite-Ring A B) →
    (f ＝ g) → htpy-hom-Finite-Ring A B f g
  htpy-eq-hom-Finite-Ring =
    htpy-eq-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
      ( f)

  is-torsorial-htpy-hom-Finite-Ring :
    is-torsorial (htpy-hom-Finite-Ring A B f)
  is-torsorial-htpy-hom-Finite-Ring =
    is-torsorial-htpy-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
      ( f)

  is-equiv-htpy-eq-hom-Finite-Ring :
    (g : hom-Finite-Ring A B) →
    is-equiv (htpy-eq-hom-Finite-Ring g)
  is-equiv-htpy-eq-hom-Finite-Ring =
    is-equiv-htpy-eq-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
      ( f)

  extensionality-hom-Finite-Ring :
    (g : hom-Finite-Ring A B) →
    (f ＝ g) ≃ htpy-hom-Finite-Ring A B f g
  extensionality-hom-Finite-Ring =
    extensionality-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
      ( f)

  eq-htpy-hom-Finite-Ring :
    (g : hom-Finite-Ring A B) →
    htpy-hom-Finite-Ring A B f g → f ＝ g
  eq-htpy-hom-Finite-Ring =
    eq-htpy-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
      ( f)
```

### Associativity of composition of ring homomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Finite-Ring l1)
  (B : Finite-Ring l2)
  (C : Finite-Ring l3)
  (D : Finite-Ring l4)
  (h : hom-Finite-Ring C D)
  (g : hom-Finite-Ring B C)
  (f : hom-Finite-Ring A B)
  where

  associative-comp-hom-Finite-Ring :
    comp-hom-Finite-Ring A B D (comp-hom-Finite-Ring B C D h g) f ＝
    comp-hom-Finite-Ring A C D h (comp-hom-Finite-Ring A B C g f)
  associative-comp-hom-Finite-Ring =
    associative-comp-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
      ( ring-Finite-Ring C)
      ( ring-Finite-Ring D)
      ( h)
      ( g)
      ( f)
```

### Unit laws for composition of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level}
  (A : Finite-Ring l1)
  (B : Finite-Ring l2)
  (f : hom-Finite-Ring A B)
  where

  left-unit-law-comp-hom-Finite-Ring :
    comp-hom-Finite-Ring A B B (id-hom-Finite-Ring B) f ＝ f
  left-unit-law-comp-hom-Finite-Ring =
    left-unit-law-comp-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
      ( f)

  right-unit-law-comp-hom-Finite-Ring :
    comp-hom-Finite-Ring A A B f (id-hom-Finite-Ring A) ＝ f
  right-unit-law-comp-hom-Finite-Ring =
    right-unit-law-comp-hom-Ring
      ( ring-Finite-Ring A)
      ( ring-Finite-Ring B)
      ( f)
```
