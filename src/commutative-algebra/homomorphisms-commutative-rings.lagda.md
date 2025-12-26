# Homomorphisms of commutative rings

```agda
module commutative-algebra.homomorphisms-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.homomorphisms-commutative-semirings
open import commutative-algebra.invertible-elements-commutative-rings

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
{{#concept "homomorphism" Disambiguation="of commutative rings" Agda=hom-Commutative-Ring}}
of [commutative rings](commutative-algebra.commutative-rings.md) is a
[homomorphism](ring-theory.homomorphisms-rings.md) between their underlying
[rings](ring-theory.rings.md).

## Definition

### The predicate of being a ring homomorphism

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (B : Commutative-Ring l2)
  where

  is-commutative-ring-homomorphism-hom-Ab-Prop :
    hom-Ab (ab-Commutative-Ring A) (ab-Commutative-Ring B) → Prop (l1 ⊔ l2)
  is-commutative-ring-homomorphism-hom-Ab-Prop =
    is-ring-homomorphism-hom-Ab-Prop
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  is-commutative-ring-homomorphism-hom-Ab :
    hom-Ab (ab-Commutative-Ring A) (ab-Commutative-Ring B) → UU (l1 ⊔ l2)
  is-commutative-ring-homomorphism-hom-Ab =
    is-ring-homomorphism-hom-Ab
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  is-prop-is-commutative-ring-homomorphism-hom-Ab :
    (f : hom-Ab (ab-Commutative-Ring A) (ab-Commutative-Ring B)) →
    is-prop (is-commutative-ring-homomorphism-hom-Ab f)
  is-prop-is-commutative-ring-homomorphism-hom-Ab =
    is-prop-is-ring-homomorphism-hom-Ab
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
```

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (B : Commutative-Ring l2)
  where

  hom-set-Commutative-Ring : Set (l1 ⊔ l2)
  hom-set-Commutative-Ring =
    hom-set-Ring (ring-Commutative-Ring A) (ring-Commutative-Ring B)

  hom-Commutative-Ring : UU (l1 ⊔ l2)
  hom-Commutative-Ring =
    hom-Ring (ring-Commutative-Ring A) (ring-Commutative-Ring B)

  is-set-hom-Commutative-Ring : is-set hom-Commutative-Ring
  is-set-hom-Commutative-Ring =
    is-set-hom-Ring (ring-Commutative-Ring A) (ring-Commutative-Ring B)

  module _
    (f : hom-Commutative-Ring)
    where

    hom-ab-hom-Commutative-Ring :
      hom-Ab (ab-Commutative-Ring A) (ab-Commutative-Ring B)
    hom-ab-hom-Commutative-Ring =
      hom-ab-hom-Ring (ring-Commutative-Ring A) (ring-Commutative-Ring B) f

    hom-multiplicative-monoid-hom-Commutative-Ring :
      hom-Monoid
        ( multiplicative-monoid-Commutative-Ring A)
        ( multiplicative-monoid-Commutative-Ring B)
    hom-multiplicative-monoid-hom-Commutative-Ring =
      hom-multiplicative-monoid-hom-Ring
        ( ring-Commutative-Ring A)
        ( ring-Commutative-Ring B)
        ( f)

    map-hom-Commutative-Ring : type-Commutative-Ring A → type-Commutative-Ring B
    map-hom-Commutative-Ring =
      map-hom-Ring
        ( ring-Commutative-Ring A)
        ( ring-Commutative-Ring B)
        ( f)

    preserves-add-hom-Commutative-Ring :
      preserves-add-Ab
        ( ab-Commutative-Ring A)
        ( ab-Commutative-Ring B)
        ( map-hom-Commutative-Ring)
    preserves-add-hom-Commutative-Ring =
      preserves-add-hom-Ring
        ( ring-Commutative-Ring A)
        ( ring-Commutative-Ring B)
        ( f)

    preserves-zero-hom-Commutative-Ring :
      preserves-zero-Ab
        ( ab-Commutative-Ring A)
        ( ab-Commutative-Ring B)
        ( map-hom-Commutative-Ring)
    preserves-zero-hom-Commutative-Ring =
      preserves-zero-hom-Ring
        ( ring-Commutative-Ring A)
        ( ring-Commutative-Ring B)
        ( f)

    preserves-neg-hom-Commutative-Ring :
      preserves-negatives-Ab
        ( ab-Commutative-Ring A)
        ( ab-Commutative-Ring B)
        ( map-hom-Commutative-Ring)
    preserves-neg-hom-Commutative-Ring =
      preserves-neg-hom-Ring
        ( ring-Commutative-Ring A)
        ( ring-Commutative-Ring B)
        ( f)

    preserves-mul-hom-Commutative-Ring :
      preserves-mul-hom-Ab
        ( ring-Commutative-Ring A)
        ( ring-Commutative-Ring B)
        ( hom-ab-hom-Commutative-Ring)
    preserves-mul-hom-Commutative-Ring =
      preserves-mul-hom-Ring
        ( ring-Commutative-Ring A)
        ( ring-Commutative-Ring B)
        ( f)

    preserves-one-hom-Commutative-Ring :
      preserves-unit-hom-Ab
        ( ring-Commutative-Ring A)
        ( ring-Commutative-Ring B)
        ( hom-ab-hom-Commutative-Ring)
    preserves-one-hom-Commutative-Ring =
      preserves-one-hom-Ring
        ( ring-Commutative-Ring A)
        ( ring-Commutative-Ring B)
        ( f)

    is-commutative-ring-homomorphism-hom-Commutative-Ring :
      is-commutative-ring-homomorphism-hom-Ab A B hom-ab-hom-Commutative-Ring
    is-commutative-ring-homomorphism-hom-Commutative-Ring =
      is-ring-homomorphism-hom-Ring
        ( ring-Commutative-Ring A)
        ( ring-Commutative-Ring B)
        ( f)

    hom-commutative-semiring-hom-Commutative-Ring :
      hom-Commutative-Semiring
        ( commutative-semiring-Commutative-Ring A)
        ( commutative-semiring-Commutative-Ring B)
    hom-commutative-semiring-hom-Commutative-Ring =
      hom-semiring-hom-Ring
        ( ring-Commutative-Ring A)
        ( ring-Commutative-Ring B)
        ( f)
```

### The identity homomorphism of commutative rings

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  preserves-mul-id-hom-Commutative-Ring :
    preserves-mul-hom-Ab
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring A)
      ( id-hom-Ab (ab-Commutative-Ring A))
  preserves-mul-id-hom-Commutative-Ring =
    preserves-mul-id-hom-Ring (ring-Commutative-Ring A)

  preserves-unit-id-hom-Commutative-Ring :
    preserves-unit-hom-Ab
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring A)
      ( id-hom-Ab (ab-Commutative-Ring A))
  preserves-unit-id-hom-Commutative-Ring =
    preserves-unit-id-hom-Ring (ring-Commutative-Ring A)

  is-ring-homomorphism-id-hom-Commutative-Ring :
    is-ring-homomorphism-hom-Ab
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring A)
      ( id-hom-Ab (ab-Commutative-Ring A))
  is-ring-homomorphism-id-hom-Commutative-Ring =
    is-ring-homomorphism-id-hom-Ring (ring-Commutative-Ring A)

  id-hom-Commutative-Ring : hom-Commutative-Ring A A
  id-hom-Commutative-Ring = id-hom-Ring (ring-Commutative-Ring A)
```

### Composition of commutative ring homomorphisms

```agda
module _
  {l1 l2 l3 : Level}
  (A : Commutative-Ring l1) (B : Commutative-Ring l2) (C : Commutative-Ring l3)
  (g : hom-Commutative-Ring B C) (f : hom-Commutative-Ring A B)
  where

  hom-ab-comp-hom-Commutative-Ring :
    hom-Ab (ab-Commutative-Ring A) (ab-Commutative-Ring C)
  hom-ab-comp-hom-Commutative-Ring =
    hom-ab-comp-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( ring-Commutative-Ring C)
      ( g)
      ( f)

  hom-multiplicative-monoid-comp-hom-Commutative-Ring :
    hom-Monoid
      ( multiplicative-monoid-Commutative-Ring A)
      ( multiplicative-monoid-Commutative-Ring C)
  hom-multiplicative-monoid-comp-hom-Commutative-Ring =
    hom-multiplicative-monoid-comp-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( ring-Commutative-Ring C)
      ( g)
      ( f)

  preserves-mul-comp-hom-Commutative-Ring :
    preserves-mul-hom-Ab
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring C)
      ( hom-ab-comp-hom-Commutative-Ring)
  preserves-mul-comp-hom-Commutative-Ring =
    preserves-mul-comp-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( ring-Commutative-Ring C)
      ( g)
      ( f)

  preserves-unit-comp-hom-Commutative-Ring :
    preserves-unit-hom-Ab
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring C)
      ( hom-ab-comp-hom-Commutative-Ring)
  preserves-unit-comp-hom-Commutative-Ring =
    preserves-unit-comp-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( ring-Commutative-Ring C)
      ( g)
      ( f)

  is-commutative-ring-homomorphism-comp-hom-Commutative-Ring :
    is-commutative-ring-homomorphism-hom-Ab A C
      ( hom-ab-comp-hom-Commutative-Ring)
  is-commutative-ring-homomorphism-comp-hom-Commutative-Ring =
    is-ring-homomorphism-comp-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( ring-Commutative-Ring C)
      ( g)
      ( f)

  comp-hom-Commutative-Ring : hom-Commutative-Ring A C
  comp-hom-Commutative-Ring =
    comp-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( ring-Commutative-Ring C)
      ( g)
      ( f)
```

### Homotopies of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (B : Commutative-Ring l2)
  where

  htpy-hom-Commutative-Ring :
    hom-Commutative-Ring A B → hom-Commutative-Ring A B → UU (l1 ⊔ l2)
  htpy-hom-Commutative-Ring =
    htpy-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  refl-htpy-hom-Commutative-Ring :
    (f : hom-Commutative-Ring A B) → htpy-hom-Commutative-Ring f f
  refl-htpy-hom-Commutative-Ring =
    refl-htpy-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
```

## Properties

### Homotopies characterize identifications of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level}
  (A : Commutative-Ring l1) (B : Commutative-Ring l2)
  (f : hom-Commutative-Ring A B)
  where

  htpy-eq-hom-Commutative-Ring :
    (g : hom-Commutative-Ring A B) →
    (f ＝ g) → htpy-hom-Commutative-Ring A B f g
  htpy-eq-hom-Commutative-Ring =
    htpy-eq-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  is-torsorial-htpy-hom-Commutative-Ring :
    is-torsorial (htpy-hom-Commutative-Ring A B f)
  is-torsorial-htpy-hom-Commutative-Ring =
    is-torsorial-htpy-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  is-equiv-htpy-eq-hom-Commutative-Ring :
    (g : hom-Commutative-Ring A B) →
    is-equiv (htpy-eq-hom-Commutative-Ring g)
  is-equiv-htpy-eq-hom-Commutative-Ring =
    is-equiv-htpy-eq-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  extensionality-hom-Commutative-Ring :
    (g : hom-Commutative-Ring A B) →
    (f ＝ g) ≃ htpy-hom-Commutative-Ring A B f g
  extensionality-hom-Commutative-Ring =
    extensionality-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  eq-htpy-hom-Commutative-Ring :
    (g : hom-Commutative-Ring A B) →
    htpy-hom-Commutative-Ring A B f g → f ＝ g
  eq-htpy-hom-Commutative-Ring =
    eq-htpy-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)
```

### Associativity of composition of ring homomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Commutative-Ring l1)
  (B : Commutative-Ring l2)
  (C : Commutative-Ring l3)
  (D : Commutative-Ring l4)
  (h : hom-Commutative-Ring C D)
  (g : hom-Commutative-Ring B C)
  (f : hom-Commutative-Ring A B)
  where

  associative-comp-hom-Commutative-Ring :
    comp-hom-Commutative-Ring A B D (comp-hom-Commutative-Ring B C D h g) f ＝
    comp-hom-Commutative-Ring A C D h (comp-hom-Commutative-Ring A B C g f)
  associative-comp-hom-Commutative-Ring =
    associative-comp-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( ring-Commutative-Ring C)
      ( ring-Commutative-Ring D)
      ( h)
      ( g)
      ( f)
```

### Unit laws for composition of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level}
  (A : Commutative-Ring l1)
  (B : Commutative-Ring l2)
  (f : hom-Commutative-Ring A B)
  where

  left-unit-law-comp-hom-Commutative-Ring :
    comp-hom-Commutative-Ring A B B (id-hom-Commutative-Ring B) f ＝ f
  left-unit-law-comp-hom-Commutative-Ring =
    left-unit-law-comp-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  right-unit-law-comp-hom-Commutative-Ring :
    comp-hom-Commutative-Ring A A B f (id-hom-Commutative-Ring A) ＝ f
  right-unit-law-comp-hom-Commutative-Ring =
    right-unit-law-comp-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)
```

### Any homomorphism of commutative rings sends invertible elements to invertible elements

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (S : Commutative-Ring l2)
  (f : hom-Commutative-Ring A S)
  where

  preserves-invertible-elements-hom-Commutative-Ring :
    {x : type-Commutative-Ring A} →
    is-invertible-element-Commutative-Ring A x →
    is-invertible-element-Commutative-Ring S (map-hom-Commutative-Ring A S f x)
  preserves-invertible-elements-hom-Commutative-Ring =
    preserves-invertible-elements-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring S)
      ( f)
```
