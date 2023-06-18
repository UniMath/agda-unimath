# Homomorphisms of finite rings

```agda
module finite-algebra.homomorphisms-finite-rings where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.finite-rings

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-monoids

open import ring-theory.homomorphisms-rings
```

</details>

## Idea

Ring homomorphisms are maps between rings that preserve the ring structure

## Definitions

```agda
module _
  {l1 l2 : Level} (A : Ring-𝔽 l1) (B : Ring-𝔽 l2)
  where

  is-finite-ring-homomorphism-hom-Ab-Prop :
    type-hom-Ab (ab-Ring-𝔽 A) (ab-Ring-𝔽 B) → Prop (l1 ⊔ l2)
  is-finite-ring-homomorphism-hom-Ab-Prop =
    is-ring-homomorphism-hom-Ab-Prop
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)

  is-finite-ring-homomorphism-hom-Ab :
    type-hom-Ab (ab-Ring-𝔽 A) (ab-Ring-𝔽 B) → UU (l1 ⊔ l2)
  is-finite-ring-homomorphism-hom-Ab =
    is-ring-homomorphism-hom-Ab
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)

  is-prop-is-finite-ring-homomorphism-hom-Ab :
    (f : type-hom-Ab (ab-Ring-𝔽 A) (ab-Ring-𝔽 B)) →
    is-prop (is-finite-ring-homomorphism-hom-Ab f)
  is-prop-is-finite-ring-homomorphism-hom-Ab =
    is-prop-is-ring-homomorphism-hom-Ab
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
```

```agda
module _
  {l1 l2 : Level} (A : Ring-𝔽 l1) (B : Ring-𝔽 l2)
  where

  hom-Ring-𝔽 : Set (l1 ⊔ l2)
  hom-Ring-𝔽 =
    hom-Ring (ring-Ring-𝔽 A) (ring-Ring-𝔽 B)

  type-hom-Ring-𝔽 : UU (l1 ⊔ l2)
  type-hom-Ring-𝔽 =
    type-hom-Ring (ring-Ring-𝔽 A) (ring-Ring-𝔽 B)

  is-set-type-hom-Ring-𝔽 : is-set type-hom-Ring-𝔽
  is-set-type-hom-Ring-𝔽 =
    is-set-type-hom-Ring (ring-Ring-𝔽 A) (ring-Ring-𝔽 B)

  module _
    (f : type-hom-Ring-𝔽)
    where

    hom-ab-hom-Ring-𝔽 :
      type-hom-Ab (ab-Ring-𝔽 A) (ab-Ring-𝔽 B)
    hom-ab-hom-Ring-𝔽 =
      hom-ab-hom-Ring (ring-Ring-𝔽 A) (ring-Ring-𝔽 B) f

    hom-multiplicative-monoid-hom-Ring-𝔽 :
      type-hom-Monoid
        ( multiplicative-monoid-Ring-𝔽 A)
        ( multiplicative-monoid-Ring-𝔽 B)
    hom-multiplicative-monoid-hom-Ring-𝔽 =
      hom-multiplicative-monoid-hom-Ring
        ( ring-Ring-𝔽 A)
        ( ring-Ring-𝔽 B)
        ( f)

    map-hom-Ring-𝔽 : type-Ring-𝔽 A → type-Ring-𝔽 B
    map-hom-Ring-𝔽 =
      map-hom-Ring
        ( ring-Ring-𝔽 A)
        ( ring-Ring-𝔽 B)
        ( f)

    preserves-add-hom-Ring-𝔽 :
      preserves-add-Ab
        ( ab-Ring-𝔽 A)
        ( ab-Ring-𝔽 B)
        ( map-hom-Ring-𝔽)
    preserves-add-hom-Ring-𝔽 =
      preserves-add-hom-Ring
        ( ring-Ring-𝔽 A)
        ( ring-Ring-𝔽 B)
        ( f)

    preserves-zero-hom-Ring-𝔽 :
      preserves-zero-Ab
        ( ab-Ring-𝔽 A)
        ( ab-Ring-𝔽 B)
        ( map-hom-Ring-𝔽)
    preserves-zero-hom-Ring-𝔽 =
      preserves-zero-hom-Ring
        ( ring-Ring-𝔽 A)
        ( ring-Ring-𝔽 B)
        ( f)

    preserves-neg-hom-Ring-𝔽 :
      preserves-negatives-Ab
        ( ab-Ring-𝔽 A)
        ( ab-Ring-𝔽 B)
        ( map-hom-Ring-𝔽)
    preserves-neg-hom-Ring-𝔽 =
      preserves-neg-hom-Ring
        ( ring-Ring-𝔽 A)
        ( ring-Ring-𝔽 B)
        ( f)

    preserves-mul-hom-Ring-𝔽 :
      preserves-mul-hom-Ab
        ( ring-Ring-𝔽 A)
        ( ring-Ring-𝔽 B)
        ( hom-ab-hom-Ring-𝔽)
    preserves-mul-hom-Ring-𝔽 =
      preserves-mul-hom-Ring
        ( ring-Ring-𝔽 A)
        ( ring-Ring-𝔽 B)
        ( f)

    preserves-unit-hom-Ring-𝔽 :
      preserves-unit-hom-Ab
        ( ring-Ring-𝔽 A)
        ( ring-Ring-𝔽 B)
        ( hom-ab-hom-Ring-𝔽)
    preserves-unit-hom-Ring-𝔽 =
      preserves-unit-hom-Ring
        ( ring-Ring-𝔽 A)
        ( ring-Ring-𝔽 B)
        ( f)

    is-finite-ring-homomorphism-hom-Ring-𝔽 :
      is-finite-ring-homomorphism-hom-Ab A B hom-ab-hom-Ring-𝔽
    is-finite-ring-homomorphism-hom-Ring-𝔽 =
      is-ring-homomorphism-hom-Ring
        ( ring-Ring-𝔽 A)
        ( ring-Ring-𝔽 B)
        ( f)
```

### The identity homomorphism of commutative rings

```agda
module _
  {l : Level} (A : Ring-𝔽 l)
  where

  preserves-mul-id-hom-Ring-𝔽 :
    preserves-mul-hom-Ab
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 A)
      ( id-hom-Ab (ab-Ring-𝔽 A))
  preserves-mul-id-hom-Ring-𝔽 =
    preserves-mul-id-hom-Ring (ring-Ring-𝔽 A)

  preserves-unit-id-hom-Ring-𝔽 :
    preserves-unit-hom-Ab
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 A)
      ( id-hom-Ab (ab-Ring-𝔽 A))
  preserves-unit-id-hom-Ring-𝔽 =
    preserves-unit-id-hom-Ring (ring-Ring-𝔽 A)

  is-ring-homomorphism-id-hom-Ring-𝔽 :
    is-ring-homomorphism-hom-Ab
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 A)
      ( id-hom-Ab (ab-Ring-𝔽 A))
  is-ring-homomorphism-id-hom-Ring-𝔽 =
    is-ring-homomorphism-id-hom-Ring (ring-Ring-𝔽 A)

  id-hom-Ring-𝔽 : type-hom-Ring-𝔽 A A
  id-hom-Ring-𝔽 = id-hom-Ring (ring-Ring-𝔽 A)
```

### Composition of commutative ring homomorphisms

```agda
module _
  {l1 l2 l3 : Level}
  (A : Ring-𝔽 l1) (B : Ring-𝔽 l2) (C : Ring-𝔽 l3)
  (g : type-hom-Ring-𝔽 B C) (f : type-hom-Ring-𝔽 A B)
  where

  hom-ab-comp-hom-Ring-𝔽 :
    type-hom-Ab (ab-Ring-𝔽 A) (ab-Ring-𝔽 C)
  hom-ab-comp-hom-Ring-𝔽 =
    hom-ab-comp-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
      ( ring-Ring-𝔽 C)
      ( g)
      ( f)

  hom-multiplicative-monoid-comp-hom-Ring-𝔽 :
    type-hom-Monoid
      ( multiplicative-monoid-Ring-𝔽 A)
      ( multiplicative-monoid-Ring-𝔽 C)
  hom-multiplicative-monoid-comp-hom-Ring-𝔽 =
    hom-multiplicative-monoid-comp-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
      ( ring-Ring-𝔽 C)
      ( g)
      ( f)

  preserves-mul-comp-hom-Ring-𝔽 :
    preserves-mul-hom-Ab
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 C)
      ( hom-ab-comp-hom-Ring-𝔽)
  preserves-mul-comp-hom-Ring-𝔽 =
    preserves-mul-comp-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
      ( ring-Ring-𝔽 C)
      ( g)
      ( f)

  preserves-unit-comp-hom-Ring-𝔽 :
    preserves-unit-hom-Ab
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 C)
      ( hom-ab-comp-hom-Ring-𝔽)
  preserves-unit-comp-hom-Ring-𝔽 =
    preserves-unit-comp-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
      ( ring-Ring-𝔽 C)
      ( g)
      ( f)

  is-finite-ring-homomorphism-comp-hom-Ring-𝔽 :
    is-finite-ring-homomorphism-hom-Ab A C
      ( hom-ab-comp-hom-Ring-𝔽)
  is-finite-ring-homomorphism-comp-hom-Ring-𝔽 =
    is-ring-homomorphism-comp-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
      ( ring-Ring-𝔽 C)
      ( g)
      ( f)

  comp-hom-Ring-𝔽 : type-hom-Ring-𝔽 A C
  comp-hom-Ring-𝔽 =
    comp-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
      ( ring-Ring-𝔽 C)
      ( g)
      ( f)
```

### Homotopies of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level} (A : Ring-𝔽 l1) (B : Ring-𝔽 l2)
  where

  htpy-hom-Ring-𝔽 :
    type-hom-Ring-𝔽 A B → type-hom-Ring-𝔽 A B → UU (l1 ⊔ l2)
  htpy-hom-Ring-𝔽 =
    htpy-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)

  refl-htpy-hom-Ring-𝔽 :
    (f : type-hom-Ring-𝔽 A B) → htpy-hom-Ring-𝔽 f f
  refl-htpy-hom-Ring-𝔽 =
    refl-htpy-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
```

## Properties

### Homotopies characterize identifications of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level}
  (A : Ring-𝔽 l1) (B : Ring-𝔽 l2)
  (f : type-hom-Ring-𝔽 A B)
  where

  htpy-eq-hom-Ring-𝔽 :
    (g : type-hom-Ring-𝔽 A B) →
    (f ＝ g) → htpy-hom-Ring-𝔽 A B f g
  htpy-eq-hom-Ring-𝔽 =
    htpy-eq-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
      ( f)

  is-contr-total-htpy-hom-Ring-𝔽 :
    is-contr
      ( Σ (type-hom-Ring-𝔽 A B) (htpy-hom-Ring-𝔽 A B f))
  is-contr-total-htpy-hom-Ring-𝔽 =
    is-contr-total-htpy-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
      ( f)

  is-equiv-htpy-eq-hom-Ring-𝔽 :
    (g : type-hom-Ring-𝔽 A B) →
    is-equiv (htpy-eq-hom-Ring-𝔽 g)
  is-equiv-htpy-eq-hom-Ring-𝔽 =
    is-equiv-htpy-eq-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
      ( f)

  extensionality-hom-Ring-𝔽 :
    (g : type-hom-Ring-𝔽 A B) →
    (f ＝ g) ≃ htpy-hom-Ring-𝔽 A B f g
  extensionality-hom-Ring-𝔽 =
    extensionality-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
      ( f)

  eq-htpy-hom-Ring-𝔽 :
    (g : type-hom-Ring-𝔽 A B) →
    htpy-hom-Ring-𝔽 A B f g → f ＝ g
  eq-htpy-hom-Ring-𝔽 =
    eq-htpy-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
      ( f)
```

### Associativity of composition of ring homomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Ring-𝔽 l1)
  (B : Ring-𝔽 l2)
  (C : Ring-𝔽 l3)
  (D : Ring-𝔽 l4)
  (h : type-hom-Ring-𝔽 C D)
  (g : type-hom-Ring-𝔽 B C)
  (f : type-hom-Ring-𝔽 A B)
  where

  associative-comp-hom-Ring-𝔽 :
    ( comp-hom-Ring-𝔽 A B D
      ( comp-hom-Ring-𝔽 B C D h g)
      ( f)) ＝
    ( comp-hom-Ring-𝔽 A C D
      ( h)
      ( comp-hom-Ring-𝔽 A B C g f))
  associative-comp-hom-Ring-𝔽 =
    associative-comp-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
      ( ring-Ring-𝔽 C)
      ( ring-Ring-𝔽 D)
      ( h)
      ( g)
      ( f)
```

### Unit laws for composition of homomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level}
  (A : Ring-𝔽 l1)
  (B : Ring-𝔽 l2)
  (f : type-hom-Ring-𝔽 A B)
  where

  left-unit-law-comp-hom-Ring-𝔽 :
    comp-hom-Ring-𝔽 A B B (id-hom-Ring-𝔽 B) f ＝ f
  left-unit-law-comp-hom-Ring-𝔽 =
    left-unit-law-comp-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
      ( f)

  right-unit-law-comp-hom-Ring-𝔽 :
    comp-hom-Ring-𝔽 A A B f (id-hom-Ring-𝔽 A) ＝ f
  right-unit-law-comp-hom-Ring-𝔽 =
    right-unit-law-comp-hom-Ring
      ( ring-Ring-𝔽 A)
      ( ring-Ring-𝔽 B)
      ( f)
```
