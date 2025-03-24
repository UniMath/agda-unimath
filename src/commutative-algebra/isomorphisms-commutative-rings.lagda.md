# Isomorphisms of commutative rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module commutative-algebra.isomorphisms-commutative-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories funext univalence truncations

open import commutative-algebra.commutative-rings funext univalence truncations
open import commutative-algebra.homomorphisms-commutative-rings funext univalence truncations
open import commutative-algebra.invertible-elements-commutative-rings funext univalence truncations
open import commutative-algebra.precategory-of-commutative-rings funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.propositions funext univalence
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families funext univalence truncations
open import foundation.universe-levels

open import group-theory.isomorphisms-abelian-groups funext univalence truncations

open import ring-theory.isomorphisms-rings funext univalence truncations
```

</details>

## Idea

An **isomorphism** of
[commutative rings](commutative-algebra.commutative-rings.md) is an invertible
[homomorphism](commutative-algebra.homomorphisms-commutative-rings.md) of
commutative rings.

## Definitions

### The predicate of being an isomorphism of rings

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (B : Commutative-Ring l2)
  (f : hom-Commutative-Ring A B)
  where

  is-iso-prop-Commutative-Ring : Prop (l1 ⊔ l2)
  is-iso-prop-Commutative-Ring =
    is-iso-prop-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  is-iso-Commutative-Ring : UU (l1 ⊔ l2)
  is-iso-Commutative-Ring =
    is-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  is-prop-is-iso-Commutative-Ring : is-prop is-iso-Commutative-Ring
  is-prop-is-iso-Commutative-Ring =
    is-prop-is-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  hom-inv-is-iso-Commutative-Ring :
    is-iso-Commutative-Ring → hom-Commutative-Ring B A
  hom-inv-is-iso-Commutative-Ring =
    hom-inv-is-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  is-section-hom-inv-is-iso-Commutative-Ring :
    (U : is-iso-Commutative-Ring) →
    comp-hom-Commutative-Ring B A B f (hom-inv-is-iso-Commutative-Ring U) ＝
    id-hom-Commutative-Ring B
  is-section-hom-inv-is-iso-Commutative-Ring =
    is-section-hom-inv-is-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  is-retraction-hom-inv-is-iso-Commutative-Ring :
    (U : is-iso-Commutative-Ring) →
    comp-hom-Commutative-Ring A B A (hom-inv-is-iso-Commutative-Ring U) f ＝
    id-hom-Commutative-Ring A
  is-retraction-hom-inv-is-iso-Commutative-Ring =
    is-retraction-hom-inv-is-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
      ( f)

  map-inv-is-iso-Commutative-Ring :
    is-iso-Commutative-Ring →
    type-Commutative-Ring B → type-Commutative-Ring A
  map-inv-is-iso-Commutative-Ring U =
    map-hom-Commutative-Ring B A (hom-inv-is-iso-Commutative-Ring U)

  is-section-map-inv-is-iso-Commutative-Ring :
    (U : is-iso-Commutative-Ring) →
    map-hom-Commutative-Ring A B f ∘ map-inv-is-iso-Commutative-Ring U ~ id
  is-section-map-inv-is-iso-Commutative-Ring U =
    htpy-eq-hom-Commutative-Ring B B
      ( comp-hom-Commutative-Ring B A B f
        ( hom-inv-is-iso-Commutative-Ring U))
      ( id-hom-Commutative-Ring B)
      ( is-section-hom-inv-is-iso-Commutative-Ring U)

  is-retraction-map-inv-is-iso-Commutative-Ring :
    (U : is-iso-Commutative-Ring) →
    map-inv-is-iso-Commutative-Ring U ∘ map-hom-Commutative-Ring A B f ~ id
  is-retraction-map-inv-is-iso-Commutative-Ring U =
    htpy-eq-hom-Commutative-Ring A A
      ( comp-hom-Commutative-Ring A B A
        ( hom-inv-is-iso-Commutative-Ring U) f)
      ( id-hom-Commutative-Ring A)
      ( is-retraction-hom-inv-is-iso-Commutative-Ring U)
```

### Isomorphisms of commutative rings

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (B : Commutative-Ring l2)
  where

  iso-Commutative-Ring : UU (l1 ⊔ l2)
  iso-Commutative-Ring =
    iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  hom-iso-Commutative-Ring :
    iso-Commutative-Ring → hom-Commutative-Ring A B
  hom-iso-Commutative-Ring =
    hom-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  map-iso-Commutative-Ring :
    iso-Commutative-Ring → type-Commutative-Ring A → type-Commutative-Ring B
  map-iso-Commutative-Ring =
    map-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  preserves-zero-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) →
    map-iso-Commutative-Ring f (zero-Commutative-Ring A) ＝
    zero-Commutative-Ring B
  preserves-zero-iso-Commutative-Ring =
    preserves-zero-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  preserves-one-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) →
    map-iso-Commutative-Ring f (one-Commutative-Ring A) ＝
    one-Commutative-Ring B
  preserves-one-iso-Commutative-Ring =
    preserves-one-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  preserves-add-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) {x y : type-Commutative-Ring A} →
    map-iso-Commutative-Ring f (add-Commutative-Ring A x y) ＝
    add-Commutative-Ring B
      ( map-iso-Commutative-Ring f x)
      ( map-iso-Commutative-Ring f y)
  preserves-add-iso-Commutative-Ring =
    preserves-add-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  preserves-neg-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) {x : type-Commutative-Ring A} →
    map-iso-Commutative-Ring f (neg-Commutative-Ring A x) ＝
    neg-Commutative-Ring B (map-iso-Commutative-Ring f x)
  preserves-neg-iso-Commutative-Ring =
    preserves-neg-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  preserves-mul-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) {x y : type-Commutative-Ring A} →
    map-iso-Commutative-Ring f (mul-Commutative-Ring A x y) ＝
    mul-Commutative-Ring B
      ( map-iso-Commutative-Ring f x)
      ( map-iso-Commutative-Ring f y)
  preserves-mul-iso-Commutative-Ring =
    preserves-mul-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  is-iso-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) →
    is-iso-Commutative-Ring A B (hom-iso-Commutative-Ring f)
  is-iso-iso-Commutative-Ring =
    is-iso-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  hom-inv-iso-Commutative-Ring :
    iso-Commutative-Ring → hom-Commutative-Ring B A
  hom-inv-iso-Commutative-Ring =
    hom-inv-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  map-inv-iso-Commutative-Ring :
    iso-Commutative-Ring → type-Commutative-Ring B → type-Commutative-Ring A
  map-inv-iso-Commutative-Ring =
    map-inv-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  preserves-zero-inv-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) →
    map-inv-iso-Commutative-Ring f (zero-Commutative-Ring B) ＝
    zero-Commutative-Ring A
  preserves-zero-inv-iso-Commutative-Ring =
    preserves-zero-inv-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  preserves-one-inv-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) →
    map-inv-iso-Commutative-Ring f (one-Commutative-Ring B) ＝
    one-Commutative-Ring A
  preserves-one-inv-iso-Commutative-Ring =
    preserves-one-inv-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  preserves-add-inv-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) {x y : type-Commutative-Ring B} →
    map-inv-iso-Commutative-Ring f (add-Commutative-Ring B x y) ＝
    add-Commutative-Ring A
      ( map-inv-iso-Commutative-Ring f x)
      ( map-inv-iso-Commutative-Ring f y)
  preserves-add-inv-iso-Commutative-Ring =
    preserves-add-inv-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  preserves-neg-inv-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) {x : type-Commutative-Ring B} →
    map-inv-iso-Commutative-Ring f (neg-Commutative-Ring B x) ＝
    neg-Commutative-Ring A (map-inv-iso-Commutative-Ring f x)
  preserves-neg-inv-iso-Commutative-Ring =
    preserves-neg-inv-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  preserves-mul-inv-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) {x y : type-Commutative-Ring B} →
    map-inv-iso-Commutative-Ring f (mul-Commutative-Ring B x y) ＝
    mul-Commutative-Ring A
      ( map-inv-iso-Commutative-Ring f x)
      ( map-inv-iso-Commutative-Ring f y)
  preserves-mul-inv-iso-Commutative-Ring =
    preserves-mul-inv-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  is-section-hom-inv-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) →
    comp-hom-Commutative-Ring B A B
      ( hom-iso-Commutative-Ring f)
      ( hom-inv-iso-Commutative-Ring f) ＝
    id-hom-Commutative-Ring B
  is-section-hom-inv-iso-Commutative-Ring =
    is-section-hom-inv-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  is-section-map-inv-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) →
    map-iso-Commutative-Ring f ∘ map-inv-iso-Commutative-Ring f ~ id
  is-section-map-inv-iso-Commutative-Ring =
    is-section-map-inv-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  is-retraction-hom-inv-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) →
    comp-hom-Commutative-Ring A B A
      ( hom-inv-iso-Commutative-Ring f)
      ( hom-iso-Commutative-Ring f) ＝
    id-hom-Commutative-Ring A
  is-retraction-hom-inv-iso-Commutative-Ring =
    is-retraction-hom-inv-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  is-retraction-map-inv-iso-Commutative-Ring :
    (f : iso-Commutative-Ring) →
    map-inv-iso-Commutative-Ring f ∘ map-iso-Commutative-Ring f ~ id
  is-retraction-map-inv-iso-Commutative-Ring =
    is-retraction-map-inv-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
```

### The identity isomorphism of commutative rings

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  is-iso-id-hom-Commutative-Ring :
    is-iso-Commutative-Ring A A (id-hom-Commutative-Ring A)
  is-iso-id-hom-Commutative-Ring =
    is-iso-id-hom-Ring (ring-Commutative-Ring A)

  id-iso-Commutative-Ring : iso-Commutative-Ring A A
  id-iso-Commutative-Ring = id-iso-Ring (ring-Commutative-Ring A)
```

### Converting identifications of commutative rings to isomorphisms of commutative rings

```agda
iso-eq-Commutative-Ring :
  { l : Level} (A B : Commutative-Ring l) → A ＝ B → iso-Commutative-Ring A B
iso-eq-Commutative-Ring =
  iso-eq-Large-Precategory Commutative-Ring-Large-Precategory
```

## Properties

### A commutative ring homomorphism is an isomorphism if and only if the underlying homomorphism of abelian groups is an isomorphism

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (B : Commutative-Ring l2)
  where

  iso-ab-Commutative-Ring : UU (l1 ⊔ l2)
  iso-ab-Commutative-Ring =
    iso-ab-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  iso-ab-iso-ab-Commutative-Ring :
    iso-ab-Commutative-Ring →
    iso-Ab (ab-Commutative-Ring A) (ab-Commutative-Ring B)
  iso-ab-iso-ab-Commutative-Ring =
    iso-ab-iso-ab-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  is-iso-ab-hom-Commutative-Ring :
    hom-Commutative-Ring A B → UU (l1 ⊔ l2)
  is-iso-ab-hom-Commutative-Ring =
    is-iso-ab-hom-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  is-iso-ab-is-iso-Commutative-Ring :
    (f : hom-Commutative-Ring A B) →
    is-iso-Commutative-Ring A B f → is-iso-ab-hom-Commutative-Ring f
  is-iso-ab-is-iso-Commutative-Ring =
    is-iso-ab-is-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  iso-ab-iso-Commutative-Ring :
    iso-Commutative-Ring A B →
    iso-Ab (ab-Commutative-Ring A) (ab-Commutative-Ring B)
  iso-ab-iso-Commutative-Ring =
    iso-ab-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)

  equiv-iso-ab-iso-Commutative-Ring :
    iso-Commutative-Ring A B ≃ iso-ab-Commutative-Ring
  equiv-iso-ab-iso-Commutative-Ring =
    equiv-iso-ab-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring B)
```

### Characterizing identifications of commutative rings

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  abstract
    is-torsorial-iso-Commutative-Ring :
      is-torsorial (λ (B : Commutative-Ring l) → iso-Commutative-Ring A B)
    is-torsorial-iso-Commutative-Ring =
      is-torsorial-Eq-subtype
        ( is-torsorial-iso-Ring (ring-Commutative-Ring A))
        ( is-prop-is-commutative-Ring)
        ( ring-Commutative-Ring A)
        ( id-iso-Ring (ring-Commutative-Ring A))
        ( commutative-mul-Commutative-Ring A)

  is-equiv-iso-eq-Commutative-Ring :
    (B : Commutative-Ring l) → is-equiv (iso-eq-Commutative-Ring A B)
  is-equiv-iso-eq-Commutative-Ring =
    fundamental-theorem-id
      ( is-torsorial-iso-Commutative-Ring)
      ( iso-eq-Commutative-Ring A)

  extensionality-Commutative-Ring :
    (B : Commutative-Ring l) → (A ＝ B) ≃ iso-Commutative-Ring A B
  pr1 (extensionality-Commutative-Ring B) = iso-eq-Commutative-Ring A B
  pr2 (extensionality-Commutative-Ring B) = is-equiv-iso-eq-Commutative-Ring B

  eq-iso-Commutative-Ring :
    (B : Commutative-Ring l) → iso-Commutative-Ring A B → A ＝ B
  eq-iso-Commutative-Ring B =
    map-inv-is-equiv (is-equiv-iso-eq-Commutative-Ring B)
```

### Any isomorphism of commutative rings preserves and reflects invertible elements

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (S : Commutative-Ring l2)
  (f : iso-Commutative-Ring A S)
  where

  preserves-invertible-elements-iso-Commutative-Ring :
    {x : type-Commutative-Ring A} →
    is-invertible-element-Commutative-Ring A x →
    is-invertible-element-Commutative-Ring S (map-iso-Commutative-Ring A S f x)
  preserves-invertible-elements-iso-Commutative-Ring =
    preserves-invertible-elements-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring S)
      ( f)

  reflects-invertible-elements-iso-Commutative-Ring :
    {x : type-Commutative-Ring A} →
    is-invertible-element-Commutative-Ring S
      ( map-iso-Commutative-Ring A S f x) →
    is-invertible-element-Commutative-Ring A x
  reflects-invertible-elements-iso-Commutative-Ring =
    reflects-invertible-elements-iso-Ring
      ( ring-Commutative-Ring A)
      ( ring-Commutative-Ring S)
      ( f)
```
