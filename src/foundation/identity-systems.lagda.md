# Identity systems

```agda
module foundation.identity-systems where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.families-of-equivalences
open import foundation-core.identity-types
open import foundation-core.sections
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
```

</details>

## Idea

A **(unary) identity system** on a type `A` equipped with a point `a : A`
consists of a type family `B` over `A` equipped with a point `b : B a` that
satisfies an induction principle analogous to the induction principle of the
[identity type](foundation.identity-types.md) at `a`. The
[dependent universal property of identity types](foundation.universal-property-identity-types.md)
also follows for identity systems.

## Definitions

### Evaluating at the base point

```agda
ev-refl-identity-system :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {a : A} (b : B a)
  {P : (x : A) (y : B x) → UU l3} →
  ((x : A) (y : B x) → P x y) → P a b
ev-refl-identity-system {a = a} b f = f a b
```

### The predicate of being an identity system with respect to a universe level

```agda
module _
  {l1 l2 : Level} (l : Level) {A : UU l1} (B : A → UU l2) (a : A) (b : B a)
  where

  is-identity-system-Level : UU (l1 ⊔ l2 ⊔ lsuc l)
  is-identity-system-Level =
    (P : (x : A) (y : B x) → UU l) → section (ev-refl-identity-system b {P})
```

### The predicate of being an identity system

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A) (b : B a)
  where

  is-identity-system : UUω
  is-identity-system = {l : Level} → is-identity-system-Level l B a b
```

## Properties

### A type family over `A` is an identity system if and only if its total space is contractible

In [`foundation.torsorial-type-families`](foundation.torsorial-type-families.md)
we will start calling type families with contractible total space torsorial.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where

  map-section-is-identity-system-is-torsorial :
    is-torsorial B →
    {l3 : Level} (P : (x : A) (y : B x) → UU l3) →
    P a b → (x : A) (y : B x) → P x y
  map-section-is-identity-system-is-torsorial H P p x y =
    tr (fam-Σ P) (eq-is-contr H) p

  is-section-map-section-is-identity-system-is-torsorial :
    (H : is-torsorial B) →
    {l3 : Level} (P : (x : A) (y : B x) → UU l3) →
    is-section
      ( ev-refl-identity-system b)
      ( map-section-is-identity-system-is-torsorial H P)
  is-section-map-section-is-identity-system-is-torsorial H P p =
    ap
      ( λ t → tr (fam-Σ P) t p)
      ( eq-is-contr'
        ( is-prop-is-contr H (a , b) (a , b))
        ( eq-is-contr H)
        ( refl))

  abstract
    is-identity-system-is-torsorial :
      is-torsorial B → is-identity-system B a b
    is-identity-system-is-torsorial H P =
      ( map-section-is-identity-system-is-torsorial H P ,
        is-section-map-section-is-identity-system-is-torsorial H P)

  abstract
    is-torsorial-is-identity-system :
      is-identity-system B a b → is-torsorial B
    pr1 (is-torsorial-is-identity-system H) = (a , b)
    pr2 (is-torsorial-is-identity-system H) (x , y) =
      pr1 (H (λ x' y' → (a , b) ＝ (x' , y'))) refl x y

  abstract
    fundamental-theorem-id-is-identity-system :
      is-identity-system B a b →
      (f : (x : A) → a ＝ x → B x) → is-fiberwise-equiv f
    fundamental-theorem-id-is-identity-system H =
      fundamental-theorem-id (is-torsorial-is-identity-system H)
```

## External links

- [Identity systems](https://1lab.dev/1Lab.Path.IdentitySystem.html) at 1lab
- [identity system](https://ncatlab.org/nlab/show/identity+system) at $n$Lab
