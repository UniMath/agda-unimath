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
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.sections
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

### The predicate of being an identity system

```agda
ev-refl-identity-system :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {a : A} (b : B a)
  {P : (x : A) (y : B x) → UU l3} →
  ((x : A) (y : B x) → P x y) → P a b
ev-refl-identity-system b f = f _ b

module _
  {l1 l2 : Level} (l : Level) {A : UU l1} (B : A → UU l2) (a : A) (b : B a)
  where

  is-identity-system : UU (l1 ⊔ l2 ⊔ lsuc l)
  is-identity-system =
    (P : (x : A) (y : B x) → UU l) → section (ev-refl-identity-system b {P})
```

## Properties

### A type family over `A` is an identity system if and only if its total space is contractible

In [`foundation.torsorial-type-families`](foundation.torsorial-type-families.md)
we will start calling type families with contractible total space torsorial.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where

  abstract
    is-identity-system-is-torsorial :
      (H : is-contr (Σ A B)) →
      {l : Level} → is-identity-system l B a b
    pr1 (is-identity-system-is-torsorial H P) p x y =
      tr
        ( fam-Σ P)
        ( eq-is-contr H)
        ( p)
    pr2 (is-identity-system-is-torsorial H P) p =
      ap
        ( λ t → tr (fam-Σ P) t p)
        ( eq-is-contr'
          ( is-prop-is-contr H (pair a b) (pair a b))
          ( eq-is-contr H)
          ( refl))

  abstract
    is-torsorial-is-identity-system :
      ({l : Level} → is-identity-system l B a b) → is-contr (Σ A B)
    pr1 (pr1 (is-torsorial-is-identity-system H)) = a
    pr2 (pr1 (is-torsorial-is-identity-system H)) = b
    pr2 (is-torsorial-is-identity-system H) (pair x y) =
      pr1 (H (λ x' y' → (pair a b) ＝ (pair x' y'))) refl x y

  abstract
    fundamental-theorem-id-is-identity-system :
      ({l : Level} → is-identity-system l B a b) →
      (f : (x : A) → a ＝ x → B x) → (x : A) → is-equiv (f x)
    fundamental-theorem-id-is-identity-system H f =
      fundamental-theorem-id
        ( is-torsorial-is-identity-system H)
        ( f)
```
