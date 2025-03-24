# The universal property of identity systems

```agda
open import foundation.function-extensionality-axiom

module foundation.universal-property-identity-systems
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-systems
open import foundation.universal-property-contractible-types funext
open import foundation.universal-property-dependent-pair-types funext
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A **(unary) identity system** on a type `A` equipped with a point `a : A`
consists of a type family `B` over `A` equipped with a point `b : B a` that
satisfies an induction principle analogous to the induction principle of the
[identity type](foundation.identity-types.md) at `a`. The
[dependent universal property of identity types](foundation.universal-property-identity-types.md)
also follows for identity systems.

## Definition

### The universal property of identity systems

```agda
dependent-universal-property-identity-system :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {a : A} (b : B a) → UUω
dependent-universal-property-identity-system {A = A} B b =
  {l3 : Level} (P : (x : A) (y : B x) → UU l3) →
  is-equiv (ev-refl-identity-system b {P})
```

## Properties

### A type family satisfies the dependent universal property of identity systems if and only if it is torsorial

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {a : A} (b : B a)
  where

  dependent-universal-property-identity-system-is-torsorial :
    is-torsorial B →
    dependent-universal-property-identity-system B b
  dependent-universal-property-identity-system-is-torsorial
    H P =
    is-equiv-left-factor
      ( ev-refl-identity-system b)
      ( ev-pair)
      ( dependent-universal-property-contr-is-contr
        ( a , b)
        ( H)
        ( λ u → P (pr1 u) (pr2 u)))
      ( is-equiv-ev-pair)

  equiv-dependent-universal-property-identity-system-is-torsorial :
    is-torsorial B →
    {l : Level} {C : (x : A) → B x → UU l} →
    ((x : A) (y : B x) → C x y) ≃ C a b
  pr1 (equiv-dependent-universal-property-identity-system-is-torsorial H) =
    ev-refl-identity-system b
  pr2 (equiv-dependent-universal-property-identity-system-is-torsorial H) =
    dependent-universal-property-identity-system-is-torsorial H _

  is-torsorial-dependent-universal-property-identity-system :
    dependent-universal-property-identity-system B b →
    is-torsorial B
  pr1 (is-torsorial-dependent-universal-property-identity-system H) = (a , b)
  pr2 (is-torsorial-dependent-universal-property-identity-system H) u =
    map-inv-is-equiv
      ( H (λ x y → (a , b) ＝ (x , y)))
      ( refl)
      ( pr1 u)
      ( pr2 u)
```

### A type family satisfies the dependent universal property of identity systems if and only if it is an identity system

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {a : A} (b : B a)
  where

  dependent-universal-property-identity-system-is-identity-system :
    is-identity-system B a b →
    dependent-universal-property-identity-system B b
  dependent-universal-property-identity-system-is-identity-system H =
    dependent-universal-property-identity-system-is-torsorial b
      ( is-torsorial-is-identity-system a b H)

  is-identity-system-dependent-universal-property-identity-system :
    dependent-universal-property-identity-system B b →
    is-identity-system B a b
  is-identity-system-dependent-universal-property-identity-system H P =
    section-is-equiv (H P)
```
