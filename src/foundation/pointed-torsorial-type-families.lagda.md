# Pointed torsorial type families

```agda
module foundation.pointed-torsorial-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.locally-small-types
open import foundation.propositional-truncations
open import foundation.sorial-type-families
open import foundation.transport
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.logical-equivalences
open import foundation-core.propositions
open import foundation-core.small-types

open import structured-types.pointed-types
```

</details>

## Idea

A type family `E` over a [pointed type](structured-types.pointed-types.md) `B`
is said to be **pointed torsorial** if it comes equipped with a family of
equivalences

```text
  E x ≃ (pt ＝ x)
```

indexed by `x : B`. Note that the type of such a **torsorial structure** on the
type family `E` is [equivalent](foundation.equivalences.md) to the type

```text
  E pt × is-contr (Σ B E)
```

Indeed, if `E` is pointed torsorial, then `refl : pt ＝ pt` induces an element
in `E pt`, and the [total space](foundation.dependent-pair-types.md) of `E` is
[contractible](foundation.contractible-types.md) by the
[fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md).
Conversely, if we are given an element `y : E pt` and the total space of `E` is
contractible, then the unique family of maps `(pt ＝ x) → E x` mapping `refl` to
`y` is a family of equivalences.

## Definitions

### The predicate of being a pointed torsorial type family

```agda
module _
  {l1 l2 : Level} (B : Pointed-Type l1) (E : type-Pointed-Type B → UU l2)
  where

  is-pointed-torsorial-family-of-types : UU (l1 ⊔ l2)
  is-pointed-torsorial-family-of-types =
    (x : type-Pointed-Type B) → E x ≃ (point-Pointed-Type B ＝ x)

module _
  {l1 l2 : Level} (B : Pointed-Type l1) {E : type-Pointed-Type B → UU l2}
  (T : is-pointed-torsorial-family-of-types B E)
  where

  point-is-pointed-torsorial-family-of-types : E (point-Pointed-Type B)
  point-is-pointed-torsorial-family-of-types =
    map-inv-equiv (T (point-Pointed-Type B)) refl

  is-contr-total-space-is-pointed-torsorial-family-of-types :
    is-contr (Σ (type-Pointed-Type B) E)
  is-contr-total-space-is-pointed-torsorial-family-of-types =
    fundamental-theorem-id'
      ( λ x → map-inv-equiv (T x))
      ( λ x → is-equiv-map-inv-equiv (T x))
```

### Torsorial families of types

```agda
pointed-torsorial-family-of-types :
  {l1 : Level} (l2 : Level) (B : Pointed-Type l1) → UU (l1 ⊔ lsuc l2)
pointed-torsorial-family-of-types l2 B =
  Σ (type-Pointed-Type B → UU l2) (is-pointed-torsorial-family-of-types B)
```

## Properties

### Any torsorial type family is sorial

```agda
is-sorial-is-pointed-torsorial-family-of-types :
  {l1 l2 : Level} (B : Pointed-Type l1) {E : type-Pointed-Type B → UU l2} →
  is-pointed-torsorial-family-of-types B E → is-sorial-family-of-types B E
is-sorial-is-pointed-torsorial-family-of-types B {E} H x y =
  equiv-tr E (map-equiv (H x) y)
```

### Being pointed torsorial is equivalent to being pointed and having contractible total space

```agda
module _
  {l1 l2 : Level} (B : Pointed-Type l1) {E : type-Pointed-Type B → UU l2}
  where

  point-and-contractible-total-space-is-pointed-torsorial-family-of-types :
    is-pointed-torsorial-family-of-types B E →
    E (point-Pointed-Type B) × is-contr (Σ (type-Pointed-Type B) E)
  pr1
    ( point-and-contractible-total-space-is-pointed-torsorial-family-of-types H)
    =
    point-is-pointed-torsorial-family-of-types B H
  pr2
    ( point-and-contractible-total-space-is-pointed-torsorial-family-of-types H)
    =
    is-contr-total-space-is-pointed-torsorial-family-of-types B H
```

### Pointed connected types equipped with a pointed torsorial family of types of universe level `l` are locally `l`-small

```agda
module _
  {l1 l2 : Level} (B : Pointed-Type l1) {E : type-Pointed-Type B → UU l2}
  (T : is-pointed-torsorial-family-of-types B E)
  where

  is-locally-small-is-pointed-torsorial-family-of-types :
    is-0-connected (type-Pointed-Type B) →
    is-locally-small l2 (type-Pointed-Type B)
  is-locally-small-is-pointed-torsorial-family-of-types H x y =
    apply-universal-property-trunc-Prop
      ( mere-eq-is-0-connected H (point-Pointed-Type B) x)
      ( is-small-Prop l2 (x ＝ y))
      ( λ { refl → (E y , inv-equiv (T y))})
```

### The type of pointed torsorial type families of universe level `l` over a pointed connected type is equivalent to the proposition that `B` is locally `l`-small

```agda
module _
  {l1 l2 : Level} (B : Pointed-Type l1)
  where

  is-locally-small-pointed-torsorial-family-of-types :
    is-0-connected (type-Pointed-Type B) →
    pointed-torsorial-family-of-types l2 B →
    is-locally-small l2 (type-Pointed-Type B)
  is-locally-small-pointed-torsorial-family-of-types H (E , T) =
    is-locally-small-is-pointed-torsorial-family-of-types B T H

  pointed-torsorial-family-of-types-is-locally-small :
    is-locally-small l2 (type-Pointed-Type B) →
    pointed-torsorial-family-of-types l2 B
  pr1 (pointed-torsorial-family-of-types-is-locally-small H) x =
    type-is-small (H (point-Pointed-Type B) x)
  pr2 (pointed-torsorial-family-of-types-is-locally-small H) x =
    inv-equiv-is-small (H (point-Pointed-Type B) x)

  is-prop-pointed-torsorial-family-of-types :
    is-prop (pointed-torsorial-family-of-types l2 B)
  is-prop-pointed-torsorial-family-of-types =
    is-prop-equiv'
      ( distributive-Π-Σ)
      ( is-prop-Π
        ( λ x →
          is-prop-equiv
            ( equiv-tot (λ X → equiv-inv-equiv))
            ( is-prop-is-small l2 (point-Pointed-Type B ＝ x))))

  compute-pointed-torsorial-family-of-types-is-0-connected :
    is-0-connected (type-Pointed-Type B) →
    is-locally-small l2 (type-Pointed-Type B) ≃
    pointed-torsorial-family-of-types l2 B
  compute-pointed-torsorial-family-of-types-is-0-connected H =
    equiv-iff
      ( is-locally-small-Prop l2 (type-Pointed-Type B))
      ( pointed-torsorial-family-of-types l2 B ,
        is-prop-pointed-torsorial-family-of-types)
      ( pointed-torsorial-family-of-types-is-locally-small)
      ( is-locally-small-pointed-torsorial-family-of-types H)

  is-contr-pointed-torsorial-family-of-types :
    is-locally-small l2 (type-Pointed-Type B) →
    is-contr (pointed-torsorial-family-of-types l2 B)
  is-contr-pointed-torsorial-family-of-types H =
    is-proof-irrelevant-is-prop
      ( is-prop-pointed-torsorial-family-of-types)
      ( pointed-torsorial-family-of-types-is-locally-small H)
```
