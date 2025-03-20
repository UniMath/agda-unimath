# Pointed spans

```agda
open import foundation.function-extensionality-axiom

module
  structured-types.pointed-spans
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.spans
open import foundation.universe-levels

open import structured-types.pointed-maps funext
open import structured-types.pointed-types
```

</details>

## Idea

Consider two [pointed types](structured-types.pointed-types.md) `A` and `B`. A
{{#concept "(binary) pointed span" Agda=pointed-span}} from `A` to `B` consists
of a
{{#concept "spanning pointed type" Disambiguation="binary pointed span" Agda=spanning-pointed-type-pointed-span}}
`S` and a [pair](foundation.dependent-pair-types.md) of
[pointed maps](structured-types.pointed-maps.md) `f : S →∗ A` and `g : S →∗ B`.
The pointed types `A` and `B` in the specification of a binary span of pointed
types are also referred to as the
{{#concept "domain" Disambiguation="binary pointed span"}} and
{{#concept "codomain" Disambiguation="binary pointed span"}} of the pointed
span, respectively.

## Definitions

### (Binary) pointed spans

```agda
pointed-span :
  {l1 l2 : Level} (l : Level) (A : Pointed-Type l1) (B : Pointed-Type l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
pointed-span l A B = Σ (Pointed-Type l) (λ S → (S →∗ A) × (S →∗ B))

module _
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (𝒮 : pointed-span l3 A B)
  where

  spanning-pointed-type-pointed-span : Pointed-Type l3
  spanning-pointed-type-pointed-span = pr1 𝒮

  spanning-type-pointed-span : UU l3
  spanning-type-pointed-span =
    type-Pointed-Type spanning-pointed-type-pointed-span

  point-spanning-type-pointed-span : spanning-type-pointed-span
  point-spanning-type-pointed-span =
    point-Pointed-Type spanning-pointed-type-pointed-span

  left-pointed-map-pointed-span :
    spanning-pointed-type-pointed-span →∗ A
  left-pointed-map-pointed-span = pr1 (pr2 𝒮)

  left-map-pointed-span :
    spanning-type-pointed-span → type-Pointed-Type A
  left-map-pointed-span =
    map-pointed-map left-pointed-map-pointed-span

  preserves-point-left-map-pointed-span :
    left-map-pointed-span point-spanning-type-pointed-span ＝
    point-Pointed-Type A
  preserves-point-left-map-pointed-span =
    preserves-point-pointed-map left-pointed-map-pointed-span

  right-pointed-map-pointed-span :
    spanning-pointed-type-pointed-span →∗ B
  right-pointed-map-pointed-span = pr2 (pr2 𝒮)

  right-map-pointed-span :
    spanning-type-pointed-span → type-Pointed-Type B
  right-map-pointed-span =
    map-pointed-map right-pointed-map-pointed-span

  preserves-point-right-map-pointed-span :
    right-map-pointed-span point-spanning-type-pointed-span ＝
    point-Pointed-Type B
  preserves-point-right-map-pointed-span =
    preserves-point-pointed-map right-pointed-map-pointed-span

  span-pointed-span : span l3 (type-Pointed-Type A) (type-Pointed-Type B)
  pr1 span-pointed-span = spanning-type-pointed-span
  pr1 (pr2 span-pointed-span) = left-map-pointed-span
  pr2 (pr2 span-pointed-span) = right-map-pointed-span
```

### Identity pointed spans

```agda
module _
  {l1 : Level} {X : Pointed-Type l1}
  where

  id-pointed-span : pointed-span l1 X X
  pr1 id-pointed-span = X
  pr1 (pr2 id-pointed-span) = id-pointed-map
  pr2 (pr2 id-pointed-span) = id-pointed-map
```

## See also

- [Opposite pointed spans](structured-types.opposite-pointed-spans.md)
- [Pointed span diagrams](structured-types.pointed-span-diagrams.md)
- [Spans](foundation.spans.md)
