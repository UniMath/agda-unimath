# Spans of pointed types

```agda
module structured-types.spans-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.spans
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

Consider two [pointed types](structured-types.pointed-types.md). A
{{#concept "binary span" Disambiguation="pointed types"}} from `A` to `B`
consists of a
{{#concept "spanning pointed type" Disambiguation="binary span of pointed types"}}
`S` and a [pair](foundation.dependent-pair-types.md) of
[pointed maps](structured-types.pointed-maps.md) `f : S →∗ A` and `g : S →∗ B`.
The pointed types `A` and `B` in the specification of a binary span of pointed
types are also referred to as the
{{#concept "domain" Disambiguation="binary span of pointed types"}} and
{{#concept "codomain" Disambiguation="binary span of pointed types"}} of the
span, respectively.

## Definitions

### (Binary) spans

```agda
span-Pointed-Type :
  {l1 l2 : Level} (l : Level) (A : Pointed-Type l1) (B : Pointed-Type l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
span-Pointed-Type l A B = Σ (Pointed-Type l) (λ X → (X →∗ A) × (X →∗ B))

module _
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (c : span-Pointed-Type l3 A B)
  where

  spanning-pointed-type-span-Pointed-Type : Pointed-Type l3
  spanning-pointed-type-span-Pointed-Type = pr1 c

  spanning-type-span-Pointed-Type : UU l3
  spanning-type-span-Pointed-Type =
    type-Pointed-Type spanning-pointed-type-span-Pointed-Type

  point-spanning-type-span-Pointed-Type : spanning-type-span-Pointed-Type
  point-spanning-type-span-Pointed-Type =
    point-Pointed-Type spanning-pointed-type-span-Pointed-Type

  left-pointed-map-span-Pointed-Type :
    spanning-pointed-type-span-Pointed-Type →∗ A
  left-pointed-map-span-Pointed-Type = pr1 (pr2 c)

  left-map-span-Pointed-Type :
    spanning-type-span-Pointed-Type → type-Pointed-Type A
  left-map-span-Pointed-Type =
    map-pointed-map left-pointed-map-span-Pointed-Type

  preserves-point-left-map-span-Pointed-Type :
    left-map-span-Pointed-Type point-spanning-type-span-Pointed-Type ＝
    point-Pointed-Type A
  preserves-point-left-map-span-Pointed-Type =
    preserves-point-pointed-map left-pointed-map-span-Pointed-Type

  right-pointed-map-span-Pointed-Type :
    spanning-pointed-type-span-Pointed-Type →∗ B
  right-pointed-map-span-Pointed-Type = pr2 (pr2 c)

  right-map-span-Pointed-Type :
    spanning-type-span-Pointed-Type → type-Pointed-Type B
  right-map-span-Pointed-Type =
    map-pointed-map right-pointed-map-span-Pointed-Type

  preserves-point-right-map-span-Pointed-Type :
    right-map-span-Pointed-Type point-spanning-type-span-Pointed-Type ＝
    point-Pointed-Type B
  preserves-point-right-map-span-Pointed-Type =
    preserves-point-pointed-map right-pointed-map-span-Pointed-Type

  span-span-Pointed-Type : span l3 (type-Pointed-Type A) (type-Pointed-Type B)
  pr1 span-span-Pointed-Type = spanning-type-span-Pointed-Type
  pr1 (pr2 span-span-Pointed-Type) = left-map-span-Pointed-Type
  pr2 (pr2 span-span-Pointed-Type) = right-map-span-Pointed-Type
```

### Identity spans

```agda
module _
  {l1 : Level} {X : Pointed-Type l1}
  where

  id-span-Pointed-Type : span-Pointed-Type l1 X X
  pr1 id-span-Pointed-Type = X
  pr1 (pr2 id-span-Pointed-Type) = id-pointed-map
  pr2 (pr2 id-span-Pointed-Type) = id-pointed-map
```

### The opposite of a span

```agda
module _
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  opposite-span-Pointed-Type :
    span-Pointed-Type l3 A B → span-Pointed-Type l3 B A
  pr1 (opposite-span-Pointed-Type s) =
    spanning-pointed-type-span-Pointed-Type s
  pr1 (pr2 (opposite-span-Pointed-Type s)) =
    right-pointed-map-span-Pointed-Type s
  pr2 (pr2 (opposite-span-Pointed-Type s)) =
    left-pointed-map-span-Pointed-Type s
```

## See also

- [Binary type duality](foundation.binary-type-duality.md)
- [Cospans](foundation.cospans.md)
- [Span diagrams](foundation.span-diagrams.md)
- [Spans](foundation.spans.md)
- [Spans of families of types](foundation.spans-families-of-types.md)
