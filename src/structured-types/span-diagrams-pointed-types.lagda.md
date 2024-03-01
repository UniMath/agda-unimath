# Span diagrams

```agda
module structured-types.span-diagrams-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.universe-levels

open import structured-types.morphisms-pointed-arrows
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.spans-pointed-types
```

</details>

## Idea

A {{#concept "(binary) span diagram of pointed types"}} is a diagram of
[pointed maps](structured-types.pointed-maps.md) of the form

```text
       f       g
  A <----- S -----> B.
```

In other words, a span diagram of pointed types consists of two
[pointed types](structured-types.pointed-types.md) `A` and `B` and a
[span of pointed types](structured-types.spans-pointed-types.md) from `A` to
`B`.

### (Binary) span diagrams of pointed types

```agda
span-diagram-Pointed-Type :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
span-diagram-Pointed-Type l1 l2 l3 =
  Σ ( Pointed-Type l1)
    ( λ A → Σ (Pointed-Type l2) (span-Pointed-Type l3 A))

module _
  {l1 l2 l3 : Level} {S : Pointed-Type l1}
  {A : Pointed-Type l2} {B : Pointed-Type l3}
  where

  make-span-diagram-Pointed-Type :
    (S →∗ A) → (S →∗ B) → span-diagram-Pointed-Type l2 l3 l1
  pr1 (make-span-diagram-Pointed-Type f g) = A
  pr1 (pr2 (make-span-diagram-Pointed-Type f g)) = B
  pr1 (pr2 (pr2 (make-span-diagram-Pointed-Type f g))) = S
  pr1 (pr2 (pr2 (pr2 (make-span-diagram-Pointed-Type f g)))) = f
  pr2 (pr2 (pr2 (pr2 (make-span-diagram-Pointed-Type f g)))) = g

module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram-Pointed-Type l1 l2 l3)
  where

  pointed-domain-span-diagram-Pointed-Type : Pointed-Type l1
  pointed-domain-span-diagram-Pointed-Type = pr1 𝒮

  domain-span-diagram-Pointed-Type : UU l1
  domain-span-diagram-Pointed-Type =
    type-Pointed-Type pointed-domain-span-diagram-Pointed-Type

  point-domain-span-diagram-Pointed-Type :
    domain-span-diagram-Pointed-Type
  point-domain-span-diagram-Pointed-Type =
    point-Pointed-Type pointed-domain-span-diagram-Pointed-Type

  pointed-codomain-span-diagram-Pointed-Type : Pointed-Type l2
  pointed-codomain-span-diagram-Pointed-Type = pr1 (pr2 𝒮)

  codomain-span-diagram-Pointed-Type : UU l2
  codomain-span-diagram-Pointed-Type =
    type-Pointed-Type pointed-codomain-span-diagram-Pointed-Type

  point-codomain-span-diagram-Pointed-Type :
    codomain-span-diagram-Pointed-Type
  point-codomain-span-diagram-Pointed-Type =
    point-Pointed-Type pointed-codomain-span-diagram-Pointed-Type

  span-pointed-type-span-diagram-Pointed-Type :
    span-Pointed-Type l3
      ( pointed-domain-span-diagram-Pointed-Type)
      ( pointed-codomain-span-diagram-Pointed-Type)
  span-pointed-type-span-diagram-Pointed-Type = pr2 (pr2 𝒮)

  spanning-pointed-type-span-diagram-Pointed-Type : Pointed-Type l3
  spanning-pointed-type-span-diagram-Pointed-Type =
    spanning-pointed-type-span-Pointed-Type
      ( span-pointed-type-span-diagram-Pointed-Type)

  spanning-type-span-diagram-Pointed-Type : UU l3
  spanning-type-span-diagram-Pointed-Type =
    type-Pointed-Type spanning-pointed-type-span-diagram-Pointed-Type

  point-spanning-type-span-diagram-Pointed-Type :
    spanning-type-span-diagram-Pointed-Type
  point-spanning-type-span-diagram-Pointed-Type =
    point-Pointed-Type spanning-pointed-type-span-diagram-Pointed-Type

  left-pointed-map-span-diagram-Pointed-Type :
    spanning-pointed-type-span-diagram-Pointed-Type →∗
    pointed-domain-span-diagram-Pointed-Type
  left-pointed-map-span-diagram-Pointed-Type =
    left-pointed-map-span-Pointed-Type
      ( span-pointed-type-span-diagram-Pointed-Type)

  left-map-span-diagram-Pointed-Type :
    spanning-type-span-diagram-Pointed-Type → domain-span-diagram-Pointed-Type
  left-map-span-diagram-Pointed-Type =
    left-map-span-Pointed-Type
      ( span-pointed-type-span-diagram-Pointed-Type)

  preserves-point-left-map-span-diagram-Pointed-Type :
    left-map-span-diagram-Pointed-Type
      ( point-spanning-type-span-diagram-Pointed-Type) ＝
    point-domain-span-diagram-Pointed-Type
  preserves-point-left-map-span-diagram-Pointed-Type =
    preserves-point-left-map-span-Pointed-Type
      ( span-pointed-type-span-diagram-Pointed-Type)

  right-pointed-map-span-diagram-Pointed-Type :
    spanning-pointed-type-span-diagram-Pointed-Type →∗
    pointed-codomain-span-diagram-Pointed-Type
  right-pointed-map-span-diagram-Pointed-Type =
    right-pointed-map-span-Pointed-Type
      ( span-pointed-type-span-diagram-Pointed-Type)

  right-map-span-diagram-Pointed-Type :
    spanning-type-span-diagram-Pointed-Type → codomain-span-diagram-Pointed-Type
  right-map-span-diagram-Pointed-Type =
    right-map-span-Pointed-Type
      ( span-pointed-type-span-diagram-Pointed-Type)

  preserves-point-right-map-span-diagram-Pointed-Type :
    right-map-span-diagram-Pointed-Type
      ( point-spanning-type-span-diagram-Pointed-Type) ＝
    point-codomain-span-diagram-Pointed-Type
  preserves-point-right-map-span-diagram-Pointed-Type =
    preserves-point-right-map-span-Pointed-Type
      ( span-pointed-type-span-diagram-Pointed-Type)
```

### The span diagram obtained from a morphism of pointed arrows

Given pointed maps `f : A →∗ B` and `g : X →∗ Y` and a morphism of pointed arrows
`α : f →∗ g`, the span diagram associated to `α` is the span diagram

```text
       f       α₀
  B <----- A -----> X.
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  (f : A →∗ B) (g : X →∗ Y) (α : hom-pointed-arrow f g)
  where

  domain-span-diagram-hom-pointed-arrow : Pointed-Type l2
  domain-span-diagram-hom-pointed-arrow = B

  type-domain-span-diagram-hom-pointed-arrow : UU l2
  type-domain-span-diagram-hom-pointed-arrow =
    type-Pointed-Type domain-span-diagram-hom-pointed-arrow

  point-domain-span-diagram-hom-pointed-arrow :
    type-domain-span-diagram-hom-pointed-arrow
  point-domain-span-diagram-hom-pointed-arrow =
    point-Pointed-Type domain-span-diagram-hom-pointed-arrow

  codomain-span-diagram-hom-pointed-arrow : Pointed-Type l3
  codomain-span-diagram-hom-pointed-arrow = X

  type-codomain-span-diagram-hom-pointed-arrow : UU l3
  type-codomain-span-diagram-hom-pointed-arrow =
    type-Pointed-Type codomain-span-diagram-hom-pointed-arrow

  point-codomain-span-diagram-hom-pointed-arrow :
    type-codomain-span-diagram-hom-pointed-arrow
  point-codomain-span-diagram-hom-pointed-arrow =
    point-Pointed-Type codomain-span-diagram-hom-pointed-arrow  

  pointed-spanning-type-hom-pointed-arrow : Pointed-Type l1
  pointed-spanning-type-hom-pointed-arrow = A

  spanning-type-hom-pointed-arrow : UU l1
  spanning-type-hom-pointed-arrow =
    type-Pointed-Type pointed-spanning-type-hom-pointed-arrow

  point-spanning-type-hom-pointed-arrow :
    spanning-type-hom-pointed-arrow
  point-spanning-type-hom-pointed-arrow =
    point-Pointed-Type pointed-spanning-type-hom-pointed-arrow

  left-pointed-map-span-diagram-hom-pointed-arrow :
    pointed-spanning-type-hom-pointed-arrow →∗
    domain-span-diagram-hom-pointed-arrow
  left-pointed-map-span-diagram-hom-pointed-arrow = ?

  left-map-span-diagram-hom-pointed-arrow :
    spanning-type-hom-pointed-arrow → type-domain-span-diagram-hom-pointed-arrow
  left-map-span-diagram-hom-pointed-arrow = ?

  right-pointed-map-span

  right-map-span-diagram-hom-pointed-arrow :
    spanning-type-hom-pointed-arrow → type-codomain-span-diagram-hom-pointed-arrow
  right-map-span-diagram-hom-pointed-arrow = map-domain-hom-pointed-arrow f g α

  span-hom-pointed-arrow :
    span-Pointed-Type l1 B X
  pr1 span-hom-pointed-arrow = A
  pr1 (pr2 span-hom-pointed-arrow) = left-pointed-map-span-diagram-hom-pointed-arrow
  pr2 (pr2 span-hom-pointed-arrow) = right-pointed-map-span-diagram-hom-pointed-arrow

  span-diagram-hom-pointed-arrow : span-diagram-Pointed-Type l2 l3 l1
  pr1 span-diagram-hom-pointed-arrow =
    domain-span-diagram-hom-pointed-arrow
  pr1 (pr2 span-diagram-hom-pointed-arrow) =
    codomain-span-diagram-hom-pointed-arrow
  pr2 (pr2 span-diagram-hom-pointed-arrow) =
    span-hom-pointed-arrow
```

## See also

- [Cospans](foundation.cospans.md)
- [Diagonal spans](foundation.diagonal-spans.md)
- [Operations on spans](foundation.operations-spans.md)
- [Kernel spans of maps](foundation.kernel-spans-of-maps.md)
- [Spans of families of types](foundation.spans-families-of-types.md)
- [Transposition of span diagrams](foundation.transposition-span-diagram-Pointed-Types.md)
