# Pointed span diagrams

```agda
module structured-types.pointed-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.universe-levels

open import structured-types.morphisms-pointed-arrows
open import structured-types.pointed-maps
open import structured-types.pointed-spans
open import structured-types.pointed-types
```

</details>

## Idea

A {{#concept "(binary) pointed span diagram" Agda=pointed-span-diagram}} is a
diagram of [pointed maps](structured-types.pointed-maps.md) of the form

```text
       f       g
  A <----- S -----> B.
```

In other words, a pointed span diagram consists of two
[pointed types](structured-types.pointed-types.md) `A` and `B` and a
[pointed span](structured-types.pointed-spans.md) from `A` to `B`.

### (Binary) span diagrams of pointed types

```agda
pointed-span-diagram :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
pointed-span-diagram l1 l2 l3 =
  Σ ( Pointed-Type l1)
    ( λ A → Σ (Pointed-Type l2) (pointed-span l3 A))

module _
  {l1 l2 l3 : Level} {S : Pointed-Type l1}
  {A : Pointed-Type l2} {B : Pointed-Type l3}
  where

  make-pointed-span-diagram :
    (S →∗ A) → (S →∗ B) → pointed-span-diagram l2 l3 l1
  make-pointed-span-diagram f g = (A , B , S , f , g)

module _
  {l1 l2 l3 : Level} (𝒮 : pointed-span-diagram l1 l2 l3)
  where

  pointed-domain-pointed-span-diagram : Pointed-Type l1
  pointed-domain-pointed-span-diagram = pr1 𝒮

  domain-pointed-span-diagram : UU l1
  domain-pointed-span-diagram =
    type-Pointed-Type pointed-domain-pointed-span-diagram

  point-domain-pointed-span-diagram :
    domain-pointed-span-diagram
  point-domain-pointed-span-diagram =
    point-Pointed-Type pointed-domain-pointed-span-diagram

  pointed-codomain-pointed-span-diagram : Pointed-Type l2
  pointed-codomain-pointed-span-diagram = pr1 (pr2 𝒮)

  codomain-pointed-span-diagram : UU l2
  codomain-pointed-span-diagram =
    type-Pointed-Type pointed-codomain-pointed-span-diagram

  point-codomain-pointed-span-diagram :
    codomain-pointed-span-diagram
  point-codomain-pointed-span-diagram =
    point-Pointed-Type pointed-codomain-pointed-span-diagram

  pointed-span-pointed-span-diagram :
    pointed-span l3
      ( pointed-domain-pointed-span-diagram)
      ( pointed-codomain-pointed-span-diagram)
  pointed-span-pointed-span-diagram = pr2 (pr2 𝒮)

  spanning-pointed-type-pointed-span-diagram : Pointed-Type l3
  spanning-pointed-type-pointed-span-diagram =
    spanning-pointed-type-pointed-span
      ( pointed-span-pointed-span-diagram)

  spanning-type-pointed-span-diagram : UU l3
  spanning-type-pointed-span-diagram =
    type-Pointed-Type spanning-pointed-type-pointed-span-diagram

  point-spanning-type-pointed-span-diagram :
    spanning-type-pointed-span-diagram
  point-spanning-type-pointed-span-diagram =
    point-Pointed-Type spanning-pointed-type-pointed-span-diagram

  left-pointed-map-pointed-span-diagram :
    spanning-pointed-type-pointed-span-diagram →∗
    pointed-domain-pointed-span-diagram
  left-pointed-map-pointed-span-diagram =
    left-pointed-map-pointed-span
      ( pointed-span-pointed-span-diagram)

  left-map-pointed-span-diagram :
    spanning-type-pointed-span-diagram → domain-pointed-span-diagram
  left-map-pointed-span-diagram =
    left-map-pointed-span
      ( pointed-span-pointed-span-diagram)

  preserves-point-left-map-pointed-span-diagram :
    left-map-pointed-span-diagram
      ( point-spanning-type-pointed-span-diagram) ＝
    point-domain-pointed-span-diagram
  preserves-point-left-map-pointed-span-diagram =
    preserves-point-left-map-pointed-span
      ( pointed-span-pointed-span-diagram)

  right-pointed-map-pointed-span-diagram :
    spanning-pointed-type-pointed-span-diagram →∗
    pointed-codomain-pointed-span-diagram
  right-pointed-map-pointed-span-diagram =
    right-pointed-map-pointed-span
      ( pointed-span-pointed-span-diagram)

  right-map-pointed-span-diagram :
    spanning-type-pointed-span-diagram → codomain-pointed-span-diagram
  right-map-pointed-span-diagram =
    right-map-pointed-span
      ( pointed-span-pointed-span-diagram)

  preserves-point-right-map-pointed-span-diagram :
    right-map-pointed-span-diagram
      ( point-spanning-type-pointed-span-diagram) ＝
    point-codomain-pointed-span-diagram
  preserves-point-right-map-pointed-span-diagram =
    preserves-point-right-map-pointed-span
      ( pointed-span-pointed-span-diagram)
```

### The pointed span diagram obtained from a morphism of pointed arrows

Given pointed maps `f : A →∗ B` and `g : X →∗ Y` and a morphism of pointed
arrows `α : f →∗ g`, the pointed span diagram associated to `α` is the pointed
span diagram

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
  left-pointed-map-span-diagram-hom-pointed-arrow = f

  left-map-span-diagram-hom-pointed-arrow :
    spanning-type-hom-pointed-arrow → type-domain-span-diagram-hom-pointed-arrow
  left-map-span-diagram-hom-pointed-arrow =
    map-pointed-map left-pointed-map-span-diagram-hom-pointed-arrow

  preserves-point-left-map-span-diagram-hom-pointed-arrow :
    left-map-span-diagram-hom-pointed-arrow
      ( point-spanning-type-hom-pointed-arrow) ＝
    point-domain-span-diagram-hom-pointed-arrow
  preserves-point-left-map-span-diagram-hom-pointed-arrow =
    preserves-point-pointed-map
      ( left-pointed-map-span-diagram-hom-pointed-arrow)

  right-pointed-map-span-diagram-hom-pointed-arrow :
    pointed-spanning-type-hom-pointed-arrow →∗
    codomain-span-diagram-hom-pointed-arrow
  right-pointed-map-span-diagram-hom-pointed-arrow =
    pointed-map-domain-hom-pointed-arrow f g α

  right-map-span-diagram-hom-pointed-arrow :
    spanning-type-hom-pointed-arrow →
    type-codomain-span-diagram-hom-pointed-arrow
  right-map-span-diagram-hom-pointed-arrow =
    map-pointed-map right-pointed-map-span-diagram-hom-pointed-arrow

  preserves-point-right-map-span-diagram-hom-pointed-arrow :
    right-map-span-diagram-hom-pointed-arrow
      ( point-spanning-type-hom-pointed-arrow) ＝
    point-codomain-span-diagram-hom-pointed-arrow
  preserves-point-right-map-span-diagram-hom-pointed-arrow =
    preserves-point-pointed-map
      ( right-pointed-map-span-diagram-hom-pointed-arrow)

  span-hom-pointed-arrow :
    pointed-span l1 B X
  pr1 span-hom-pointed-arrow =
    A
  pr1 (pr2 span-hom-pointed-arrow) =
    left-pointed-map-span-diagram-hom-pointed-arrow
  pr2 (pr2 span-hom-pointed-arrow) =
    right-pointed-map-span-diagram-hom-pointed-arrow

  span-diagram-hom-pointed-arrow : pointed-span-diagram l2 l3 l1
  pr1 span-diagram-hom-pointed-arrow =
    domain-span-diagram-hom-pointed-arrow
  pr1 (pr2 span-diagram-hom-pointed-arrow) =
    codomain-span-diagram-hom-pointed-arrow
  pr2 (pr2 span-diagram-hom-pointed-arrow) =
    span-hom-pointed-arrow
```

## See also

- [Transposition of pointed span diagrams](structured-types.transposition-pointed-span-diagrams.md)
