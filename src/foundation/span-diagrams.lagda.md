# Span diagrams

```agda
open import foundation.function-extensionality-axiom

module foundation.span-diagrams
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows funext
open import foundation.spans
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "(binary) span diagram" Agda=span-diagram}} is a diagram of the
form

```text
       f       g
  A <----- S -----> B.
```

In other words, a span diagram consists of two types `A` and `B` and a
[span](foundation.spans.md) from `A` to `B`.

We disambiguate between [spans](foundation.spans.md) and span diagrams. We
consider spans from `A` to `B` to be _morphisms_ from `A` to `B` in the category
of types and spans between them, whereas we consider span diagrams to be
_objects_ in the category of diagrams of types of the form `* <---- * ----> *`.
Conceptually there is a subtle, but important distinction between spans and span
diagrams. In [binary type duality](foundation.binary-type-duality.md) we show a
span from `A` to `B` is [equivalently](foundation-core.equivalences.md)
described as a [binary relation](foundation.binary-relations.md) from `A` to
`B`. On the other hand, span diagrams are more suitable for functorial
operations that take "spans" as input, but for which the functorial action takes
a natural transformation, i.e., a morphism of span diagrams, as input. Examples
of this kind include [pushouts](synthetic-homotopy-theory.pushouts.md).

### (Binary) span diagrams

```agda
span-diagram : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
span-diagram l1 l2 l3 =
  Σ (UU l1) (λ A → Σ (UU l2) (λ B → span l3 A B))

module _
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  where

  make-span-diagram :
    (S → A) → (S → B) → span-diagram l2 l3 l1
  pr1 (make-span-diagram f g) = A
  pr1 (pr2 (make-span-diagram f g)) = B
  pr1 (pr2 (pr2 (make-span-diagram f g))) = S
  pr1 (pr2 (pr2 (pr2 (make-span-diagram f g)))) = f
  pr2 (pr2 (pr2 (pr2 (make-span-diagram f g)))) = g

module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  domain-span-diagram : UU l1
  domain-span-diagram = pr1 𝒮

  codomain-span-diagram : UU l2
  codomain-span-diagram = pr1 (pr2 𝒮)

  span-span-diagram :
    span l3 domain-span-diagram codomain-span-diagram
  span-span-diagram = pr2 (pr2 𝒮)

  spanning-type-span-diagram : UU l3
  spanning-type-span-diagram =
    spanning-type-span span-span-diagram

  left-map-span-diagram : spanning-type-span-diagram → domain-span-diagram
  left-map-span-diagram =
    left-map-span span-span-diagram

  right-map-span-diagram : spanning-type-span-diagram → codomain-span-diagram
  right-map-span-diagram =
    right-map-span span-span-diagram
```

### The span diagram obtained from a morphism of arrows

Given maps `f : A → B` and `g : X → Y` and a morphism of arrows `α : f → g`, the
span diagram associated to `α` is the span diagram

```text
       f       α₀
  B <----- A -----> X.
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  domain-span-diagram-hom-arrow : UU l2
  domain-span-diagram-hom-arrow = B

  codomain-span-diagram-hom-arrow : UU l3
  codomain-span-diagram-hom-arrow = X

  spanning-type-hom-arrow : UU l1
  spanning-type-hom-arrow = A

  left-map-span-diagram-hom-arrow :
    spanning-type-hom-arrow → domain-span-diagram-hom-arrow
  left-map-span-diagram-hom-arrow = f

  right-map-span-diagram-hom-arrow :
    spanning-type-hom-arrow → codomain-span-diagram-hom-arrow
  right-map-span-diagram-hom-arrow = map-domain-hom-arrow f g α

  span-hom-arrow :
    span l1 B X
  pr1 span-hom-arrow = A
  pr1 (pr2 span-hom-arrow) = left-map-span-diagram-hom-arrow
  pr2 (pr2 span-hom-arrow) = right-map-span-diagram-hom-arrow

  span-diagram-hom-arrow : span-diagram l2 l3 l1
  pr1 span-diagram-hom-arrow = domain-span-diagram-hom-arrow
  pr1 (pr2 span-diagram-hom-arrow) = codomain-span-diagram-hom-arrow
  pr2 (pr2 span-diagram-hom-arrow) = span-hom-arrow
```

## See also

- [Cospan diagrams](foundation.cospan-diagrams.md)
- [Diagonal span diagrams](foundation.diagonal-span-diagrams.md)
- [Extensions of span diagrams](foundation.operations-span-diagrams.md)
- [Kernel span diagrams of maps](foundation.kernel-span-diagrams-of-maps.md)
- [Spans of families of types](foundation.spans-families-of-types.md)
- [Transposition of span diagrams](foundation.transposition-span-diagrams.md)
