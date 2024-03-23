# Spans of types

```agda
module foundation.spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
```

</details>

## Idea

A {{#concept "binary span" Agda=span}} from `A` to `B` consists of a
{{#concept "spanning type" Disambiguation="binary span" Agda=spanning-type-span}}
`S` and a [pair](foundation.dependent-pair-types.md) of functions `f : S → A`
and `g : S → B`. The types `A` and `B` in the specification of a binary span are
also referred to as the {{#concept "domain" Disambiguation="binary span"}} and
{{#concept "codomain" Disambiguation="binary span"}} of the span, respectively.

In [`foundation.binary-type-duality`](foundation.binary-type-duality.md) we show
that [binary relations](foundation.binary-relations.md) are equivalently
described as spans of types.

We disambiguate between spans and [span diagrams](foundation.span-diagrams.md).
We consider spans from `A` to `B` to be _morphisms_ from `A` to `B` in the
category of types and spans between them, whereas we consider span diagrams to
be _objects_ in the category of diagrams of types of the form
`* <---- * ----> *`. Conceptually there is a subtle, but important distinction
between spans and span diagrams. As mentioned previously, a span from `A` to `B`
is equivalently described as a binary relation from `A` to `B`. On the other
hand, span diagrams are more suitable for functorial operations that take
"spans" as input, but for which the functorial action takes a natural
transformation, i.e., a morphism of span diagrams, as input. Examples of this
kind include [pushouts](synthetic-homotopy-theory.pushouts.md).

## Definitions

### (Binary) spans

```agda
span :
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2 ⊔ lsuc l)
span l A B = Σ (UU l) (λ X → (X → A) × (X → B))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (c : span l3 A B)
  where

  spanning-type-span : UU l3
  spanning-type-span = pr1 c

  left-map-span : spanning-type-span → A
  left-map-span = pr1 (pr2 c)

  right-map-span : spanning-type-span → B
  right-map-span = pr2 (pr2 c)
```

### Identity spans

```agda
module _
  {l1 : Level} {X : UU l1}
  where

  id-span : span l1 X X
  pr1 id-span = X
  pr1 (pr2 id-span) = id
  pr2 (pr2 id-span) = id
```

## See also

- [Binary type duality](foundation.binary-type-duality.md)
- [Cospans](foundation.cospans.md)
- [Span diagrams](foundation.span-diagrams.md)
- [Spans of families of types](foundation.spans-families-of-types.md)
- [Spans of pointed types](structured-types.pointed-spans.md)
