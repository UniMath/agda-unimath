# Spans of types

```agda
module foundation.spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
```

</details>

## Idea

A {{#concept "binary span"}} is a [pair](foundation.dependent-pair-types.md) of functions with a common domain, i.e., it is a
diagram of the form

```text
  A <----- S -----> B.
```

More precisely, a {{#concept "binary span with fixed domain and codomain"}} from `A` to `B` consists of a type `S` and two
maps `f : S → A` and `g : S → B`. In this case, the types `A` and `B` are also
referred to as the {{#concept "domain" Disambiguation="binary span"}} and {{#concept "codomain" Disambiguation="binary span"}} of the span, respectively, and
the type `S` is referred to as the {{#concept "spanning type" Disambiguation="binary span"}} of the span.

We also consider the notion of {{#concept "binary span"}}, which consists of two
types `A` and `B` and a binary span with fixed domain and codomain from `A` to `B`.

In [`foundation.binary-type-duality`](foundation.binary-type-duality.md) we show that [binary relations](foundation.binary-relations.md) are equivalently described as spans of types.
  
## Definitions

### (Binary) spans with fixed domain and codomain

```agda
span-fixed-domain-codomain :
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
span-fixed-domain-codomain l A B =
  Σ (UU l) (λ X → (X → A) × (X → B))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (c : span-fixed-domain-codomain l3 A B)
  where

  spanning-type-span-fixed-domain-codomain : UU l3
  spanning-type-span-fixed-domain-codomain = pr1 c

  left-map-span-fixed-domain-codomain :
    spanning-type-span-fixed-domain-codomain → A
  left-map-span-fixed-domain-codomain = pr1 (pr2 c)

  right-map-span-fixed-domain-codomain :
    spanning-type-span-fixed-domain-codomain → B
  right-map-span-fixed-domain-codomain = pr2 (pr2 c)
```

### Identity spans with fixed domain and codomain

```agda
module _
  {l1 : Level} {X : UU l1}
  where

  id-span-fixed-domain-codomain : span-fixed-domain-codomain l1 X X
  pr1 id-span-fixed-domain-codomain = X
  pr1 (pr2 id-span-fixed-domain-codomain) = id
  pr2 (pr2 id-span-fixed-domain-codomain) = id
```

### (Binary) spans

```agda
span : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
span l1 l2 l3 =
  Σ (UU l1) (λ A → Σ (UU l2) (λ B → span-fixed-domain-codomain l3 A B))

module _
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  where

  make-span :
    (S → A) → (S → B) → span l2 l3 l1
  pr1 (make-span f g) = A
  pr1 (pr2 (make-span f g)) = B
  pr1 (pr2 (pr2 (make-span f g))) = S
  pr1 (pr2 (pr2 (pr2 (make-span f g)))) = f
  pr2 (pr2 (pr2 (pr2 (make-span f g)))) = g

module _
  {l1 l2 l3 : Level} (s : span l1 l2 l3)
  where

  domain-span : UU l1
  domain-span = pr1 s

  codomain-span : UU l2
  codomain-span = pr1 (pr2 s)

  span-fixed-domain-codomain-span :
    span-fixed-domain-codomain l3 domain-span codomain-span
  span-fixed-domain-codomain-span = pr2 (pr2 s)

  spanning-type-span : UU l3
  spanning-type-span =
    spanning-type-span-fixed-domain-codomain span-fixed-domain-codomain-span

  left-map-span : spanning-type-span → domain-span
  left-map-span =
    left-map-span-fixed-domain-codomain span-fixed-domain-codomain-span

  right-map-span : spanning-type-span → codomain-span
  right-map-span =
    right-map-span-fixed-domain-codomain span-fixed-domain-codomain-span
```

### Constant spans

```agda
module _
  {l1 : Level}
  where

  constant-span : UU l1 → span l1 l1 l1
  pr1 (constant-span X) = X
  pr1 (pr2 (constant-span X)) = X
  pr2 (pr2 (constant-span X)) = id-span-fixed-domain-codomain
```

### The span obtained from a morphism of arrows

Given maps `f : A → B` and `g : X → Y` and a morphism of arrows `α : f → g`, the span associated to `α` is the span

```text
       f       α₀
  B <----- A -----> X.
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α : hom-arrow f g)
  where

  domain-span-hom-arrow : UU l2
  domain-span-hom-arrow = B

  codomain-span-hom-arrow : UU l3
  codomain-span-hom-arrow = X

  spanning-type-hom-arrow : UU l1
  spanning-type-hom-arrow = A

  left-map-span-hom-arrow : spanning-type-hom-arrow → domain-span-hom-arrow
  left-map-span-hom-arrow = f

  right-map-span-hom-arrow : spanning-type-hom-arrow → codomain-span-hom-arrow
  right-map-span-hom-arrow = map-domain-hom-arrow f g α

  span-fixed-domain-codomain-hom-arrow :
    span-fixed-domain-codomain l1 B X
  pr1 span-fixed-domain-codomain-hom-arrow = A
  pr1 (pr2 span-fixed-domain-codomain-hom-arrow) = left-map-span-hom-arrow
  pr2 (pr2 span-fixed-domain-codomain-hom-arrow) = right-map-span-hom-arrow

  span-hom-arrow : span l2 l3 l1
  pr1 span-hom-arrow = domain-span-hom-arrow
  pr1 (pr2 span-hom-arrow) = codomain-span-hom-arrow
  pr2 (pr2 span-hom-arrow) = span-fixed-domain-codomain-hom-arrow
```

### The opposite of a span with fixed domain and codomain

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  opposite-span-fixed-domain-codomain :
    span-fixed-domain-codomain l3 A B →
    span-fixed-domain-codomain l3 B A
  pr1 (opposite-span-fixed-domain-codomain s) =
    spanning-type-span-fixed-domain-codomain s
  pr1 (pr2 (opposite-span-fixed-domain-codomain s)) =
    right-map-span-fixed-domain-codomain s
  pr2 (pr2 (opposite-span-fixed-domain-codomain s)) =
    left-map-span-fixed-domain-codomain s
```

### The opposite of a span

```agda
module _
  {l1 l2 l3 : Level} (s : span l1 l2 l3)
  where

  opposite-span : span l2 l1 l3
  pr1 opposite-span =
    codomain-span s
  pr1 (pr2 opposite-span) =
    domain-span s
  pr2 (pr2 opposite-span) =
    opposite-span-fixed-domain-codomain (span-fixed-domain-codomain-span s)
```

## See also

- [Cospans](foundation.cospans.md)
- [Extensions of spans](foundation.extensions-spans.md)
- [Spans of families of types](foundation.spans-families-of-types.md)
