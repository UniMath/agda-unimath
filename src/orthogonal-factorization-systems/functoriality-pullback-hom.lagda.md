# Functoriality of the pullback-hom

```agda
module orthogonal-factorization-systems.functoriality-pullback-hom where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.bicomposition-functions
open import foundation.composition-algebra
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-morphisms-arrows
open import foundation.functoriality-pullbacks
open import foundation.homotopies
open import foundation.homotopies-morphisms-arrows
open import foundation.homotopies-morphisms-cospan-diagrams
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.morphisms-cospan-diagrams
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.retracts-of-arrows
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-composition

open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

The construction of the
[pullback-hom](orthogonal-factorization-systems.pullback-hom.md) is functorial.
I.e., we have a functorial action on pairs of
[morphisms of arrows](foundation.morphisms-arrows.md)

```text
  (α : f' ⇒ f, β : g ⇒ g') ↦ α ⋔ β : (f ⋔ g) ⇒ (f' ⋔ g')
```

We construct this action as the restriction of a more general action on
morphisms of _exponentiated cospan diagrams_ of the form:

```text
            - ∘ f           g ∘ -
   (B → Y) ------> (A → Y) <------ (A → X)
      |               |               |
      |               |               |
      ∨     - ∘ f'    ∨    g' ∘ -     ∨
  (B' → Y') ----> (A' → Y') <---- (A' → X').
```

In general, such morphisms need not necessarily come from pairs of morphisms of
the underlying arrows.

This gives us a commuting triangle of functors

```text
  [pairs of arrows of types] ---> [exponentiated cospan diagrams]
                     \                 /
                      \               /
                       ∨             ∨
                      [arrows of types]
```

where the functorial action of the pullback-hom on arrows is the left vertical
arrow.

### Functoriality of pullback-homs on exponentiated cospan diagrams

By [functoriality of pullbacks](foundation.functoriality-pullbacks.md), there is
a functor that maps cospan diagrams of the form

```text
           - ∘ f           g ∘ -
  (B → Y) ------> (A → Y) <------ (A → X)
```

to the type of [morphisms of arrows](foundation.morphisms-arrows.md) from `f` to
`g`

```text
  f ⇒ g -------> A → X
    | ⌟            |
    |              | g ∘ -
    ∨              ∨
  B → Y -------> A → Y.
          - ∘ f
```

For every morphism of cospan diagrams of this form

```text
            - ∘ f           g ∘ -
   (B → Y) ------> (A → Y) <------ (A → X)
      |               |               |
      |               |               |
      ∨     - ∘ f'    ∨    g' ∘ -     ∨
  (B' → Y') ----> (A' → Y') <---- (A' → X')
```

we thus have a commuting cube given by the functorial action of pullbacks

```text
                 f ⇒ g -----------> A → X
                /  | ⌟             /  |
              /    |             /    |
            ∨      |           ∨      |
      f' ⇒ g' ---------> A' → X'      |
         | ⌟       ∨        |         ∨
         |       B → Y ---- | ----> A → Y
         |      /           |      /
         |    /             |    /
         ∨  ∨               ∨  ∨
      B' → Y' ---------> A' → Y'.
```

This is the
{{#concept "functorial action of pullback-homs on exponentiated cospan diagrams"}}.

### Functoriality of pullback-homs on pairs of morphisms of arrows

There is a bifunctor mapping pairs of arrows to cospan diagrams of the form
described above. This bifunctor is contravariant in the left argument and
covariant in the right. I.e., a pair of morphisms of arrows `f' ⇒ f` and
`g ⇒ g'` gives a morphism of cospan diagrams

```text
            - ∘ f           g ∘ -
   (B → Y) ------> (A → Y) <------ (A → X)
      |               |               |
      |               |               |
      ∨     - ∘ f'    ∨    g' ∘ -     ∨
  (B' → Y') ----> (A' → Y') <---- (A' → X')
```

that is given componentwise by
[bicomposition of functions](foundation.bicomposition-functions.md).

Restricting along this bifunctor, the functorial action of pullbacks extends to
a bifunctorial action that we call the
{{#concept "bifunctoriality of the pullback-hom" Disambiguation="on types"}}.

Given a pair of maps `f` and `g`, the pullback-hom produces a new map
`f ⋔ g : (B → X) → (f ⇒ g)`, and given morphisms of arrows `f' ⇒ f` and
`g ⇒ g'`, we obtain a morphism of pullback-hom arrows

```text
     (B → X) -----> (B' → X')
        |               |
  f ⋔ g |               | f' ⋔ g'
        ∨               ∨
     (f ⇒ g) -----> (f' ⇒ g').
```

## Definitions

### Functorial action on maps of the pullback-hom

```agda
module _
  {l11 l12 l13 l14 l21 l22 l23 l24 : Level}
  {A1 : UU l11} {B1 : UU l12} {X1 : UU l13} {Y1 : UU l14}
  {A2 : UU l21} {B2 : UU l22} {X2 : UU l23} {Y2 : UU l24}
  (f1 : A1 → B1) (g1 : X1 → Y1)
  (f2 : A2 → B2) (g2 : X2 → Y2)
  where

  map-pullback-hom :
    hom-cospan-diagram
      ( cospan-diagram-hom-arrow f2 g2)
      ( cospan-diagram-hom-arrow f1 g1) →
    hom-arrow f2 g2 →
    hom-arrow f1 g1
  map-pullback-hom =
    map-pullback-cone
      ( cospan-diagram-hom-arrow f2 g2)
      ( cospan-diagram-hom-arrow f1 g1)
      ( pullback-cone-hom-arrow-pullback-hom f2 g2)
      ( pullback-cone-hom-arrow-pullback-hom f1 g1)
```
