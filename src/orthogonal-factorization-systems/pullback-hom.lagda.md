# The pullback-hom

```agda
module orthogonal-factorization-systems.pullback-hom where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.cones-over-cospan-diagrams
open import foundation.cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.functoriality-morphisms-arrows
open import foundation.higher-homotopies-morphisms-arrows
open import foundation.homotopies
open import foundation.homotopies-morphisms-arrows
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.postcomposition-functions
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.pullback-cones
open import foundation.pullbacks
open import foundation.retractions
open import foundation.sections
open import foundation.standard-pullbacks
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universal-property-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
```

</details>

## Idea

The {{#concept "pullback-hom" Agda=pullback-hom}} or
{{#concept "pullback-power" Agda=pullback-hom}} of two maps `f : A → B` and
`g : X → Y`, is the [gap map](foundation.pullbacks.md) of the
[commuting square](foundation-core.commuting-squares-of-maps.md):

```text
             - ∘ f
      B → X -------> A → X
        |              |
  g ∘ - |              | g ∘ -
        ∨              ∨
      B → Y -------> A → Y.
             - ∘ f
```

More explicitly, the pullback of `- ∘ f` and `g ∘ -` is the type of
[morphisms of arrows](foundation.morphisms-arrows.md) from `f` to `g`, while the
domain of the pullback-hom is the type `B → X` of diagonal fillers for morphisms
of arrows from `f` to `g`. The pullback-hom can therefore be described as a map

```text
  pullback-hom f g : (B → X) → hom-arrow f g
```

This map takes a map `j : B → X` as in the diagram

```text
    A       X
    |     ∧ |
  f |  j/   | g
    ∨ /     ∨
    B       Y
```

to the [morphism of arrows](foundation.morphisms-arrows.md) from `f` to `g` as
in the diagram

```text
         j ∘ f
    A ----------> X
    |             |
  f |  refl-htpy  | g
    ∨             ∨
    B ----------> Y.
         g ∘ j
```

The [fibers](foundation-core.fibers-of-maps.md) of the pullback-hom are
[lifting squares](orthogonal-factorization-systems.lifting-structures-on-squares.md).
The pullback-hom is therefore a fundamental operation in the study of
[lifting conditions](orthogonal-factorization-systems.mere-lifting-properties.md)
and
[orthogonality conditions](orthogonal-factorization-systems.orthogonal-maps.md):
The pullback-hom of `f` and `g` is an
[equivalence](foundation-core.equivalences.md) if and only if `f` is left
orthogonal to `g`, while the pullback-hom of `f` and `g` is
[surjective](foundation.surjective-maps.md) if and only if `f` satisfies the
left lifting property to `g`.

**Notation.** There are two common ways to denote the pullback-hom: Some authors
use `f ⋔ g`, while other authors use `⟨f , g⟩`. Both notations can be used,
depending on what perspective of the pullback-hom is emphasized. The
pitchfork-notation `f ⋔ g` is used more often in settings where a lifting
property of `f` and `g` is emphasized, while the hom-notation `⟨f , g⟩` is used
when the pullback-hom is thought of in terms of hom-sets. The latter notation is
useful for instance, if one wants to emphasize an adjoint relation between the
pullback-hom and the
[pushout-product](synthetic-homotopy-theory.pushout-products.md):

```text
  ⟨f □ g , h⟩ ＝ ⟨f , ⟨g , h⟩⟩.
```

## Definitions

### The pullback-hom

The pullback-hom `f ⋔ g` is the map `(B → X) → hom-arrow f g`, that takes a
diagonal map `j` from the codomain of `f` to the domain of `g` to the morphism
of arrows

```text
         j ∘ f
    A ----------> X
    |             |
  f |  refl-htpy  | g
    ∨             ∨
    B ----------> Y.
         g ∘ j
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  map-domain-pullback-hom : (B → X) → A → X
  map-domain-pullback-hom j = j ∘ f

  map-codomain-pullback-hom : (B → X) → B → Y
  map-codomain-pullback-hom j = g ∘ j

  coh-pullback-hom :
    (j : B → X) →
    coherence-hom-arrow f g
      ( map-domain-pullback-hom j)
      ( map-codomain-pullback-hom j)
  coh-pullback-hom j = refl-htpy

  pullback-hom : (B → X) → hom-arrow f g
  pullback-hom j =
    ( map-domain-pullback-hom j ,
      map-codomain-pullback-hom j ,
      coh-pullback-hom j)

  infix 30 _⋔_
  _⋔_ = pullback-hom
```

The symbol `⋔` is the [pitchfork](https://codepoints.net/U+22D4) (agda-input:
`\pitchfork`).

### The cone structure on the codomain of the pullback-hom

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  left-projection-hom-arrow-pullback-hom : hom-arrow f g → B → Y
  left-projection-hom-arrow-pullback-hom = map-codomain-hom-arrow f g

  right-projection-hom-arrow-pullback-hom : hom-arrow f g → A → X
  right-projection-hom-arrow-pullback-hom = map-domain-hom-arrow f g

  coherence-square-cone-hom-arrow-pullback-hom :
    coherence-square-maps
      ( right-projection-hom-arrow-pullback-hom)
      ( left-projection-hom-arrow-pullback-hom)
      ( postcomp A g)
      ( precomp f Y)
  coherence-square-cone-hom-arrow-pullback-hom h = eq-htpy (coh-hom-arrow f g h)

  cone-hom-arrow-pullback-hom :
    cone (precomp f Y) (postcomp A g) (hom-arrow f g)
  pr1 cone-hom-arrow-pullback-hom = left-projection-hom-arrow-pullback-hom
  pr1 (pr2 cone-hom-arrow-pullback-hom) =
    right-projection-hom-arrow-pullback-hom
  pr2 (pr2 cone-hom-arrow-pullback-hom) =
    coherence-square-cone-hom-arrow-pullback-hom
```

### The standard pullback of the defining cospan of the pullback-hom

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  type-standard-pullback-hom : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  type-standard-pullback-hom =
    standard-pullback (precomp f Y) (postcomp A g)

  module _
    (h : type-standard-pullback-hom)
    where

    map-domain-standard-pullback-hom : A → X
    map-domain-standard-pullback-hom = pr1 (pr2 h)

    map-codomain-standard-pullback-hom : B → Y
    map-codomain-standard-pullback-hom = pr1 h

    eq-coh-standard-pullback-hom :
      precomp f Y map-codomain-standard-pullback-hom ＝
      postcomp A g map-domain-standard-pullback-hom
    eq-coh-standard-pullback-hom = pr2 (pr2 h)

    coh-standard-pullback-hom :
      precomp f Y map-codomain-standard-pullback-hom ~
      postcomp A g map-domain-standard-pullback-hom
    coh-standard-pullback-hom = htpy-eq eq-coh-standard-pullback-hom
```

### The cone of the diagram defining the pullback-hom

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  cone-pullback-hom : cone (precomp f Y) (postcomp A g) (B → X)
  cone-pullback-hom = (postcomp B g , precomp f X , refl-htpy)

  gap-pullback-hom : (B → X) → type-standard-pullback-hom f g
  gap-pullback-hom = gap (precomp f Y) (postcomp A g) cone-pullback-hom
```

### The equivalence of the codomain of the pullback-hom with the standard pullback

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  map-compute-pullback-hom :
    hom-arrow f g → type-standard-pullback-hom f g
  map-compute-pullback-hom h =
    ( map-codomain-hom-arrow f g h ,
      map-domain-hom-arrow f g h ,
      eq-htpy (coh-hom-arrow f g h))

  map-inv-compute-pullback-hom :
    type-standard-pullback-hom f g → hom-arrow f g
  map-inv-compute-pullback-hom h =
    ( map-domain-standard-pullback-hom f g h ,
      map-codomain-standard-pullback-hom f g h ,
      coh-standard-pullback-hom f g h)

  is-section-map-inv-compute-pullback-hom :
    is-section map-compute-pullback-hom map-inv-compute-pullback-hom
  is-section-map-inv-compute-pullback-hom h =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber
        ( is-retraction-eq-htpy (eq-coh-standard-pullback-hom f g h)))

  is-retraction-map-inv-compute-pullback-hom :
    is-retraction map-compute-pullback-hom map-inv-compute-pullback-hom
  is-retraction-map-inv-compute-pullback-hom h =
    eq-pair-eq-fiber
      ( eq-pair-eq-fiber (is-section-eq-htpy (coh-hom-arrow f g h)))

  is-equiv-map-compute-pullback-hom :
    is-equiv map-compute-pullback-hom
  is-equiv-map-compute-pullback-hom =
    is-equiv-is-invertible
      ( map-inv-compute-pullback-hom)
      ( is-section-map-inv-compute-pullback-hom)
      ( is-retraction-map-inv-compute-pullback-hom)

  is-equiv-map-inv-compute-pullback-hom :
    is-equiv map-inv-compute-pullback-hom
  is-equiv-map-inv-compute-pullback-hom =
    is-equiv-is-invertible
      ( map-compute-pullback-hom)
      ( is-retraction-map-inv-compute-pullback-hom)
      ( is-section-map-inv-compute-pullback-hom)

  compute-pullback-hom : hom-arrow f g ≃ type-standard-pullback-hom f g
  pr1 compute-pullback-hom = map-compute-pullback-hom
  pr2 compute-pullback-hom = is-equiv-map-compute-pullback-hom

  inv-compute-pullback-hom : type-standard-pullback-hom f g ≃ hom-arrow f g
  pr1 inv-compute-pullback-hom = map-inv-compute-pullback-hom
  pr2 inv-compute-pullback-hom = is-equiv-map-inv-compute-pullback-hom
```

### The commuting triangle of the pullback-hom and the gap map

We construct the homotopy witnessing that the triangle of maps

```text
                  (B → X)
                 /       \
  pullback-hom  /         \ gap
               ∨           ∨
     hom-arrow f g -----> type-standard-pullback-hom f g
```

commutes. The bottom map in this triangle is the underlying map of the
equivalence `hom-arrow f g ≃ type-stanard-pullback-hom f g` constructed above.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  triangle-pullback-hom :
    coherence-triangle-maps'
      ( gap-pullback-hom f g)
      ( gap (precomp f Y) (postcomp A g) (cone-hom-arrow' f g))
      ( pullback-hom f g)
  triangle-pullback-hom j =
    eq-pair-eq-fiber (eq-pair-eq-fiber (is-retraction-eq-htpy refl))
```

### The action on homotopies of the `pullback-hom`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) {j k : B → X} (H : j ~ k)
  where

  htpy-domain-htpy-hom-arrow-htpy :
    map-domain-pullback-hom f g j ~ map-domain-pullback-hom f g k
  htpy-domain-htpy-hom-arrow-htpy = H ·r f

  htpy-codomain-htpy-hom-arrow-htpy :
    map-codomain-pullback-hom f g j ~ map-codomain-pullback-hom f g k
  htpy-codomain-htpy-hom-arrow-htpy = g ·l H

  coh-htpy-hom-arrow-htpy :
    coherence-htpy-hom-arrow f g
      ( pullback-hom f g j)
      ( pullback-hom f g k)
      ( htpy-domain-htpy-hom-arrow-htpy)
      ( htpy-codomain-htpy-hom-arrow-htpy)
  coh-htpy-hom-arrow-htpy = inv-htpy right-unit-htpy

  htpy-hom-arrow-htpy :
    htpy-hom-arrow f g (pullback-hom f g j) (pullback-hom f g k)
  pr1 htpy-hom-arrow-htpy = htpy-domain-htpy-hom-arrow-htpy
  pr1 (pr2 htpy-hom-arrow-htpy) = htpy-codomain-htpy-hom-arrow-htpy
  pr2 (pr2 htpy-hom-arrow-htpy) = coh-htpy-hom-arrow-htpy
```

## Properties

### The cone of the pullback-hom is a pullback

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-pullback-cone-hom-arrow-pullback-hom :
    is-pullback
      ( precomp f Y)
      ( postcomp A g)
      ( cone-hom-arrow-pullback-hom f g)
  is-pullback-cone-hom-arrow-pullback-hom =
    is-equiv-map-compute-pullback-hom f g

  pullback-cone-hom-arrow-pullback-hom :
    pullback-cone (cospan-diagram-hom-arrow f g) (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pullback-cone-hom-arrow-pullback-hom =
    ( hom-arrow f g , cone-hom-arrow-pullback-hom f g) ,
    ( is-pullback-cone-hom-arrow-pullback-hom)

  universal-property-pullback-cone-hom-arrow-pullback-hom :
    universal-property-pullback
      ( precomp f Y)
      ( postcomp A g)
      ( cone-hom-arrow-pullback-hom f g)
  universal-property-pullback-cone-hom-arrow-pullback-hom =
    universal-property-pullback-is-pullback
      ( precomp f Y)
      ( postcomp A g)
      ( cone-hom-arrow-pullback-hom f g)
      ( is-pullback-cone-hom-arrow-pullback-hom)
```

### The action on homotopies at `refl-htpy` is the reflexivity homotopy of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {X : UU l2} {B : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) {j : B → X}
  where

  htpy-domain-compute-refl-htpy-hom-arrow-htpy :
    htpy-domain-htpy-hom-arrow-htpy f g (refl-htpy' j) ~
    htpy-domain-refl-htpy-hom-arrow f g (pullback-hom f g j)
  htpy-domain-compute-refl-htpy-hom-arrow-htpy = refl-htpy

  htpy-codomain-compute-refl-htpy-hom-arrow-htpy :
    htpy-codomain-htpy-hom-arrow-htpy f g (refl-htpy' j) ~
    htpy-codomain-refl-htpy-hom-arrow f g (pullback-hom f g j)
  htpy-codomain-compute-refl-htpy-hom-arrow-htpy = refl-htpy

  coh-compute-refl-htpy-hom-arrow-htpy :
    coherence-htpy-htpy-hom-arrow f g
      ( pullback-hom f g j)
      ( pullback-hom f g j)
      ( htpy-hom-arrow-htpy f g refl-htpy)
      ( refl-htpy-hom-arrow f g (pullback-hom f g j))
      ( htpy-domain-compute-refl-htpy-hom-arrow-htpy)
      ( htpy-codomain-compute-refl-htpy-hom-arrow-htpy)
  coh-compute-refl-htpy-hom-arrow-htpy = refl-htpy

  compute-refl-htpy-hom-arrow-htpy :
    htpy-htpy-hom-arrow f g
      ( pullback-hom f g j)
      ( pullback-hom f g j)
      ( htpy-hom-arrow-htpy f g refl-htpy)
      ( refl-htpy-hom-arrow f g (pullback-hom f g j))
  pr1 compute-refl-htpy-hom-arrow-htpy =
    htpy-domain-compute-refl-htpy-hom-arrow-htpy
  pr1 (pr2 compute-refl-htpy-hom-arrow-htpy) =
    htpy-codomain-compute-refl-htpy-hom-arrow-htpy
  pr2 (pr2 compute-refl-htpy-hom-arrow-htpy) =
    coh-compute-refl-htpy-hom-arrow-htpy
```

### Computing the pullback-hom of a composite

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {S : UU l5}
  (f : A → B) (g : X → Y) (h : Y → S)
  where

  map-domain-left-whisker-hom-arrow : hom-arrow f g → A → X
  map-domain-left-whisker-hom-arrow α = map-domain-hom-arrow f g α

  map-codomain-left-whisker-hom-arrow : hom-arrow f g → B → S
  map-codomain-left-whisker-hom-arrow α = h ∘ map-codomain-hom-arrow f g α

  coh-left-whisker-hom-arrow :
    (α : hom-arrow f g) →
    coherence-square-maps
      ( map-domain-left-whisker-hom-arrow α)
      ( f)
      ( h ∘ g)
      ( map-codomain-left-whisker-hom-arrow α)
  coh-left-whisker-hom-arrow α = h ·l (coh-hom-arrow f g α)

  left-whisker-hom-arrow :
    hom-arrow f g → hom-arrow f (h ∘ g)
  pr1 (left-whisker-hom-arrow α) = map-domain-left-whisker-hom-arrow α
  pr1 (pr2 (left-whisker-hom-arrow α)) = map-codomain-left-whisker-hom-arrow α
  pr2 (pr2 (left-whisker-hom-arrow α)) = coh-left-whisker-hom-arrow α

  compute-pullback-hom-comp-right :
    coherence-triangle-maps
      ( pullback-hom f (h ∘ g))
      ( left-whisker-hom-arrow)
      ( pullback-hom f g)
  compute-pullback-hom-comp-right = refl-htpy

module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {S : UU l5}
  (f : A → B) (g : X → Y) (h : S → A)
  where

  map-domain-right-whisker-hom-arrow : hom-arrow f g → S → X
  map-domain-right-whisker-hom-arrow α = map-domain-hom-arrow f g α ∘ h

  map-codomain-right-whisker-hom-arrow : hom-arrow f g → B → Y
  map-codomain-right-whisker-hom-arrow α = map-codomain-hom-arrow f g α

  coh-right-whisker-hom-arrow :
    (α : hom-arrow f g) →
    coherence-hom-arrow (f ∘ h) g
      ( map-domain-right-whisker-hom-arrow α)
      ( map-codomain-right-whisker-hom-arrow α)
  coh-right-whisker-hom-arrow α =
    coh-hom-arrow f g α ·r h

  right-whisker-hom-arrow :
    hom-arrow f g → hom-arrow (f ∘ h) g
  pr1 (right-whisker-hom-arrow α) = map-domain-right-whisker-hom-arrow α
  pr1 (pr2 (right-whisker-hom-arrow α)) = map-codomain-right-whisker-hom-arrow α
  pr2 (pr2 (right-whisker-hom-arrow α)) = coh-right-whisker-hom-arrow α

  compute-pullback-hom-comp-left :
    coherence-triangle-maps
      ( pullback-hom (f ∘ h) g)
      ( right-whisker-hom-arrow)
      ( pullback-hom f g)
  compute-pullback-hom-comp-left = refl-htpy
```

### Computing the fiber map between the vertical maps in the pullback-hom square

We have an equivalence of arrows

```text
                                      ~
      (Π (b : B), fiber g (h b)) ----------> fiber (g ∘ -) h
                  |                                 |
                  |                                 |
                  ∨                   ~             ∨
  (Π (a : A) → (fiber g (h (f a)))) ----> fiber (g ∘ -) (h ∘ f)
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  compute-map-fiber-vertical-pullback-hom :
    (h : B → Y) →
    equiv-arrow
      ( precomp-Π f (fiber g ∘ h))
      ( map-fiber-vertical-map-cone
        ( precomp f Y)
        ( postcomp A g)
        ( cone-pullback-hom f g)
        ( h))
  pr1 (compute-map-fiber-vertical-pullback-hom h) =
    compute-Π-fiber-postcomp B g h
  pr1 (pr2 (compute-map-fiber-vertical-pullback-hom h)) =
    compute-Π-fiber-postcomp A g (h ∘ f)
  pr2 (pr2 (compute-map-fiber-vertical-pullback-hom h)) H =
    eq-Eq-fiber
      ( postcomp A g)
      ( precomp f Y h)
      ( refl)
      ( coherence-eq-htpy-ap-precomp f (pr2 (map-distributive-Π-Σ H)))
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}

## External links

- [Pullback-power](https://ncatlab.org/nlab/show/pullback+power) at the $n$Lab

A wikidata identifier for this concept is unavailable.

## References

{{#bibliography}} {{#reference Rie22}}
