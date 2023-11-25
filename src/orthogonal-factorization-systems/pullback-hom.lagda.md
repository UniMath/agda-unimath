# The pullback-hom

```agda
module orthogonal-factorization-systems.pullback-hom where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibered-maps
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.pullbacks
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import orthogonal-factorization-systems.lifting-squares
```

</details>

## Idea

The **pullback-hom** or **pullback-power** of two maps `f : A → B` and
`g : X → Y`, is the [gap map](foundation.pullbacks.md) of the
[commuting square](foundation-core.commuting-squares-of-maps.md):

```text
             - ∘ f
      B → X -------> A → X
        |              |
  g ∘ - |              | g ∘ -
        V              V
      B → Y -------> A → Y.
             - ∘ f
```

The pullback of `- ∘ f` and `g ∘ -` can be understood as the type of
[morphisms of arrows](foundation.morphisms-arrows.md) from `f` to `g`, while the
domain of the pullback-hom is the type `B → X` of diagonal fillers for morphisms
of arrows from `f` to `g`. The pullback-hom is therefore closely related to
[lifting conditions](orthogonal-factorization-systems.mere-lifting-properties.md)
and
[orthogonality conditions](orthogonal-factorization-systems.orthogonal-maps.md):
The pullback-hom of `f` and `g` is an
[equivalence](foundation-core.equivalences.md) if and only if `f` is left
orthogonal to `g`, while the pullback-hom of `f` and `g` is
[surjective](foundation.surjective-maps.md) if and only if `f` satisfies the
left lifting property to `g`.

There are two common ways to denote the pullback-hom: Some authors use `f ⋔ g`,
while other authors use `⟨f , g⟩`. Both notations can be used, depending on what
perspective of the pullback-hom is emphasized. The pitchfork-notation `f ⋔ g` is
used more often in settings where a lifting property of `f` and `g` is
emphasized, while the hom-notation `⟨f , g⟩` is used when the pullback-hom is
thought of in terms of hom-sets. The latter notation is useful for instance, if
one wants to emphasize an adjoint relation between the pullback-hom and the
pushout-product:

```text
  ⟨f □ g , h⟩ ＝ ⟨f , ⟨g , h⟩⟩.
```

## Definitions

### The codomain of the pullback-hom

```agda
type-standard-pullback-hom :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
type-standard-pullback-hom {A = A} {Y = Y} f g =
  standard-pullback (precomp f Y) (postcomp A g)
```

#### The standard pullback-hom type is equivalent to the type of fibered maps

**Proof:** The equivalence is a single application of
[function extensionality](foundation.function-extensionality.md).

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  equiv-fibered-map-type-standard-pullback-hom :
    type-standard-pullback-hom f g ≃ fibered-map f g
  equiv-fibered-map-type-standard-pullback-hom =
    equiv-tot (λ _ → equiv-tot (λ _ → equiv-funext))

  equiv-type-standard-pullback-hom-fibered-map :
    fibered-map f g ≃ type-standard-pullback-hom f g
  equiv-type-standard-pullback-hom-fibered-map =
    inv-equiv equiv-fibered-map-type-standard-pullback-hom

  map-fibered-map-type-standard-pullback-hom :
    type-standard-pullback-hom f g → fibered-map f g
  map-fibered-map-type-standard-pullback-hom =
    map-equiv equiv-fibered-map-type-standard-pullback-hom

  map-type-standard-pullback-hom-fibered-map :
    fibered-map f g → type-standard-pullback-hom f g
  map-type-standard-pullback-hom-fibered-map =
    map-equiv equiv-type-standard-pullback-hom-fibered-map
```

Below are basic definitions related to the pullback property of the type of
fibered maps.

```agda
  cone-standard-pullback-hom :
    cone (precomp f Y) (postcomp A g) (type-standard-pullback-hom f g)
  cone-standard-pullback-hom =
    cone-standard-pullback (precomp f Y) (postcomp A g)

  cone-pullback-hom :
    cone (precomp f Y) (postcomp A g) (fibered-map f g)
  cone-pullback-hom =
    cone-map
      ( precomp f Y)
      ( postcomp A g)
      ( cone-standard-pullback (precomp f Y) (postcomp A g))
      ( map-type-standard-pullback-hom-fibered-map)

  gap-standard-pullback-hom :
    {l : Level} {C : UU l} →
    cone (precomp f Y) (postcomp A g) C → C → type-standard-pullback-hom f g
  gap-standard-pullback-hom = gap (precomp f Y) (postcomp A g)

  gap-pullback-hom :
    {l : Level} {C : UU l} →
    cone (precomp f Y) (postcomp A g) C → C → fibered-map f g
  gap-pullback-hom c x =
    map-fibered-map-type-standard-pullback-hom (gap-standard-pullback-hom c x)

  is-pullback-fibered-map :
    is-pullback (precomp f Y) (postcomp A g) (cone-pullback-hom)
  is-pullback-fibered-map =
    is-equiv-map-equiv equiv-type-standard-pullback-hom-fibered-map

  universal-property-pullback-fibered-map :
    {l : Level} →
    universal-property-pullback l
      ( precomp f Y) (postcomp A g) (cone-pullback-hom)
  universal-property-pullback-fibered-map =
    universal-property-pullback-is-pullback
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom)
      ( is-pullback-fibered-map)
```

### The pullback-hom map

The pullback-hom `f ⋔ g` is the map `(B → X) → fibered-map f g`, that takes a
diagonal map `j` from the codomain of `f` to the domain of `g` to the fibered
map

```text
        j ∘ f
    A --------> X
    |           |
  f | refl-htpy | g
    v           v
    B --------> Y.
        g ∘ j
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  pullback-hom : (B → X) → fibered-map f g
  pullback-hom = gap-pullback-hom f g (postcomp B g , precomp f X , refl-htpy)

  infix 30 _⋔_
  _⋔_ = pullback-hom
```

The symbol `⋔` is the [pitchfork](https://codepoints.net/U+22D4) (agda-input:
`\pitchfork`).

## Properties

### The fibers of the pullback-hom

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : fibered-map f g)
  where

  inv-compute-fiber-pullback-hom :
    fiber (pullback-hom f g) h ≃ lifting-square-fibered-map f g h
  inv-compute-fiber-pullback-hom =
    equiv-tot
      ( λ j →
        ( equiv-Σ _
          ( equiv-inv-htpy (j ∘ f) (map-total-fibered-map f g h))
          ( λ E →
            equiv-Σ _
              ( equiv-inv-htpy (g ∘ j) (map-base-fibered-map f g h))
              ( λ L →
                ( equiv-concat-htpy'
                  ( inv-htpy L ·r f)
                  ( λ x →
                    ap
                      ( is-map-over-map-total-fibered-map f g h x ∙_)
                      ( inv-htpy-left-whisk-inv-htpy g E x))) ∘e
                ( equiv-right-transpose-htpy-concat
                  ( inv-htpy (L ·r f))
                  ( g ·l E)
                  ( is-map-over-map-total-fibered-map f g h)) ∘e
                ( equiv-left-transpose-htpy-concat'
                  ( g ·l E)
                  ( L ·r f)
                  ( is-map-over-map-total-fibered-map f g h))))) ∘e
        ( equiv-left-swap-Σ) ∘e
        ( extensionality-fibered-map f g (pullback-hom f g j) h))

  compute-fiber-pullback-hom :
    lifting-square-fibered-map f g h ≃ fiber (pullback-hom f g) h
  compute-fiber-pullback-hom = inv-equiv inv-compute-fiber-pullback-hom
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}

## External links

- [Pullback-power](https://ncatlab.org/nlab/show/pullback+power) at the $n$Lab

A wikidata identifier for this concept is unavailable.

## References

- Emily Riehl and Dominic Verity. _Elements of `∞`-category theory_. Cambridge
  Studies in Advanced Mathematics 194. Cambridge University Press,
  Cambridge, 2022.
  [doi:10.1017/9781108936880](https://doi.org/10.1017/9781108936880). ISBN:
  978-1-108-83798-9.
