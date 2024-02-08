# Coherently invertible maps

```agda
module foundation-core.coherently-invertible-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.invertible-maps
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

A [(two-sided) inverse](foundation-core.invertible-maps.md) for a map
`f : A → B` is a map `g : B → A` equipped with
[homotopies](foundation-core.homotopies.md) ` f ∘ g ~ id` and `g ∘ f ~ id`. Such
data, however is [structure](foundation.structure.md) on the map `f`, and not
generally a [property](foundation-core.propositions.md). One way to make the
type of inverses into a property is by adding a single coherence condition
between the homotopies of the inverse, asking that the following diagram
commmutes

```text
               G ·r f
             ~~~~~~~~~~
  f ∘ g ∘ f             f.
             ~~~~~~~~~~
               f ·l H
```

We call such data a
{{# "coherently invertible map" Agda=coherently-invertible-map}}. I.e., a
coherently invertible map `f : A → B` is a map equipped with a two-sided inverse
and this additional coherence.

**Note.** Coherently invertible maps are also called
{{#concept "half adjoint equivalences"}}.

## Definition

### The predicate of being coherently invertible on maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  coherence-is-coherently-invertible :
    (f : A → B) (g : B → A) (G : f ∘ g ~ id) (H : g ∘ f ~ id) → UU (l1 ⊔ l2)
  coherence-is-coherently-invertible f g G H = G ·r f ~ f ·l H

  is-coherently-invertible : (A → B) → UU (l1 ⊔ l2)
  is-coherently-invertible f =
    Σ ( B → A)
      ( λ g →
        Σ (f ∘ g ~ id)
          ( λ G →
            Σ (g ∘ f ~ id)
              ( λ H → coherence-is-coherently-invertible f g G H)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-coherently-invertible f)
  where

  map-inv-is-coherently-invertible : B → A
  map-inv-is-coherently-invertible = pr1 H

  is-section-map-inv-is-coherently-invertible :
    f ∘ map-inv-is-coherently-invertible ~ id
  is-section-map-inv-is-coherently-invertible = pr1 (pr2 H)

  is-retraction-map-inv-is-coherently-invertible :
    map-inv-is-coherently-invertible ∘ f ~ id
  is-retraction-map-inv-is-coherently-invertible = pr1 (pr2 (pr2 H))

  coh-is-coherently-invertible :
    coherence-is-coherently-invertible f
      ( map-inv-is-coherently-invertible)
      ( is-section-map-inv-is-coherently-invertible)
      ( is-retraction-map-inv-is-coherently-invertible)
  coh-is-coherently-invertible = pr2 (pr2 (pr2 H))

  is-invertible-is-coherently-invertible : is-invertible f
  pr1 is-invertible-is-coherently-invertible =
    map-inv-is-coherently-invertible
  pr1 (pr2 is-invertible-is-coherently-invertible) =
    is-section-map-inv-is-coherently-invertible
  pr2 (pr2 is-invertible-is-coherently-invertible) =
    is-retraction-map-inv-is-coherently-invertible

  section-map-is-coherently-invertible : section f
  pr1 section-map-is-coherently-invertible =
    map-inv-is-coherently-invertible
  pr2 section-map-is-coherently-invertible =
    is-section-map-inv-is-coherently-invertible

  retraction-map-is-coherently-invertible : retraction f
  pr1 retraction-map-is-coherently-invertible =
    map-inv-is-coherently-invertible
  pr2 retraction-map-is-coherently-invertible =
    is-retraction-map-inv-is-coherently-invertible
```

We will show that `is-coherently-invertible` is a proposition in
[`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).

### The type of coherently invertible maps

```agda
coherently-invertible-map : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
coherently-invertible-map A B = Σ (A → B) (is-coherently-invertible)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : coherently-invertible-map A B)
  where

  map-coherently-invertible-map : A → B
  map-coherently-invertible-map = pr1 e

  is-coherently-invertible-map-coherently-invertible-map :
    is-coherently-invertible map-coherently-invertible-map
  is-coherently-invertible-map-coherently-invertible-map = pr2 e

  map-inv-coherently-invertible-map : B → A
  map-inv-coherently-invertible-map =
    map-inv-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  is-section-map-inv-coherently-invertible-map :
    map-coherently-invertible-map ∘ map-inv-coherently-invertible-map ~ id
  is-section-map-inv-coherently-invertible-map =
    is-section-map-inv-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  is-retraction-map-inv-coherently-invertible-map :
    map-inv-coherently-invertible-map ∘ map-coherently-invertible-map ~ id
  is-retraction-map-inv-coherently-invertible-map =
    is-retraction-map-inv-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  coh-coherently-invertible-map :
    coherence-is-coherently-invertible
      ( map-coherently-invertible-map)
      ( map-inv-coherently-invertible-map)
      ( is-section-map-inv-coherently-invertible-map)
      ( is-retraction-map-inv-coherently-invertible-map)
  coh-coherently-invertible-map =
    coh-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  section-map-coherently-invertible-map :
    section map-coherently-invertible-map
  section-map-coherently-invertible-map =
    section-map-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  retraction-map-coherently-invertible-map :
    retraction map-coherently-invertible-map
  retraction-map-coherently-invertible-map =
    retraction-map-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  is-invertible-map-coherently-invertible-map :
    is-invertible map-coherently-invertible-map
  is-invertible-map-coherently-invertible-map =
    is-invertible-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)
```

## Properties

### Invertible maps are coherently invertible

#### Lemma: A coherence for homotopies to an identity map

```agda
coh-is-coherently-invertible-id :
  {l : Level} {A : UU l} {f : A → A} (H : f ~ id) →
  (x : A) → H (f x) ＝ ap f (H x)
coh-is-coherently-invertible-id {A = A} {f} H x =
  is-injective-concat'
    ( H x)
    ( ap (concat (H (f x)) x) (inv (ap-id (H x))) ∙ nat-htpy H (H x))
```

#### The proof that invertible maps are coherently invertible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-invertible f)
  where

  abstract
    is-section-map-inv-is-coherently-invertible-is-invertible :
      f ∘ map-inv-is-invertible H ~ id
    is-section-map-inv-is-coherently-invertible-is-invertible y =
      ( inv
        ( is-section-map-inv-is-invertible H (f (map-inv-is-invertible H y)))) ∙
      ( ( ap
          ( f)
          ( is-retraction-map-inv-is-invertible
            ( H)
            ( map-inv-is-invertible H y))) ∙
        ( is-section-map-inv-is-invertible H y))

  is-retraction-map-inv-is-coherently-invertible-is-invertible :
    map-inv-is-invertible H ∘ f ~ id
  is-retraction-map-inv-is-coherently-invertible-is-invertible =
    is-retraction-map-inv-is-invertible H

  abstract
    inv-coh-is-coherently-invertible-is-invertible :
      f ·l is-retraction-map-inv-is-coherently-invertible-is-invertible ~
      is-section-map-inv-is-coherently-invertible-is-invertible ·r f
    inv-coh-is-coherently-invertible-is-invertible x =
      left-transpose-eq-concat
        ( is-section-map-inv-is-invertible
          ( H)
          ( f (map-inv-is-invertible H (f x))))
        ( ap f (is-retraction-map-inv-is-invertible H x))
        ( ( ap f
            ( is-retraction-map-inv-is-invertible
              ( H)
              ( map-inv-is-invertible H (f x)))) ∙
          ( is-section-map-inv-is-invertible H (f x)))
        ( ( nat-htpy
            ( right-whisker-comp (is-section-map-inv-is-invertible H) f)
            ( is-retraction-map-inv-is-invertible H x)) ∙
          ( ap
            ( concat' _ (is-section-map-inv-is-invertible H (f x)))
            ( ( ap-comp f
                ( map-inv-is-invertible H ∘ f)
                ( is-retraction-map-inv-is-invertible H x)) ∙
              ( inv
                ( ap
                  ( ap f)
                  ( coh-is-coherently-invertible-id
                    ( is-retraction-map-inv-is-invertible H) x))))))

  abstract
    coh-is-coherently-invertible-is-invertible :
      coherence-is-coherently-invertible
        ( f)
        ( map-inv-is-invertible H)
        ( is-section-map-inv-is-coherently-invertible-is-invertible)
        ( is-retraction-map-inv-is-coherently-invertible-is-invertible)
    coh-is-coherently-invertible-is-invertible x =
      inv (inv-coh-is-coherently-invertible-is-invertible x)

  abstract
    is-coherently-invertible-is-invertible : is-coherently-invertible f
    pr1 is-coherently-invertible-is-invertible =
      map-inv-is-invertible H
    pr1 (pr2 is-coherently-invertible-is-invertible) =
      is-section-map-inv-is-coherently-invertible-is-invertible
    pr1 (pr2 (pr2 is-coherently-invertible-is-invertible)) =
      is-retraction-map-inv-is-coherently-invertible-is-invertible
    pr2 (pr2 (pr2 is-coherently-invertible-is-invertible)) =
      coh-is-coherently-invertible-is-invertible
```

### Coherently invertible maps are embeddings

We first construct the converse map to the
[action on identifications](foundation.action-on-identifications-functions.md).
This is a rerun of the proof that maps with
[retractions](foundation-core.retractions.md) are
[injective](foundation-core.injective-maps.md) (`is-injective-retraction`), and
we repeat the proof to avoid cyclic dependencies.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-coherently-invertible f) {x y : A}
  where

  map-inv-ap-is-coherently-invertible : f x ＝ f y → x ＝ y
  map-inv-ap-is-coherently-invertible p =
    ( inv (is-retraction-map-inv-is-coherently-invertible H x)) ∙
    ( ( ap (map-inv-is-coherently-invertible H) p) ∙
      ( is-retraction-map-inv-is-coherently-invertible H y))
```

Next, we show that this converse map is a [section](foundation-core.sections.md)
and retraction of `ap f`.

```agda
  abstract
    is-section-map-inv-ap-is-coherently-invertible :
      ap f ∘ map-inv-ap-is-coherently-invertible ~ id
    is-section-map-inv-ap-is-coherently-invertible p =
      ( ap-concat f
        ( inv (is-retraction-map-inv-is-coherently-invertible H x))
        ( ( ap (map-inv-is-coherently-invertible H) p) ∙
          ( is-retraction-map-inv-is-coherently-invertible H y))) ∙
      ( ( ap-binary
          ( _∙_)
          ( ap-inv f (is-retraction-map-inv-is-coherently-invertible H x))
          ( ( ap-concat f
              ( ap (map-inv-is-coherently-invertible H) p)
              ( is-retraction-map-inv-is-coherently-invertible H y)) ∙
            ( ap-binary
              ( _∙_)
              ( inv (ap-comp f (map-inv-is-coherently-invertible H) p))
              ( inv (coh-is-coherently-invertible H y))))) ∙
        ( inv
          ( left-transpose-eq-concat
            ( ap f (is-retraction-map-inv-is-coherently-invertible H x))
            ( p)
            ( ( ap (f ∘ map-inv-is-coherently-invertible H) p) ∙
              ( is-section-map-inv-is-coherently-invertible H (f y)))
            ( ( ap-binary
                ( _∙_)
                ( inv (coh-is-coherently-invertible H x))
                ( inv (ap-id p))) ∙
              ( nat-htpy (is-section-map-inv-is-coherently-invertible H) p)))))

  abstract
    is-retraction-map-inv-ap-is-coherently-invertible :
      map-inv-ap-is-coherently-invertible ∘ ap f ~ id
    is-retraction-map-inv-ap-is-coherently-invertible refl =
      left-inv (is-retraction-map-inv-is-coherently-invertible H x)

  abstract
    is-invertible-ap-is-coherently-invertible : is-invertible (ap f {x} {y})
    pr1 is-invertible-ap-is-coherently-invertible =
      map-inv-ap-is-coherently-invertible
    pr1 (pr2 is-invertible-ap-is-coherently-invertible) =
      is-section-map-inv-ap-is-coherently-invertible
    pr2 (pr2 is-invertible-ap-is-coherently-invertible) =
      is-retraction-map-inv-ap-is-coherently-invertible

    is-coherently-invertible-ap-is-coherently-invertible :
      is-coherently-invertible (ap f {x} {y})
    is-coherently-invertible-ap-is-coherently-invertible =
      is-coherently-invertible-is-invertible
        ( is-invertible-ap-is-coherently-invertible)
```

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
