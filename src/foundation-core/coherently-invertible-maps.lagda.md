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
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-homotopies
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.invertible-maps
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.whiskering-homotopies-concatenation
```

</details>

## Idea

A [(two-sided) inverse](foundation-core.invertible-maps.md) for a map
`f : A → B` is a map `g : B → A` equipped with
[homotopies](foundation-core.homotopies.md) ` S : f ∘ g ~ id` and
`R : g ∘ f ~ id`. Such data, however is [structure](foundation.structure.md) on
the map `f`, and not generally a [property](foundation-core.propositions.md).
One way to make the type of inverses into a property is by adding a single
coherence condition between the homotopies of the inverse, asking that the
following diagram commmutes

```text
               S ·r f
             ~~~~~~~~~~
  f ∘ g ∘ f             f.
             ~~~~~~~~~~
               f ·l R
```

We call such data a
{{#concept "coherently invertible map" Agda=coherently-invertible-map}}. I.e., a
coherently invertible map `f : A → B` is a map equipped with a two-sided inverse
and this additional coherence.

There is also the alternative coherence condition we could add

```text
               R ·r g
             ~~~~~~~~~~
  g ∘ f ∘ g             g.
             ~~~~~~~~~~
               g ·l S
```

We will colloquially refer to invertible maps equipped with this coherence for
_transpose coherently invertible maps_.

**Note.** Coherently invertible maps are referred to as
{{#concept "half adjoint equivalences"}} in _Homotopy Type Theory – Univalent
Foundations of Mathematics_.

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
            Σ ( g ∘ f ~ id)
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

  section-is-coherently-invertible : section f
  pr1 section-is-coherently-invertible =
    map-inv-is-coherently-invertible
  pr2 section-is-coherently-invertible =
    is-section-map-inv-is-coherently-invertible

  retraction-is-coherently-invertible : retraction f
  pr1 retraction-is-coherently-invertible =
    map-inv-is-coherently-invertible
  pr2 retraction-is-coherently-invertible =
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
    section-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  retraction-map-coherently-invertible-map :
    retraction map-coherently-invertible-map
  retraction-map-coherently-invertible-map =
    retraction-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  is-invertible-map-coherently-invertible-map :
    is-invertible map-coherently-invertible-map
  is-invertible-map-coherently-invertible-map =
    is-invertible-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)
```

### The predicate of being transpose coherently invertible on maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  coherence-is-transpose-coherently-invertible :
    (f : A → B) (g : B → A) (G : f ∘ g ~ id) (H : g ∘ f ~ id) → UU (l1 ⊔ l2)
  coherence-is-transpose-coherently-invertible f g G H = H ·r g ~ g ·l G

  is-transpose-coherently-invertible : (A → B) → UU (l1 ⊔ l2)
  is-transpose-coherently-invertible f =
    Σ ( B → A)
      ( λ g →
        Σ ( f ∘ g ~ id)
          ( λ G →
            Σ (g ∘ f ~ id)
              ( λ H → coherence-is-transpose-coherently-invertible f g G H)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-transpose-coherently-invertible f)
  where

  map-inv-is-transpose-coherently-invertible : B → A
  map-inv-is-transpose-coherently-invertible = pr1 H

  is-section-map-inv-is-transpose-coherently-invertible :
    f ∘ map-inv-is-transpose-coherently-invertible ~ id
  is-section-map-inv-is-transpose-coherently-invertible = pr1 (pr2 H)

  is-retraction-map-inv-is-transpose-coherently-invertible :
    map-inv-is-transpose-coherently-invertible ∘ f ~ id
  is-retraction-map-inv-is-transpose-coherently-invertible = pr1 (pr2 (pr2 H))

  coh-is-transpose-coherently-invertible :
    coherence-is-transpose-coherently-invertible f
      ( map-inv-is-transpose-coherently-invertible)
      ( is-section-map-inv-is-transpose-coherently-invertible)
      ( is-retraction-map-inv-is-transpose-coherently-invertible)
  coh-is-transpose-coherently-invertible = pr2 (pr2 (pr2 H))

  is-invertible-is-transpose-coherently-invertible : is-invertible f
  pr1 is-invertible-is-transpose-coherently-invertible =
    map-inv-is-transpose-coherently-invertible
  pr1 (pr2 is-invertible-is-transpose-coherently-invertible) =
    is-section-map-inv-is-transpose-coherently-invertible
  pr2 (pr2 is-invertible-is-transpose-coherently-invertible) =
    is-retraction-map-inv-is-transpose-coherently-invertible

  section-is-transpose-coherently-invertible : section f
  pr1 section-is-transpose-coherently-invertible =
    map-inv-is-transpose-coherently-invertible
  pr2 section-is-transpose-coherently-invertible =
    is-section-map-inv-is-transpose-coherently-invertible

  retraction-is-transpose-coherently-invertible : retraction f
  pr1 retraction-is-transpose-coherently-invertible =
    map-inv-is-transpose-coherently-invertible
  pr2 retraction-is-transpose-coherently-invertible =
    is-retraction-map-inv-is-transpose-coherently-invertible
```

We will show that `is-transpose-coherently-invertible` is a proposition in
[`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).

### The type of transpose coherently invertible maps

```agda
transpose-coherently-invertible-map :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
transpose-coherently-invertible-map A B =
  Σ (A → B) (is-transpose-coherently-invertible)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (e : transpose-coherently-invertible-map A B)
  where

  map-transpose-coherently-invertible-map : A → B
  map-transpose-coherently-invertible-map = pr1 e

  is-transpose-coherently-invertible-map-transpose-coherently-invertible-map :
    is-transpose-coherently-invertible map-transpose-coherently-invertible-map
  is-transpose-coherently-invertible-map-transpose-coherently-invertible-map =
    pr2 e

  map-inv-transpose-coherently-invertible-map : B → A
  map-inv-transpose-coherently-invertible-map =
    map-inv-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  is-section-map-inv-transpose-coherently-invertible-map :
    ( map-transpose-coherently-invertible-map ∘
      map-inv-transpose-coherently-invertible-map) ~
    ( id)
  is-section-map-inv-transpose-coherently-invertible-map =
    is-section-map-inv-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  is-retraction-map-inv-transpose-coherently-invertible-map :
    ( map-inv-transpose-coherently-invertible-map ∘
      map-transpose-coherently-invertible-map) ~
    ( id)
  is-retraction-map-inv-transpose-coherently-invertible-map =
    is-retraction-map-inv-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  coh-transpose-coherently-invertible-map :
    coherence-is-transpose-coherently-invertible
      ( map-transpose-coherently-invertible-map)
      ( map-inv-transpose-coherently-invertible-map)
      ( is-section-map-inv-transpose-coherently-invertible-map)
      ( is-retraction-map-inv-transpose-coherently-invertible-map)
  coh-transpose-coherently-invertible-map =
    coh-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  section-map-transpose-coherently-invertible-map :
    section map-transpose-coherently-invertible-map
  section-map-transpose-coherently-invertible-map =
    section-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  retraction-map-transpose-coherently-invertible-map :
    retraction map-transpose-coherently-invertible-map
  retraction-map-transpose-coherently-invertible-map =
    retraction-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  is-invertible-map-transpose-coherently-invertible-map :
    is-invertible map-transpose-coherently-invertible-map
  is-invertible-map-transpose-coherently-invertible-map =
    is-invertible-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)
```

### Invertible maps that are coherent are coherently invertible maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-invertible f)
  where

  coherence-is-invertible : UU (l1 ⊔ l2)
  coherence-is-invertible =
    coherence-is-coherently-invertible
      ( f)
      ( map-inv-is-invertible H)
      ( is-section-map-inv-is-invertible H)
      ( is-retraction-map-inv-is-invertible H)

  transpose-coherence-is-invertible : UU (l1 ⊔ l2)
  transpose-coherence-is-invertible =
    coherence-is-transpose-coherently-invertible
      ( f)
      ( map-inv-is-invertible H)
      ( is-section-map-inv-is-invertible H)
      ( is-retraction-map-inv-is-invertible H)

  is-coherently-invertible-coherence-is-invertible :
    coherence-is-invertible → is-coherently-invertible f
  is-coherently-invertible-coherence-is-invertible coh =
    ( map-inv-is-invertible H ,
      is-section-map-inv-is-invertible H ,
      is-retraction-map-inv-is-invertible H ,
      coh)

  is-transpose-coherently-invertible-transpose-coherence-is-invertible :
    transpose-coherence-is-invertible → is-transpose-coherently-invertible f
  is-transpose-coherently-invertible-transpose-coherence-is-invertible coh =
    ( map-inv-is-invertible H ,
      is-section-map-inv-is-invertible H ,
      is-retraction-map-inv-is-invertible H ,
      coh)
```

## Properties

### Invertible maps are coherently invertible

The construction follows Theorem 4.2.3 in _Homotopy Type Theory – Univalent
Foundations of Mathematics_.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-invertible f)
  where

  is-retraction-map-inv-is-coherently-invertible-is-invertible :
    map-inv-is-invertible H ∘ f ~ id
  is-retraction-map-inv-is-coherently-invertible-is-invertible =
    is-retraction-map-inv-is-invertible H

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

  abstract
    inv-coh-is-coherently-invertible-is-invertible :
      f ·l is-retraction-map-inv-is-coherently-invertible-is-invertible ~
      is-section-map-inv-is-coherently-invertible-is-invertible ·r f
    inv-coh-is-coherently-invertible-is-invertible =
      left-transpose-htpy-concat
        ( ( is-section-map-inv-is-invertible H) ·r
          ( f ∘ map-inv-is-invertible H ∘ f))
        ( f ·l is-retraction-map-inv-is-invertible H)
        ( ( ( f) ·l
            ( is-retraction-map-inv-is-invertible H) ·r
            ( map-inv-is-invertible H ∘ f)) ∙h
          ( is-section-map-inv-is-invertible H ·r f))
        ( ( ( nat-htpy (is-section-map-inv-is-invertible H ·r f)) ·r
            ( is-retraction-map-inv-is-invertible H)) ∙h
          ( right-whisker-concat-htpy
            ( ( inv-preserves-comp-left-whisker-comp
                ( f)
                ( map-inv-is-invertible H ∘ f)
                ( is-retraction-map-inv-is-invertible H)) ∙h
              ( left-whisker-comp²
                ( f)
                ( inv-htpy-coh-htpy-id
                  ( is-retraction-map-inv-is-invertible H))))
            ( is-section-map-inv-is-invertible H ·r f)))

  abstract
    coh-is-coherently-invertible-is-invertible :
      coherence-is-coherently-invertible
        ( f)
        ( map-inv-is-invertible H)
        ( is-section-map-inv-is-coherently-invertible-is-invertible)
        ( is-retraction-map-inv-is-coherently-invertible-is-invertible)
    coh-is-coherently-invertible-is-invertible =
      inv-htpy inv-coh-is-coherently-invertible-is-invertible

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

### The inverse of a coherently invertible map is transpose coherently invertible

Of course there is also a converse construction, and since these just move data
around, they are strict inverses to one another.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-transpose-coherently-invertible-map-inv-is-coherently-invertible :
    {f : A → B} (H : is-coherently-invertible f) →
    is-transpose-coherently-invertible (map-inv-is-coherently-invertible H)
  is-transpose-coherently-invertible-map-inv-is-coherently-invertible {f} H =
    ( f ,
      is-retraction-map-inv-is-coherently-invertible H ,
      is-section-map-inv-is-coherently-invertible H ,
      coh-is-coherently-invertible H)

  is-coherently-invertible-map-inv-is-transpose-coherently-invertible :
    {f : A → B} (H : is-transpose-coherently-invertible f) →
    is-coherently-invertible (map-inv-is-transpose-coherently-invertible H)
  is-coherently-invertible-map-inv-is-transpose-coherently-invertible {f} H =
    ( f ,
      is-retraction-map-inv-is-transpose-coherently-invertible H ,
      is-section-map-inv-is-transpose-coherently-invertible H ,
      coh-is-transpose-coherently-invertible H)

  transpose-coherently-invertible-map-inv-coherently-invertible-map :
    coherently-invertible-map A B → transpose-coherently-invertible-map B A
  transpose-coherently-invertible-map-inv-coherently-invertible-map e =
    ( map-inv-coherently-invertible-map e ,
      is-transpose-coherently-invertible-map-inv-is-coherently-invertible
        ( is-coherently-invertible-map-coherently-invertible-map e))

  coherently-invertible-map-inv-transpose-coherently-invertible-map :
    transpose-coherently-invertible-map A B → coherently-invertible-map B A
  coherently-invertible-map-inv-transpose-coherently-invertible-map e =
    ( map-inv-transpose-coherently-invertible-map e ,
      is-coherently-invertible-map-inv-is-transpose-coherently-invertible
        ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map
          ( e)))
```

### Coherently invertible maps are coherently invertible in both senses

The proof follows Lemma 4.2.2 in _Homotopy Type Theory – Univalent Foundations
of Mathematics_.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B)
  (g : B → A)
  (S : is-section f g)
  (R : is-retraction f g)
  (H : coherence-is-coherently-invertible f g S R)
  where

  lemma-is-coherently-invertible' :
    g ·l S ·r (f ∘ g) ~ (g ∘ f) ·l R ·r g
  lemma-is-coherently-invertible' =
    ( preserves-comp-right-whisker-comp f g (g ·l S)) ∙h
    ( double-whisker-comp² g H g) ∙h
    ( preserves-comp-left-whisker-comp g f (R ·r g))

  inv-coh-is-transpose-coherently-invertible-coherence-is-coherently-invertible :
    (g ∘ f ∘ g) ·l S ~ (g ∘ f) ·l R ·r g
  inv-coh-is-transpose-coherently-invertible-coherence-is-coherently-invertible =
    ( inv-preserves-comp-left-whisker-comp g (f ∘ g) S) ∙h
    ( left-whisker-comp² g (inv-htpy-coh-htpy-id S)) ∙h
    ( lemma-is-coherently-invertible')
```

By naturality we have

```text
                   gfgS
     gfgfg --------------------> gfg
       |                          |
  Rgfg |  nat-htpy (R ·r g) ·r S  | Rg
       ∨                          ∨
      gfg ----------------------> g
                    gS
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B)
  (g : B → A)
  (S : is-section f g)
  (R : is-retraction f g)
  where

  naturality-square-is-retraction-is-section :
    coherence-square-homotopies
      ( (g ∘ f ∘ g) ·l S)
      ( R ·r (g ∘ f ∘ g))
      ( R ·r g)
      ( g ·l S)
  naturality-square-is-retraction-is-section = nat-htpy (R ·r g) ·r S
```

TODO Explain

```text
             Rgfg
     gfgfg -------> gfg
       |             |
  Sgfg |             | Rg
       ∨             ∨
      gfg ---------> g
              Rg
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B)
  (g : B → A)
  (S : is-section f g)
  (R : is-retraction f g)
  (H : coherence-is-coherently-invertible f g S R)
  where

  naturality-square-transposition-coherence-is-coherently-invertible :
    coherence-square-homotopies
      ( R ·r (g ∘ f ∘ g))
      ( (g ∘ f ∘ g) ·l S)
      ( R ·r g)
      ( R ·r g)
  naturality-square-transposition-coherence-is-coherently-invertible =
    ( ap-concat-htpy'
      ( R ·r g)
      ( inv-coh-is-transpose-coherently-invertible-coherence-is-coherently-invertible
        ( f) (g) (S) (R) (H))) ∙h
    (inv-htpy (nat-htpy R ·r (R ·r g))) ∙h
    ap-concat-htpy (R ·r (g ∘ f ∘ g)) (left-unit-law-left-whisker-comp (R ·r g))
```

Pasting the two lemmas along the common edge `Rgfg`

```text
            gfgS           gfgS
      gfg <------- gfgfg -------> gfg
       |             |             |
    Rg |            Rgfg           | Rg
       ∨             ∨             ∨
       g <--------- gfg ---------> gm
             Rg             gS
```

we observe that the homotopy `gfgS` at the top cancels itself, as well as the
`Rg` on the left, leaving us with a homotopy `Rg ~ gS` as desired.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B)
  (g : B → A)
  (S : is-section f g)
  (R : is-retraction f g)
  (H : coherence-is-coherently-invertible f g S R)
  where abstract

  coherence-transposition-coherence-is-coherently-invertible :
    coherence-is-transpose-coherently-invertible f g S R
  coherence-transposition-coherence-is-coherently-invertible =
    ( ap-concat-htpy' (R ·r g) (inv-htpy (left-inv-htpy ((g ∘ f ∘ g) ·l S)))) ∙h
    ( assoc-htpy (inv-htpy ((g ∘ f ∘ g) ·l S)) ((g ∘ f ∘ g) ·l S) (R ·r g)) ∙h
    ( ap-concat-htpy
      ( inv-htpy ((g ∘ f ∘ g) ·l S))
      ( inv-htpy (naturality-square-is-retraction-is-section f g S R))) ∙h
    ( inv-htpy
      ( assoc-htpy
        ( inv-htpy ((g ∘ f ∘ g) ·l S)) (R ·r (g ∘ f ∘ g)) (g ·l S))) ∙h
    ( ap-concat-htpy'
      ( g ·l S)
      ( ( vertical-inv-coherence-square-homotopies
          ( R ·r (g ∘ f ∘ g)) ((g ∘ f ∘ g) ·l S) (R ·r g) (R ·r g)
          ( naturality-square-transposition-coherence-is-coherently-invertible
            ( f) (g) (S) (R) (H))) ∙h
        ( right-inv-htpy (R ·r g))))
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  coherence-transposition-is-coherently-invertible :
    (H : is-coherently-invertible f) →
    coherence-is-transpose-coherently-invertible
      ( f)
      ( map-inv-is-coherently-invertible H)
      ( is-section-map-inv-is-coherently-invertible H)
      ( is-retraction-map-inv-is-coherently-invertible H)
  coherence-transposition-is-coherently-invertible
    ( g , S , R , H) =
    coherence-transposition-coherence-is-coherently-invertible
      f g S R H

  transposition-is-coherently-invertible :
    is-coherently-invertible f → is-transpose-coherently-invertible f
  transposition-is-coherently-invertible H =
    is-transpose-coherently-invertible-transpose-coherence-is-invertible
      ( is-invertible-is-coherently-invertible H)
      ( coherence-transposition-is-coherently-invertible H)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  coherence-transposition-is-transpose-coherently-invertible :
    (H : is-transpose-coherently-invertible f) →
    coherence-is-coherently-invertible
      ( f)
      ( map-inv-is-transpose-coherently-invertible H)
      ( is-section-map-inv-is-transpose-coherently-invertible H)
      ( is-retraction-map-inv-is-transpose-coherently-invertible H)
  coherence-transposition-is-transpose-coherently-invertible H =
    coherence-transposition-is-coherently-invertible
      ( is-coherently-invertible-map-inv-is-transpose-coherently-invertible H)

  transposition-is-transpose-coherently-invertible :
    is-transpose-coherently-invertible f → is-coherently-invertible f
  transposition-is-transpose-coherently-invertible H =
    is-coherently-invertible-coherence-is-invertible
      ( is-invertible-is-transpose-coherently-invertible H)
      ( coherence-transposition-is-transpose-coherently-invertible H)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  transposition-coherently-invertible-map :
    coherently-invertible-map A B → transpose-coherently-invertible-map A B
  transposition-coherently-invertible-map (f , H) =
    ( f , transposition-is-coherently-invertible H)

  transposition-transpose-coherently-invertible-map :
    transpose-coherently-invertible-map A B → coherently-invertible-map A B
  transposition-transpose-coherently-invertible-map (f , H) =
    ( f , transposition-is-transpose-coherently-invertible H)
```

### Inversion of coherently invertible maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-coherently-invertible-map-inv-is-coherently-invertible :
    {f : A → B} (H : is-coherently-invertible f) →
    is-coherently-invertible (map-inv-is-coherently-invertible H)
  is-coherently-invertible-map-inv-is-coherently-invertible H =
    is-coherently-invertible-map-inv-is-transpose-coherently-invertible
      ( transposition-is-coherently-invertible H)

  is-transpose-coherently-invertible-map-inv-is-transpose-coherently-invertible :
    {f : A → B} (H : is-transpose-coherently-invertible f) →
    is-transpose-coherently-invertible
      ( map-inv-is-transpose-coherently-invertible H)
  is-transpose-coherently-invertible-map-inv-is-transpose-coherently-invertible
    H =
    transposition-is-coherently-invertible
      ( is-coherently-invertible-map-inv-is-transpose-coherently-invertible H)

  inv-coherently-invertible-map :
    coherently-invertible-map A B → coherently-invertible-map B A
  inv-coherently-invertible-map (f , H) =
    ( map-inv-is-coherently-invertible H ,
      is-coherently-invertible-map-inv-is-coherently-invertible H)

  inv-transpose-coherently-invertible-map :
    transpose-coherently-invertible-map A B →
    transpose-coherently-invertible-map B A
  inv-transpose-coherently-invertible-map (f , H) =
    ( map-inv-is-transpose-coherently-invertible H ,
      is-transpose-coherently-invertible-map-inv-is-transpose-coherently-invertible
        ( H))
```

### The identity map is coherently invertible

```agda
module _
  {l : Level} {A : UU l}
  where

  is-coherently-invertible-id :
    is-coherently-invertible (id {A = A})
  is-coherently-invertible-id =
    is-coherently-invertible-coherence-is-invertible is-invertible-id refl-htpy

  id-coherently-invertible-map : coherently-invertible-map A A
  pr1 id-coherently-invertible-map = id
  pr2 id-coherently-invertible-map = is-coherently-invertible-id

  is-transpose-coherently-invertible-id :
    is-transpose-coherently-invertible (id {A = A})
  is-transpose-coherently-invertible-id =
    is-transpose-coherently-invertible-map-inv-is-coherently-invertible
      ( is-coherently-invertible-id)

  id-transpose-coherently-invertible-map :
    transpose-coherently-invertible-map A A
  pr1 id-transpose-coherently-invertible-map = id
  pr2 id-transpose-coherently-invertible-map =
    is-transpose-coherently-invertible-id
```

### Composition of coherently invertible maps

```text
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
    (g : B → C) (f : A → B)
    (G : is-coherently-invertible g)
    (F : is-coherently-invertible f)
  where

  coh-is-coherently-invertible-comp :
    coherence-is-coherently-invertible
      ( g ∘ f)
      ( map-inv-is-invertible-comp g f
        ( is-invertible-is-coherently-invertible G)
        ( is-invertible-is-coherently-invertible F))
      ( is-section-map-inv-is-invertible-comp g f
        ( is-invertible-is-coherently-invertible G)
        ( is-invertible-is-coherently-invertible F))
      ( is-retraction-map-inv-is-invertible-comp g f
        ( is-invertible-is-coherently-invertible G)
        ( is-invertible-is-coherently-invertible F))
  coh-is-coherently-invertible-comp =
    homotopy-reasoning
    ( ( g) ·l
      ( is-section-map-inv-is-coherently-invertible F) ·r
      ( map-inv-is-coherently-invertible G ∘ g ∘ f)) ∙h
    ( is-section-map-inv-is-coherently-invertible G ·r (g ∘ f))
    ~
    ( {!  !}) ∙h
    ( g ·l is-retraction-map-inv-is-coherently-invertible G ·r f)
      by
      ap-binary-concat-htpy
        ( {! ( g) ·l
          ( is-section-map-inv-is-coherently-invertible F) ·r
          ( map-inv-is-coherently-invertible G ∘ g ∘ f)  !})
        ( coh-is-coherently-invertible G ·r f)
    ~ {!   !} by {!   !}
    ~ {!   !} by {!   !}
    ~ {!   !} by {!   !}
    ~ {!   !} by {!   !}
    ~ ( ( ( g ∘ f) ·l
          ( map-inv-is-coherently-invertible F ·l
            is-retraction-map-inv-is-coherently-invertible G ·r f)) ∙h
          ( ( g ∘ f) ·l is-retraction-map-inv-is-coherently-invertible F))
      by {!   !}
    ~ ( ( g ∘ f) ·l
        ( ( map-inv-is-coherently-invertible F ·l
            is-retraction-map-inv-is-coherently-invertible G ·r f) ∙h
          ( is-retraction-map-inv-is-coherently-invertible F)))
      by
        inv-htpy
          ( distributive-left-whisker-comp-concat
            ( g ∘ f)
            ( map-inv-is-coherently-invertible F ·l is-retraction-map-inv-is-coherently-invertible G ·r f)
            ( is-retraction-map-inv-is-coherently-invertible F))

  is-coherently-invertible-comp : is-coherently-invertible (g ∘ f)
  is-coherently-invertible-comp =
    is-coherently-invertible-coherence-is-invertible
      ( is-invertible-comp g f
        ( is-invertible-is-coherently-invertible G)
        ( is-invertible-is-coherently-invertible F))
      {!   !}

```

## References

1. Univalent Foundations Project, _Homotopy Type Theory – Univalent Foundations
   of Mathematics_ (2013) ([website](https://homotopytypetheory.org/book/),
   [arXiv:1308.0729](https://arxiv.org/abs/1308.0729))

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
