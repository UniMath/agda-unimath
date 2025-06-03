# Coherently invertible maps

```agda
module foundation-core.coherently-invertible-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.homotopy-algebra
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
[homotopies](foundation-core.homotopies.md) `S : f ∘ g ~ id` and
`R : g ∘ f ~ id`. Such data, however is [structure](foundation.structure.md) on
the map `f`, and not generally a [property](foundation-core.propositions.md).
One way to make the type of inverses into a property is by adding a single
coherence condition between the homotopies of the inverse, asking that the
following diagram commmutes

```text
              S ·r f
            --------->
  f ∘ g ∘ f            f.
            --------->
              f ·l R
```

We call such data a
{{#concept "coherently invertible map" Agda=coherently-invertible-map}}. I.e., a
coherently invertible map `f : A → B` is a map equipped with a two-sided inverse
and this additional coherence.

There is also the alternative coherence condition we could add

```text
              R ·r g
            --------->
  g ∘ f ∘ g            g.
            --------->
              g ·l S
```

We will colloquially refer to invertible maps equipped with this coherence as
_transpose coherently invertible maps_.

**Note.** Coherently invertible maps are referred to as
{{#concept "half adjoint equivalences"}} in {{#cite UF13}}.

On this page we will prove that every two-sided inverse `g` of `f` can be
promoted to a coherent two-sided inverse. Thus, for most properties of
coherently invertible maps, it suffices to consider the data of a two-sided
inverse. However, this coherence construction requires us to replace the section
homotopy (or retraction homotopy). For this reason we also give direct
constructions showing

1. The identity map is coherently invertible.
2. The composite of two coherently invertible maps is coherently invertible.
3. The inverse of a coherently invertible map is coherently invertible.
4. Every map homotopic to a coherently invertible map is coherently invertible.
5. The 3-for-2 property of coherently invertible maps.

Each of these constructions appropriately preserve the data of the underlying
two-sided inverse.

## Definition

### The predicate of being a coherently invertible map

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
        Σ ( f ∘ g ~ id)
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
    is-section f map-inv-is-coherently-invertible
  is-section-map-inv-is-coherently-invertible = pr1 (pr2 H)

  is-retraction-map-inv-is-coherently-invertible :
    is-retraction f map-inv-is-coherently-invertible
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

  section-coherently-invertible-map :
    section map-coherently-invertible-map
  section-coherently-invertible-map =
    section-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  retraction-coherently-invertible-map :
    retraction map-coherently-invertible-map
  retraction-coherently-invertible-map =
    retraction-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  is-invertible-coherently-invertible-map :
    is-invertible map-coherently-invertible-map
  is-invertible-coherently-invertible-map =
    is-invertible-is-coherently-invertible
      ( is-coherently-invertible-map-coherently-invertible-map)

  invertible-map-coherently-invertible-map : invertible-map A B
  pr1 invertible-map-coherently-invertible-map =
    map-coherently-invertible-map
  pr2 invertible-map-coherently-invertible-map =
    is-invertible-coherently-invertible-map
```

### The predicate of being a transpose coherently invertible map

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
            Σ ( g ∘ f ~ id)
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

  section-transpose-coherently-invertible-map :
    section map-transpose-coherently-invertible-map
  section-transpose-coherently-invertible-map =
    section-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  retraction-transpose-coherently-invertible-map :
    retraction map-transpose-coherently-invertible-map
  retraction-transpose-coherently-invertible-map =
    retraction-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  is-invertible-transpose-coherently-invertible-map :
    is-invertible map-transpose-coherently-invertible-map
  is-invertible-transpose-coherently-invertible-map =
    is-invertible-is-transpose-coherently-invertible
      ( is-transpose-coherently-invertible-map-transpose-coherently-invertible-map)

  invertible-map-transpose-coherently-invertible-map : invertible-map A B
  pr1 invertible-map-transpose-coherently-invertible-map =
    map-transpose-coherently-invertible-map
  pr2 invertible-map-transpose-coherently-invertible-map =
    is-invertible-transpose-coherently-invertible-map
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

### The inverse of a coherently invertible map is transpose coherently invertible and vice versa

The inverse of a coherently invertible map is transpose coherently invertible.
Conversely, the inverse of a transpose coherently invertible map is coherently
invertible. Since these are defined by simply moving data around, they are
strict inverses to one another.

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

### Invertible maps are coherently invertible

This result is known as
[Vogt's lemma](https://ncatlab.org/nlab/show/homotopy+equivalence#vogts_lemma)
in point-set topology. The construction follows Lemma 10.4.5 in {{#cite Rij22}}.

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
    is-section-map-inv-is-coherently-invertible-is-invertible =
      ( ( inv-htpy (is-section-map-inv-is-invertible H)) ·r
        ( f ∘ map-inv-is-invertible H)) ∙h
      ( ( ( f) ·l
          ( is-retraction-map-inv-is-invertible H) ·r
          ( map-inv-is-invertible H)) ∙h
        ( is-section-map-inv-is-invertible H))

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
                ( inv-coh-htpy-id (is-retraction-map-inv-is-invertible H))))
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

  is-coherently-invertible-is-invertible : is-coherently-invertible f
  is-coherently-invertible-is-invertible =
    ( map-inv-is-invertible H ,
      is-section-map-inv-is-coherently-invertible-is-invertible ,
      is-retraction-map-inv-is-coherently-invertible-is-invertible ,
      coh-is-coherently-invertible-is-invertible)
```

We get the transpose version for free:

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-invertible f)
  where

  is-transpose-coherently-invertible-is-invertible :
    is-transpose-coherently-invertible f
  is-transpose-coherently-invertible-is-invertible =
    is-transpose-coherently-invertible-map-inv-is-coherently-invertible
      ( is-coherently-invertible-is-invertible
        ( is-invertible-map-inv-is-invertible H))
```

### Coherently invertible maps are injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-injective-is-coherently-invertible :
    (H : is-coherently-invertible f) {x y : A} → f x ＝ f y → x ＝ y
  is-injective-is-coherently-invertible H =
    is-injective-is-invertible
      ( is-invertible-is-coherently-invertible H)

  is-injective-is-transpose-coherently-invertible :
    (H : is-transpose-coherently-invertible f) {x y : A} → f x ＝ f y → x ＝ y
  is-injective-is-transpose-coherently-invertible H =
    is-injective-is-invertible
      ( is-invertible-is-transpose-coherently-invertible H)
```

### Coherently invertible maps are embeddings

We show that `is-injective-is-coherently-invertible` is a
[section](foundation-core.sections.md) and
[retraction](foundation-core.retractions.md) of `ap f`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-coherently-invertible f) {x y : A}
  where

  abstract
    is-section-is-injective-is-coherently-invertible :
      ap f {x} {y} ∘ is-injective-is-coherently-invertible H ~ id
    is-section-is-injective-is-coherently-invertible p =
      ( ap-concat f
        ( inv (is-retraction-map-inv-is-coherently-invertible H x))
        ( ( ap (map-inv-is-coherently-invertible H) p) ∙
          ( is-retraction-map-inv-is-coherently-invertible H y))) ∙
      ( ap-binary
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
            ( nat-htpy (is-section-map-inv-is-coherently-invertible H) p))))

  abstract
    is-retraction-is-injective-is-coherently-invertible :
      is-injective-is-coherently-invertible H ∘ ap f {x} {y} ~ id
    is-retraction-is-injective-is-coherently-invertible refl =
      left-inv (is-retraction-map-inv-is-coherently-invertible H x)

  is-invertible-ap-is-coherently-invertible : is-invertible (ap f {x} {y})
  is-invertible-ap-is-coherently-invertible =
    ( is-injective-is-coherently-invertible H ,
      is-section-is-injective-is-coherently-invertible ,
      is-retraction-is-injective-is-coherently-invertible)

  is-coherently-invertible-ap-is-coherently-invertible :
    is-coherently-invertible (ap f {x} {y})
  is-coherently-invertible-ap-is-coherently-invertible =
    is-coherently-invertible-is-invertible
      ( is-invertible-ap-is-coherently-invertible)
```

### Coherently invertible maps are transpose coherently invertible

The proof follows Lemma 4.2.2 in {{#cite UF13}}.

**Proof.** By naturality of homotopies we have

```text
                   gfRg
     gfgfg --------------------> gfg
       |                          |
  Rgfg |  nat-htpy R ·r (R ·r g)  | Rg
       ∨                          ∨
      gfg ----------------------> g.
                    Rg
```

We can paste the homotopy

```text
  g (inv-coh-htpy-id S) ∙ gHg : Sgfg ~ gfSg ~ gfRg
```

along the top edge of this naturality square obtaining the coherence square

```text
             gfgS
     gfgfg -------> gfg
       |             |
  Rgfg |             | Rg
       ∨             ∨
      gfg ---------> g.
              Rg
```

There is also the naturality square

```text
                   gfgS
     gfgfg --------------------> gfg
       |                          |
  Rgfg |  nat-htpy (R ·r g) ·r S  | Rg
       ∨                          ∨
      gfg ----------------------> g.
                    gS
```

Now, by pasting these along the common edge `Rgfg`, we obtain

```text
            gfgS           gfgS
      gfg <------- gfgfg -------> gfg
       |             |             |
    Rg |             | Rgfg        | Rg
       ∨             ∨             ∨
       g <--------- gfg ---------> g.
             Rg             gS
```

After canceling `gfgS` and `Rg` with themselves, we are left with `Rg ~ gS` as
desired.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B)
  (g : B → A)
  (S : is-section f g)
  (R : is-retraction f g)
  (H : coherence-is-coherently-invertible f g S R)
  where

  abstract
    coh-transposition-coherence-is-coherently-invertible :
      (g ∘ f ∘ g) ·l S ~ (g ∘ f) ·l R ·r g
    coh-transposition-coherence-is-coherently-invertible =
      ( inv-preserves-comp-left-whisker-comp g (f ∘ g) S) ∙h
      ( left-whisker-comp² g (inv-coh-htpy-id S)) ∙h
      ( double-whisker-comp² g H g) ∙h
      ( preserves-comp-left-whisker-comp g f (R ·r g))

  abstract
    naturality-square-transposition-coherence-is-coherently-invertible :
      coherence-square-homotopies
        ( R ·r (g ∘ f ∘ g))
        ( (g ∘ f ∘ g) ·l S)
        ( R ·r g)
        ( R ·r g)
    naturality-square-transposition-coherence-is-coherently-invertible =
      ( ap-concat-htpy'
        ( R ·r g)
        ( coh-transposition-coherence-is-coherently-invertible)) ∙h
      ( inv-htpy (nat-htpy R ·r (R ·r g))) ∙h
      ( ap-concat-htpy
        ( R ·r (g ∘ f ∘ g))
        ( left-unit-law-left-whisker-comp (R ·r g)))

  abstract
    coherence-transposition-coherence-is-coherently-invertible :
      coherence-is-transpose-coherently-invertible f g S R
    coherence-transposition-coherence-is-coherently-invertible =
      ( ap-concat-htpy'
        ( R ·r g)
        ( inv-htpy (left-inv-htpy ((g ∘ f ∘ g) ·l S)))) ∙h
      ( assoc-htpy (inv-htpy ((g ∘ f ∘ g) ·l S)) ((g ∘ f ∘ g) ·l S) (R ·r g)) ∙h
      ( ap-concat-htpy
        ( inv-htpy ((g ∘ f ∘ g) ·l S))
        ( inv-htpy (nat-htpy (R ·r g) ·r S))) ∙h
      ( inv-htpy
        ( assoc-htpy
          ( inv-htpy ((g ∘ f ∘ g) ·l S))
          ( R ·r (g ∘ f ∘ g))
          ( g ·l S))) ∙h
      ( ap-concat-htpy'
        ( g ·l S)
        ( ( vertical-inv-coherence-square-homotopies
            ( R ·r (g ∘ f ∘ g)) ((g ∘ f ∘ g) ·l S) (R ·r g) (R ·r g)
            ( naturality-square-transposition-coherence-is-coherently-invertible)) ∙h
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
    coherence-transposition-coherence-is-coherently-invertible f g S R H

  transposition-is-coherently-invertible :
    is-coherently-invertible f → is-transpose-coherently-invertible f
  transposition-is-coherently-invertible H =
    is-transpose-coherently-invertible-transpose-coherence-is-invertible
      ( is-invertible-is-coherently-invertible H)
      ( coherence-transposition-is-coherently-invertible H)
```

### Transpose coherently invertible maps are coherently invertible

```agda
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

### Coherently invertible maps are closed under homotopies

**Proof.** Assume given a coherently invertible map `f` with inverse `g`,
homotopies `S : f ∘ g ~ id`, `R : g ∘ f ~ id` and coherence `C : Sf ~ fR`.
Moreover, assume the map `f'` is homotopic to `f` with homotopy `H : f' ~ f`.
Then `g` is also a two-sided inverse to `f'` via the homotopies

```text
  S' := Hg ∙ S : f' ∘ g ~ id    and    R' := gH ∙ R : g ∘ f' ~ id.
```

Moreover, these witnesses are part of a coherent inverse to `f'`. To show this,
we must construct a coherence `C'` of the square

```text
           Hgf'
    f'gf' -----> f'gf
      |           |
 f'gH |           | Sf'
      ∨           ∨
    f'gf -------> f'.
           f'R
```

We begin by observing that `C` fits somewhere along the diagonal of this square
via the composite

```text
                        Sf
            HgH       ------>     H⁻¹
    f'gf' ------> fgf    C    f ------> f'.
                      ------>
                        fR
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f f' : A → B} (H : f' ~ f)
  (g : B → A) (S : f ∘ g ~ id) (R : g ∘ f ~ id) (C : S ·r f ~ f ·l R)
  where

  coh-coh-is-coherently-invertible-htpy :
    horizontal-concat-htpy' (H ·r g) H ∙h (S ·r f ∙h inv-htpy H) ~
    horizontal-concat-htpy' (H ·r g) H ∙h (f ·l R ∙h inv-htpy H)
  coh-coh-is-coherently-invertible-htpy =
    left-whisker-concat-htpy
      ( horizontal-concat-htpy' (H ·r g) H)
      ( right-whisker-concat-htpy C (inv-htpy H))
```

Now the problem is reduced to constructing two homotopies

```text
  Hgf' ∙ Sf' ~ HgH ∙ Sf ∙ H⁻¹    and    f'gH ∙ f'R ~ HgH ∙ fR ∙ H⁻¹.
```

By the two equivalent constructions of the horizontal composite `HgH`

```text
    Hgf' ∙ fgH ~ HgH ~ f'gH ∙ Hgf
```

constructing the two homotopies is equivalent to constructing coherences of the
squares

```text
            fgH                        Hgf
     fgf' -------> fgf          f'gf -------> fgf
      |             |            |             |
  Sf' |             | Sf     f'R |             | fR
      ∨             ∨            ∨             ∨
      f' ---------> f            f' ---------> f.
             H                          H
```

However, these squares are naturality squares, so we are done.

```agda
  coh-section-is-coherently-invertible-htpy :
    (H ·r g ∙h S) ·r f' ~
    horizontal-concat-htpy' (H ·r g) H ∙h ((S ·r f) ∙h inv-htpy H)
  coh-section-is-coherently-invertible-htpy =
    ( left-whisker-concat-htpy
      ( H ·r (g ∘ f'))
      ( right-transpose-htpy-concat (S ·r f') H ((f ∘ g) ·l H ∙h S ·r f)
        ( ( ap-concat-htpy
            ( S ·r f')
            ( inv-htpy (left-unit-law-left-whisker-comp H))) ∙h
          ( nat-htpy S ·r H)))) ∙h
    ( ( ap-concat-htpy
        ( H ·r (g ∘ f'))
        ( assoc-htpy ((f ∘ g) ·l H) (S ·r f) (inv-htpy H))) ∙h
      ( inv-htpy
        ( assoc-htpy (H ·r (g ∘ f')) ((f ∘ g) ·l H) ((S ·r f) ∙h inv-htpy H))))

  coh-retraction-is-coherently-invertible-htpy :
    horizontal-concat-htpy' (H ·r g) H ∙h ((f ·l R) ∙h inv-htpy H) ~
    f' ·l ((g ·l H) ∙h R)
  coh-retraction-is-coherently-invertible-htpy =
    ( ap-concat-htpy'
      ( f ·l R ∙h inv-htpy H)
      ( coh-horizontal-concat-htpy (H ·r g) H)) ∙h
    ( assoc-htpy ((f' ∘ g) ·l H) (H ·r (g ∘ f)) (f ·l R ∙h inv-htpy H)) ∙h
    ( ap-concat-htpy
      ( (f' ∘ g) ·l H)
      ( inv-htpy (assoc-htpy (H ·r (g ∘ f)) (f ·l R) (inv-htpy H)))) ∙h
    ( left-whisker-concat-htpy
      ( (f' ∘ g) ·l H)
      ( inv-htpy
        ( right-transpose-htpy-concat (f' ·l R) H ((H ·r (g ∘ f) ∙h f ·l R))
          ( inv-htpy (nat-htpy H ·r R))))) ∙h
    ( ap-concat-htpy'
      ( f' ·l R)
      ( inv-preserves-comp-left-whisker-comp f' g H)) ∙h
    ( inv-htpy (distributive-left-whisker-comp-concat f' (g ·l H) R))
```

Finally, we concatenate the three coherences to obtain our desired result.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f f' : A → B}
  where

  abstract
    coh-is-coherently-invertible-htpy :
      (H : f' ~ f) (F : is-coherently-invertible f) →
      coherence-is-coherently-invertible
        ( f')
        ( map-inv-is-coherently-invertible F)
        ( is-section-map-inv-is-invertible-htpy
          ( H)
          ( is-invertible-is-coherently-invertible F))
        ( is-retraction-map-inv-is-invertible-htpy
          ( H)
          ( is-invertible-is-coherently-invertible F))
    coh-is-coherently-invertible-htpy H F =
      ( coh-section-is-coherently-invertible-htpy H
        ( map-inv-is-coherently-invertible F)
        ( is-section-map-inv-is-coherently-invertible F)
        ( is-retraction-map-inv-is-coherently-invertible F)
        ( coh-is-coherently-invertible F)) ∙h
      ( coh-coh-is-coherently-invertible-htpy H
        ( map-inv-is-coherently-invertible F)
        ( is-section-map-inv-is-coherently-invertible F)
        ( is-retraction-map-inv-is-coherently-invertible F)
        ( coh-is-coherently-invertible F)) ∙h
      ( coh-retraction-is-coherently-invertible-htpy H
        ( map-inv-is-coherently-invertible F)
        ( is-section-map-inv-is-coherently-invertible F)
        ( is-retraction-map-inv-is-coherently-invertible F)
        ( coh-is-coherently-invertible F))

  is-coherently-invertible-htpy :
    f' ~ f → is-coherently-invertible f → is-coherently-invertible f'
  is-coherently-invertible-htpy H F =
    is-coherently-invertible-coherence-is-invertible
      ( is-invertible-htpy H (is-invertible-is-coherently-invertible F))
      ( coh-is-coherently-invertible-htpy H F)

  is-coherently-invertible-inv-htpy :
    f ~ f' → is-coherently-invertible f → is-coherently-invertible f'
  is-coherently-invertible-inv-htpy H =
    is-coherently-invertible-htpy (inv-htpy H)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-coherently-invertible-htpy-coherently-invertible-map :
    (e : coherently-invertible-map A B) →
    f ~ map-coherently-invertible-map e →
    is-coherently-invertible f
  is-coherently-invertible-htpy-coherently-invertible-map (e , E) H =
    is-coherently-invertible-htpy H E

  is-coherently-invertible-inv-htpy-coherently-invertible-map :
    (e : coherently-invertible-map A B) →
    map-coherently-invertible-map e ~ f →
    is-coherently-invertible f
  is-coherently-invertible-inv-htpy-coherently-invertible-map (e , E) H =
    is-coherently-invertible-inv-htpy H E
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
  id-coherently-invertible-map =
    ( id , is-coherently-invertible-id)

  is-transpose-coherently-invertible-id :
    is-transpose-coherently-invertible (id {A = A})
  is-transpose-coherently-invertible-id =
    is-transpose-coherently-invertible-map-inv-is-coherently-invertible
      ( is-coherently-invertible-id)

  id-transpose-coherently-invertible-map :
    transpose-coherently-invertible-map A A
  id-transpose-coherently-invertible-map =
    ( id , is-transpose-coherently-invertible-id)
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

### Composition of coherently invertible maps

```agda
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
    ( ap-concat-htpy
      ( ( g) ·l
        ( is-section-map-inv-is-coherently-invertible F) ·r
        ( map-inv-is-coherently-invertible G ∘ g ∘ f))
      ( coh-is-coherently-invertible G ·r f)) ∙h
    ( right-whisker-comp²
      ( ( nat-htpy (g ·l is-section-map-inv-is-coherently-invertible F)) ·r
        ( is-retraction-map-inv-is-coherently-invertible G))
      ( f)) ∙h
    ( ap-binary-concat-htpy
      ( inv-preserves-comp-left-whisker-comp
          ( g ∘ f)
          ( map-inv-is-coherently-invertible F)
          ( is-retraction-map-inv-is-coherently-invertible G ·r f))
      ( ( left-whisker-comp² g (coh-is-coherently-invertible F)) ∙h
        ( preserves-comp-left-whisker-comp g f
          ( is-retraction-map-inv-is-coherently-invertible F)))) ∙h
    ( inv-htpy
      ( distributive-left-whisker-comp-concat
        ( g ∘ f)
        ( ( map-inv-is-coherently-invertible F) ·l
          ( is-retraction-map-inv-is-coherently-invertible G ·r f))
        ( is-retraction-map-inv-is-coherently-invertible F)))

  is-coherently-invertible-comp : is-coherently-invertible (g ∘ f)
  is-coherently-invertible-comp =
    is-coherently-invertible-coherence-is-invertible
      ( is-invertible-comp g f
        ( is-invertible-is-coherently-invertible G)
        ( is-invertible-is-coherently-invertible F))
      ( coh-is-coherently-invertible-comp)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
    (g : B → C) (f : A → B)
    (G : is-transpose-coherently-invertible g)
    (F : is-transpose-coherently-invertible f)
  where

  coh-is-transpose-coherently-invertible-comp :
    coherence-is-transpose-coherently-invertible
      ( g ∘ f)
      ( map-inv-is-invertible-comp g f
        ( is-invertible-is-transpose-coherently-invertible G)
        ( is-invertible-is-transpose-coherently-invertible F))
      ( is-section-map-inv-is-invertible-comp g f
        ( is-invertible-is-transpose-coherently-invertible G)
        ( is-invertible-is-transpose-coherently-invertible F))
      ( is-retraction-map-inv-is-invertible-comp g f
        ( is-invertible-is-transpose-coherently-invertible G)
        ( is-invertible-is-transpose-coherently-invertible F))
  coh-is-transpose-coherently-invertible-comp =
    coh-is-coherently-invertible-comp
      ( map-inv-is-transpose-coherently-invertible F)
      ( map-inv-is-transpose-coherently-invertible G)
      ( is-coherently-invertible-map-inv-is-transpose-coherently-invertible F)
      ( is-coherently-invertible-map-inv-is-transpose-coherently-invertible G)

  is-transpose-coherently-invertible-comp :
    is-transpose-coherently-invertible (g ∘ f)
  is-transpose-coherently-invertible-comp =
    is-transpose-coherently-invertible-transpose-coherence-is-invertible
      ( is-invertible-comp g f
        ( is-invertible-is-transpose-coherently-invertible G)
        ( is-invertible-is-transpose-coherently-invertible F))
      ( coh-is-transpose-coherently-invertible-comp)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  comp-coherently-invertible-map :
    coherently-invertible-map B C →
    coherently-invertible-map A B →
    coherently-invertible-map A C
  comp-coherently-invertible-map (g , G) (f , F) =
    ( g ∘ f , is-coherently-invertible-comp g f G F)

  comp-transpose-coherently-invertible-map :
    transpose-coherently-invertible-map B C →
    transpose-coherently-invertible-map A B →
    transpose-coherently-invertible-map A C
  comp-transpose-coherently-invertible-map (g , G) (f , F) =
    ( g ∘ f , is-transpose-coherently-invertible-comp g f G F)
```

### The 3-for-2 property of coherently invertible maps

The
{{#concept "3-for-2 property" Disambiguation="of coherently invertible maps"}}
of coherently invertible maps asserts that for any
[commuting triangle](foundation-core.commuting-triangles-of-maps.md) of maps

```text
       h
  A ------> B
   \       /
   f\     /g
     \   /
      ∨ ∨
       X,
```

if two of the three maps are coherently invertible, then so is the third.

We also record special cases of the 3-for-2 property of coherently invertible
maps, where we only assume maps `g : B → X` and `h : A → B`. In this special
case, we set `f := g ∘ h` and the triangle commutes by `refl-htpy`.

[André Joyal](https://en.wikipedia.org/wiki/André_Joyal) proposed calling this
property the 3-for-2 property, despite most mathematicians calling it the
_2-out-of-3 property_. The story goes that on the produce market is is common to
advertise a discount as "3-for-2". If you buy two apples, then you get the third
for free. Similarly, if you prove that two maps in a commuting triangle are
coherently invertible, then you get the third proof for free.

#### The left map in a commuting triangle is coherently invertible if the other two maps are

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (T : f ~ g ∘ h)
  where

  is-coherently-invertible-left-map-triangle :
    is-coherently-invertible h →
    is-coherently-invertible g →
    is-coherently-invertible f
  is-coherently-invertible-left-map-triangle H G =
    is-coherently-invertible-htpy T (is-coherently-invertible-comp g h G H)
```

#### The right map in a commuting triangle is coherently invertible if the other two maps are

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (T : f ~ g ∘ h)
  where

  is-coherently-invertible-right-map-triangle :
    is-coherently-invertible f →
    is-coherently-invertible h →
    is-coherently-invertible g
  is-coherently-invertible-right-map-triangle F H =
    is-coherently-invertible-htpy
      ( ( g ·l inv-htpy (is-section-map-inv-is-coherently-invertible H)) ∙h
        ( inv-htpy T ·r map-inv-is-coherently-invertible H))
      ( is-coherently-invertible-comp
        ( f)
        ( map-inv-is-coherently-invertible H)
        ( F)
        ( is-coherently-invertible-map-inv-is-coherently-invertible H))
```

#### The top map in a commuting triangle is coherently invertible if the other two maps are

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (T : f ~ g ∘ h)
  where

  is-coherently-invertible-top-map-triangle :
    is-coherently-invertible g →
    is-coherently-invertible f →
    is-coherently-invertible h
  is-coherently-invertible-top-map-triangle G F =
    is-coherently-invertible-htpy
      ( ( inv-htpy (is-retraction-map-inv-is-coherently-invertible G) ·r h) ∙h
        ( map-inv-is-coherently-invertible G ·l inv-htpy T))
      ( is-coherently-invertible-comp
        ( map-inv-is-coherently-invertible G)
        ( f)
        ( is-coherently-invertible-map-inv-is-coherently-invertible G)
        ( F))
```

#### If a composite and its right factor are coherently invertible, then so is its left factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  is-coherently-invertible-left-factor :
    (g : B → X) (h : A → B) →
    is-coherently-invertible (g ∘ h) →
    is-coherently-invertible h →
    is-coherently-invertible g
  is-coherently-invertible-left-factor g h GH H =
    is-coherently-invertible-right-map-triangle (g ∘ h) g h refl-htpy GH H
```

#### If a composite and its left factor are coherently invertible, then so is its right factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  is-coherently-invertible-right-factor :
    (g : B → X) (h : A → B) →
    is-coherently-invertible g →
    is-coherently-invertible (g ∘ h) →
    is-coherently-invertible h
  is-coherently-invertible-right-factor g h G GH =
    is-coherently-invertible-top-map-triangle (g ∘ h) g h refl-htpy G GH
```

### Any section of a coherently invertible map is coherently invertible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-coherently-invertible-is-section :
    {f : A → B} {g : B → A} →
    is-coherently-invertible f → f ∘ g ~ id → is-coherently-invertible g
  is-coherently-invertible-is-section {f = f} {g} F H =
    is-coherently-invertible-top-map-triangle id f g
      ( inv-htpy H)
      ( F)
      ( is-coherently-invertible-id)
```

### Any retraction of a coherently invertible map is coherently invertible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-coherently-invertible-is-retraction :
    {f : A → B} {g : B → A} →
    is-coherently-invertible f → (g ∘ f) ~ id → is-coherently-invertible g
  is-coherently-invertible-is-retraction {f = f} {g} F H =
    is-coherently-invertible-right-map-triangle id g f
      ( inv-htpy H)
      ( is-coherently-invertible-id)
      ( F)
```

### If a section of `f` is coherently invertible, then `f` is coherently invertible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

    is-coherently-invertible-is-coherently-invertible-section :
      (s : section f) →
      is-coherently-invertible (map-section f s) → is-coherently-invertible f
    is-coherently-invertible-is-coherently-invertible-section (g , G) S =
      is-coherently-invertible-is-retraction S G
```

### If a retraction of `f` is coherently invertible, then `f` is coherently invertible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-coherently-invertible-is-coherently-invertible-retraction :
      (r : retraction f) →
      is-coherently-invertible (map-retraction f r) → is-coherently-invertible f
    is-coherently-invertible-is-coherently-invertible-retraction (g , G) R =
      is-coherently-invertible-is-section R G
```

### Any section of a coherently invertible map is homotopic to its inverse

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : coherently-invertible-map A B)
  where

  htpy-map-inv-coherently-invertible-map-section :
    (f : section (map-coherently-invertible-map e)) →
    map-inv-coherently-invertible-map e ~
    map-section (map-coherently-invertible-map e) f
  htpy-map-inv-coherently-invertible-map-section =
    htpy-map-inv-invertible-map-section
      ( invertible-map-coherently-invertible-map e)
```

### Any retraction of a coherently invertible map is homotopic to its inverse

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : coherently-invertible-map A B)
  where

  htpy-map-inv-coherently-invertible-map-retraction :
    (f : retraction (map-coherently-invertible-map e)) →
    map-inv-coherently-invertible-map e ~
    map-retraction (map-coherently-invertible-map e) f
  htpy-map-inv-coherently-invertible-map-retraction =
    htpy-map-inv-invertible-map-retraction
      ( invertible-map-coherently-invertible-map e)
```

## References

{{#bibliography}}

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).

## External links

- [Adjoint equivalences](https://1lab.dev/1Lab.Equiv.HalfAdjoint.html) at 1lab
- [adjoint equivalence](https://ncatlab.org/nlab/show/adjoint+equivalence) at
  $n$Lab
