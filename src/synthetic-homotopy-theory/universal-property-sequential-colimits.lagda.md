# The universal property of sequential colimits

```agda
module synthetic-homotopy-theory.universal-property-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.equivalences
open import foundation.equivalences-contractible-types
open import foundation.fibers-of-maps
open import foundation.function-extensionality-axiom
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.precomposition-functions
open import foundation.retractions
open import foundation.sections
open import foundation.subtype-identity-principle
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams
open import synthetic-homotopy-theory.equivalences-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-coequalizers
```

</details>

## Idea

Given a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)`, consider a
[cocone under it](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
`c` with vertex `X`. The **universal property of sequential colimits** is the
statement that the cocone postcomposition map

```text
cocone-map-sequential-diagram : (X → Y) → cocone-sequential-diagram Y
```

is an [equivalence](foundation.equivalences.md).

A sequential colimit `X` may be visualized as a "point in infinity" in the
diagram

```text
     a₀      a₁      a₂     i
 A₀ ---> A₁ ---> A₂ ---> ⋯ --> X.
```

## Definitions

### The universal property of sequential colimits

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  universal-property-sequential-colimit : UUω
  universal-property-sequential-colimit =
    {l : Level} (Y : UU l) → is-equiv (cocone-map-sequential-diagram c {Y = Y})
```

### The map induced by the universal property of sequential colimits

The universal property allows us to construct a map from the colimit by
providing a cocone under the sequential diagram.

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  { c : cocone-sequential-diagram A X} {Y : UU l3}
  ( up-sequential-colimit : universal-property-sequential-colimit c)
  where

  equiv-universal-property-sequential-colimit :
    (X → Y) ≃ cocone-sequential-diagram A Y
  pr1 equiv-universal-property-sequential-colimit =
    cocone-map-sequential-diagram c
  pr2 equiv-universal-property-sequential-colimit =
    up-sequential-colimit Y

  map-universal-property-sequential-colimit :
    cocone-sequential-diagram A Y → (X → Y)
  map-universal-property-sequential-colimit =
    map-inv-is-equiv (up-sequential-colimit Y)
```

## Properties

### The mediating map obtained by the universal property is unique

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  { c : cocone-sequential-diagram A X} {Y : UU l3}
  ( up-sequential-colimit : universal-property-sequential-colimit c)
  ( c' : cocone-sequential-diagram A Y)
  where

  htpy-cocone-universal-property-sequential-colimit :
    htpy-cocone-sequential-diagram
      ( cocone-map-sequential-diagram c
        ( map-universal-property-sequential-colimit
          ( up-sequential-colimit)
          ( c')))
      ( c')
  htpy-cocone-universal-property-sequential-colimit =
    htpy-eq-cocone-sequential-diagram A
      ( cocone-map-sequential-diagram c
        ( map-universal-property-sequential-colimit
          ( up-sequential-colimit)
          ( c')))
      ( c')
      ( is-section-map-inv-is-equiv (up-sequential-colimit Y) c')

  abstract
    uniqueness-map-universal-property-sequential-colimit :
      is-contr
        ( Σ ( X → Y)
            ( λ h →
              htpy-cocone-sequential-diagram
                ( cocone-map-sequential-diagram c h)
                ( c')))
    uniqueness-map-universal-property-sequential-colimit =
      is-contr-equiv'
        ( fiber (cocone-map-sequential-diagram c) c')
        ( equiv-tot
          ( λ h →
            extensionality-cocone-sequential-diagram A
              ( cocone-map-sequential-diagram c h)
              ( c')))
        ( is-contr-map-is-equiv (up-sequential-colimit Y) c')
```

### The cocone of a sequential colimit induces the identity function by its universal property

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  where

  compute-map-universal-property-sequential-colimit-id :
    map-universal-property-sequential-colimit up-c c ~ id
  compute-map-universal-property-sequential-colimit-id =
    htpy-eq
      ( ap pr1
        ( eq-is-contr'
          ( uniqueness-map-universal-property-sequential-colimit up-c c)
          ( ( map-universal-property-sequential-colimit up-c c) ,
            ( htpy-cocone-universal-property-sequential-colimit up-c c))
          ( id , htpy-cocone-map-id-sequential-diagram A c)))
```

### Homotopies between cocones under sequential diagrams induce homotopies between the induced maps out of sequential colimits

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {Y : UU l3} {c' c'' : cocone-sequential-diagram A Y}
  (H : htpy-cocone-sequential-diagram c' c'')
  where

  htpy-map-universal-property-htpy-cocone-sequential-diagram :
    map-universal-property-sequential-colimit up-c c' ~
    map-universal-property-sequential-colimit up-c c''
  htpy-map-universal-property-htpy-cocone-sequential-diagram =
    htpy-eq
      ( ap
        ( map-universal-property-sequential-colimit up-c)
        ( eq-htpy-cocone-sequential-diagram A c' c'' H))
```

### Correspondence between universal properties of sequential colimits and coequalizers

A cocone under a sequential diagram has the universal property of sequential
colimits if and only if the
[corresponding cofork](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)
has the universal property of coequalizers.

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  universal-property-sequential-colimit-universal-property-coequalizer :
    universal-property-coequalizer
      ( double-arrow-sequential-diagram A)
      ( cofork-cocone-sequential-diagram c) →
    universal-property-sequential-colimit c
  universal-property-sequential-colimit-universal-property-coequalizer
    ( up-cofork)
    ( Y) =
    is-equiv-left-map-triangle
      ( cocone-map-sequential-diagram c)
      ( cocone-sequential-diagram-cofork)
      ( cofork-map
        ( double-arrow-sequential-diagram A)
        ( cofork-cocone-sequential-diagram c))
      ( triangle-cocone-sequential-diagram-cofork c)
      ( up-cofork Y)
      ( is-equiv-cocone-sequential-diagram-cofork)

  universal-property-coequalizer-universal-property-sequential-colimit :
    universal-property-sequential-colimit c →
    universal-property-coequalizer
      ( double-arrow-sequential-diagram A)
      ( cofork-cocone-sequential-diagram c)
  universal-property-coequalizer-universal-property-sequential-colimit
    ( up-sequential-colimit)
    ( Y) =
    is-equiv-top-map-triangle
      ( cocone-map-sequential-diagram c)
      ( cocone-sequential-diagram-cofork)
      ( cofork-map
        ( double-arrow-sequential-diagram A)
        ( cofork-cocone-sequential-diagram c))
      ( triangle-cocone-sequential-diagram-cofork c)
      ( is-equiv-cocone-sequential-diagram-cofork)
      ( up-sequential-colimit Y)
```

### The universal property of colimits is preserved by equivalences of cocones under equivalences of sequential diagrams

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1} {X : UU l2} {c : cocone-sequential-diagram A X}
  {B : sequential-diagram l3} {Y : UU l4} {c' : cocone-sequential-diagram B Y}
  (e : equiv-sequential-diagram A B)
  (e' : equiv-cocone-equiv-sequential-diagram c c' e)
  where

  universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagram :
    universal-property-sequential-colimit c' →
    universal-property-sequential-colimit c
  universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagram
    up-c' =
    universal-property-sequential-colimit-universal-property-coequalizer c
      ( universal-property-coequalizer-equiv-cofork-equiv-double-arrow
        ( cofork-cocone-sequential-diagram c)
        ( cofork-cocone-sequential-diagram c')
        ( equiv-double-arrow-equiv-sequential-diagram A B e)
        ( equiv-cofork-equiv-cocone-equiv-sequential-diagram c c' e e')
        ( universal-property-coequalizer-universal-property-sequential-colimit _
          ( up-c')))

  universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagram' :
    universal-property-sequential-colimit c →
    universal-property-sequential-colimit c'
  universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagram'
    up-c =
    universal-property-sequential-colimit-universal-property-coequalizer c'
      ( universal-property-coequalizer-equiv-cofork-equiv-double-arrow'
        ( cofork-cocone-sequential-diagram c)
        ( cofork-cocone-sequential-diagram c')
        ( equiv-double-arrow-equiv-sequential-diagram A B e)
        ( equiv-cofork-equiv-cocone-equiv-sequential-diagram c c' e e')
        ( universal-property-coequalizer-universal-property-sequential-colimit _
          ( up-c)))
```

### The 3-for-2 property of the universal property of sequential colimits

Given two cocones under a sequential diagram, one of which has the universal
property of sequential colimits, and a map between their vertices, we prove that
the other has the universal property if and only if the map is an
[equivalence](foundation.equivalences.md).

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2} {Y : UU l3}
  ( c : cocone-sequential-diagram A X)
  ( c' : cocone-sequential-diagram A Y)
  ( h : X → Y)
  ( H :
    htpy-cocone-sequential-diagram (cocone-map-sequential-diagram c h) c')
  where

  inv-triangle-cocone-map-precomp-sequential-diagram :
    { l4 : Level} (Z : UU l4) →
    coherence-triangle-maps'
      ( cocone-map-sequential-diagram c')
      ( cocone-map-sequential-diagram c)
      ( precomp h Z)
  inv-triangle-cocone-map-precomp-sequential-diagram Z k =
    ( cocone-map-comp-sequential-diagram A c h k) ∙
    ( ap
      ( λ d → cocone-map-sequential-diagram d k)
      ( eq-htpy-cocone-sequential-diagram A
        ( cocone-map-sequential-diagram c h)
        ( c')
        ( H)))

  triangle-cocone-map-precomp-sequential-diagram :
    { l4 : Level} (Z : UU l4) →
    coherence-triangle-maps
      ( cocone-map-sequential-diagram c')
      ( cocone-map-sequential-diagram c)
      ( precomp h Z)
  triangle-cocone-map-precomp-sequential-diagram Z =
    inv-htpy (inv-triangle-cocone-map-precomp-sequential-diagram Z)

  abstract
    is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimit :
      universal-property-sequential-colimit c →
      universal-property-sequential-colimit c' →
      is-equiv h
    is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimit
      ( up-sequential-colimit)
      ( up-sequential-colimit') =
      is-equiv-is-equiv-precomp h
        ( λ Z →
          is-equiv-top-map-triangle
            ( cocone-map-sequential-diagram c')
            ( cocone-map-sequential-diagram c)
            ( precomp h Z)
            ( triangle-cocone-map-precomp-sequential-diagram Z)
            ( up-sequential-colimit Z)
            ( up-sequential-colimit' Z))

    universal-property-sequential-colimit-is-equiv-universal-property-sequential-colimit :
      universal-property-sequential-colimit c →
      is-equiv h →
      universal-property-sequential-colimit c'
    universal-property-sequential-colimit-is-equiv-universal-property-sequential-colimit
      ( up-sequential-colimit)
      ( is-equiv-h)
      ( Z) =
      is-equiv-left-map-triangle
        ( cocone-map-sequential-diagram c')
        ( cocone-map-sequential-diagram c)
        ( precomp h Z)
        ( triangle-cocone-map-precomp-sequential-diagram Z)
        ( is-equiv-precomp-is-equiv h is-equiv-h Z)
        ( up-sequential-colimit Z)

    universal-property-sequential-colimit-universal-property-sequential-colimit-is-equiv :
      is-equiv h →
      universal-property-sequential-colimit c' →
      universal-property-sequential-colimit c
    universal-property-sequential-colimit-universal-property-sequential-colimit-is-equiv
      ( is-equiv-h)
      ( up-sequential-colimit)
      ( Z) =
      is-equiv-right-map-triangle
        ( cocone-map-sequential-diagram c')
        ( cocone-map-sequential-diagram c)
        ( precomp h Z)
        ( triangle-cocone-map-precomp-sequential-diagram Z)
        ( up-sequential-colimit Z)
        ( is-equiv-precomp-is-equiv h is-equiv-h Z)
```

### Unique uniqueness of of sequential colimits

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2} {Y : UU l3}
  { c : cocone-sequential-diagram A X}
  ( up-c : universal-property-sequential-colimit c)
  { c' : cocone-sequential-diagram A Y}
  ( up-c' : universal-property-sequential-colimit c')
  where

  abstract
    uniquely-unique-sequential-colimit :
      is-contr
        ( Σ ( X ≃ Y)
            ( λ e →
              htpy-cocone-sequential-diagram
                ( cocone-map-sequential-diagram c (map-equiv e))
                ( c')))
    uniquely-unique-sequential-colimit =
      is-torsorial-Eq-subtype
        ( uniqueness-map-universal-property-sequential-colimit up-c c')
        ( is-property-is-equiv)
        ( map-universal-property-sequential-colimit up-c c')
        ( htpy-cocone-universal-property-sequential-colimit up-c c')
        ( is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimit
          ( c)
          ( c')
          ( map-universal-property-sequential-colimit up-c c')
          ( htpy-cocone-universal-property-sequential-colimit up-c c')
          ( up-c)
          ( up-c'))
```

### Inclusion maps of a sequential colimit under a sequential diagram of equivalences are equivalences

If a sequential diagram `(A, a)` with a colimit `X` and inclusion maps
`iₙ : Aₙ → X` has the property that all `aₙ : Aₙ → Aₙ₊₁` are equivalences, then
all the inclusion maps are also equivalences.

It suffices to show that `i₀ : A₀ → X` is an equivalence, since then the
statement follows by induction on `n` and the 3-for-2 property of equivalences:
we have [commuting triangles](foundation-core.commuting-triangles-of-maps.md)

```text
        aₙ
  Aₙ ------> Aₙ₊₁
    \   ≃   /
  ≃  \     /
   iₙ \   / iₙ₊₁
       ∨ ∨
        X ,
```

where `aₙ` is an equivalence by assumption, and `iₙ` is an equivalence by the
induction hypothesis, making `iₙ₊₁` an equivalence.

To show that `i₀` is an equivalence, we use the map

```text
  first-map-cocone-sequential-colimit : {Y : 𝒰} → cocone A Y → (A₀ → Y)
```

selecting the first map of a cocone `j₀ : A₀ → Y`, which makes the following
triangle commute:

```text
        cocone-map
  X → Y ----------> cocone A Y
        \         /
         \       /
   - ∘ i₀ \     / first-map-cocone-sequential-colimit
           \   /
            ∨ ∨
          A₀ → Y .
```

By `X` being a colimit we have that `cocone-map` is an equivalence. Then it
suffices to show that `first-map-cocone-sequential-colimit` is an equivalence,
because it would follow that `- ∘ i₀` is an equivalence, which by the
[universal property of equivalences](foundation.universal-property-equivalences.md)
implies that `iₒ` is an equivalence.

To show that `first-map-cocone-sequential-colimit` is an equivalence, we
construct an inverse map

```text
  cocone-first-map-is-equiv-sequential-diagram : {Y : 𝒰} → (A₀ → Y) → cocone A Y ,
```

which to every `f : A₀ → Y` assigns the cocone

```text
       a₀       a₁
  A₀ ----> A₁ ----> A₂ ----> ⋯
    \      |      /
     \     |     /
      \ f ∘ a₀⁻¹/
     f \   |   / f ∘ a₁⁻¹ ∘ a₀⁻¹
        \  |  /
         ∨ ∨ ∨
           Y ,
```

where the coherences are witnesses that `aₙ⁻¹` are retractions of `aₙ`.

Since the first inclusion map in this cocone is `f`, it is immediate that
`cocone-first-map-is-equiv-sequential-diagram` is a section of
`first-map-cocone-sequential-colimit`. To show that it is a retraction we need a
homotopy for any cocone `c` between itself and the cocone induced by its first
map `j₀ : A₀ → Y`. We refer to the cocone induced by `j₀` as `(j₀')`.

The homotopy of cocones consists of homotopies

```text
  Kₙ : (j₀')ₙ ~ jₙ ,
```

which we construct by induction as

```text
  K₀ : (j₀')₀ ≐ j₀ ~ j₀     by reflexivity
  Kₙ₊₁ : (j₀')ₙ₊₁
       ≐ (j₀')ₙ ∘ aₙ⁻¹      by definition
       ~ jₙ ∘ aₙ⁻¹          by Kₙ
       ~ jₙ₊₁ ∘ aₙ ∘ aₙ⁻¹   by coherence Hₙ of c
       ~ jₙ₊₁               by aₙ⁻¹ being a section of aₙ ,
```

and a coherence datum which upon some pondering boils down to the following
[commuting square of homotopies](foundation-core.commuting-squares-of-homotopies.md):

```text
                        Kₙ ·r (aₙ⁻¹ ∘ aₙ)                Hₙ ·r (aₙ⁻¹ ∘ aₙ)
     (j₀')ₙ ∘ aₙ⁻¹ ∘ aₙ ----------------> jₙ ∘ aₙ⁻¹ ∘ aₙ ----------------> jₙ₊₁ ∘ aₙ ∘ aₙ⁻¹ ∘ aₙ
              |                                 |                                    |
              |                                 |                                    |
  (j₀')ₙ ·l is-retraction aₙ⁻¹      jₙ ·l is-retraction aₙ⁻¹            jₙ₊₁ ·l is-section aₙ⁻¹ ·r aₙ
              |                                 |                                    |
              ∨                                 ∨                                    ∨
           (j₀')ₙ ----------------------------> jₙ -------------------------->  jₙ₊₁ ∘ aₙ .
                               Kₙ                                 Hₙ
```

This rectangle is almost a pasting of the squares of naturality of `Kₙ` and `Hₙ`
with respect to `is-retraction` --- it remains to pass from
`(jₙ₊₁ ∘ aₙ) ·l is-retraction aₙ⁻¹` to `jₙ₊₁ ·l is-section aₙ⁻¹ ·r aₙ`, which we
can do by applying the coherence of
[coherently invertible maps](foundation-core.coherently-invertible-maps.md).

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {Y : UU l2}
  (equivs : (n : ℕ) → is-equiv (map-sequential-diagram A n))
  where

  map-cocone-first-map-is-equiv-sequential-diagram :
    (family-sequential-diagram A 0 → Y) →
    (n : ℕ) →
    family-sequential-diagram A n → Y
  map-cocone-first-map-is-equiv-sequential-diagram f zero-ℕ =
    f
  map-cocone-first-map-is-equiv-sequential-diagram f (succ-ℕ n) =
    ( map-cocone-first-map-is-equiv-sequential-diagram f n) ∘
    ( map-inv-is-equiv (equivs n))

  inv-htpy-cocone-first-map-is-equiv-sequential-diagram :
    (f : family-sequential-diagram A 0 → Y) →
    (n : ℕ) →
    coherence-triangle-maps'
      ( map-cocone-first-map-is-equiv-sequential-diagram f n)
      ( ( map-cocone-first-map-is-equiv-sequential-diagram f n) ∘
        ( map-inv-is-equiv (equivs n)))
      ( map-sequential-diagram A n)
  inv-htpy-cocone-first-map-is-equiv-sequential-diagram f n =
    ( map-cocone-first-map-is-equiv-sequential-diagram f n) ·l
    ( is-retraction-map-inv-is-equiv (equivs n))

  htpy-cocone-first-map-is-equiv-sequential-diagram :
    (f : family-sequential-diagram A 0 → Y) →
    (n : ℕ) →
    coherence-triangle-maps
      ( map-cocone-first-map-is-equiv-sequential-diagram f n)
      ( ( map-cocone-first-map-is-equiv-sequential-diagram f n) ∘
        ( map-inv-is-equiv (equivs n)))
      ( map-sequential-diagram A n)
  htpy-cocone-first-map-is-equiv-sequential-diagram f n =
    inv-htpy (inv-htpy-cocone-first-map-is-equiv-sequential-diagram f n)

  cocone-first-map-is-equiv-sequential-diagram :
    (family-sequential-diagram A 0 → Y) → cocone-sequential-diagram A Y
  pr1 (cocone-first-map-is-equiv-sequential-diagram f) =
    map-cocone-first-map-is-equiv-sequential-diagram f
  pr2 (cocone-first-map-is-equiv-sequential-diagram f) =
    htpy-cocone-first-map-is-equiv-sequential-diagram f

  is-section-cocone-first-map-is-equiv-sequential-diagram :
    is-section
      ( first-map-cocone-sequential-diagram)
      ( cocone-first-map-is-equiv-sequential-diagram)
  is-section-cocone-first-map-is-equiv-sequential-diagram = refl-htpy

  htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagram :
    (c : cocone-sequential-diagram A Y) →
    (n : ℕ) →
    map-cocone-first-map-is-equiv-sequential-diagram
      ( first-map-cocone-sequential-diagram c)
      ( n) ~
    map-cocone-sequential-diagram c n
  htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagram
    c zero-ℕ = refl-htpy
  htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagram
    c (succ-ℕ n) =
    ( ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagram c
        ( n)) ·r
      ( map-inv-is-equiv (equivs n))) ∙h
    ( ( coherence-cocone-sequential-diagram c n) ·r
      ( map-inv-is-equiv (equivs n))) ∙h
    ( ( map-cocone-sequential-diagram c (succ-ℕ n)) ·l
      ( is-section-map-inv-is-equiv (equivs n)))

  coh-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagram :
    (c : cocone-sequential-diagram A Y) →
    coherence-htpy-cocone-sequential-diagram
      ( cocone-first-map-is-equiv-sequential-diagram
        ( first-map-cocone-sequential-diagram c))
      ( c)
      ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagram c)
  coh-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagram c n =
    inv-htpy-left-transpose-htpy-concat
      ( inv-htpy-cocone-first-map-is-equiv-sequential-diagram
        ( first-map-cocone-sequential-diagram c)
        ( n))
      ( ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagram c
          ( n)) ∙h
        ( coherence-cocone-sequential-diagram c n))
      ( ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagram c
          ( succ-ℕ n)) ·r
        ( map-sequential-diagram A n))
      ( concat-right-homotopy-coherence-square-homotopies
        ( ( ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagram
              ( c)
              ( n)) ∙h
            ( coherence-cocone-sequential-diagram c n)) ·r
          ( map-inv-is-equiv (equivs n) ∘ map-sequential-diagram A n))
        ( ( map-cocone-first-map-is-equiv-sequential-diagram
            ( first-map-cocone-sequential-diagram c)
            ( n)) ·l
          ( is-retraction-map-inv-is-equiv (equivs n)))
        ( ( ( map-cocone-sequential-diagram c (succ-ℕ n)) ∘
            ( map-sequential-diagram A n)) ·l
          ( is-retraction-map-inv-is-equiv (equivs n)))
        ( ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagram
            ( c)
            ( n)) ∙h
          ( coherence-cocone-sequential-diagram c n))
        ( ( inv-preserves-comp-left-whisker-comp
            ( map-cocone-sequential-diagram c (succ-ℕ n))
            ( map-sequential-diagram A n)
            ( is-retraction-map-inv-is-equiv (equivs n))) ∙h
          ( left-whisker-comp²
            ( map-cocone-sequential-diagram c (succ-ℕ n))
            ( inv-htpy (coherence-map-inv-is-equiv (equivs n)))))
        ( λ a →
          inv-nat-htpy
            ( ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagram
                ( c)
                ( n)) ∙h
              ( coherence-cocone-sequential-diagram c n))
            ( is-retraction-map-inv-is-equiv (equivs n) a)))

  abstract
    is-retraction-cocone-first-map-is-equiv-sequential-diagram :
      is-retraction
        ( first-map-cocone-sequential-diagram)
        ( cocone-first-map-is-equiv-sequential-diagram)
    is-retraction-cocone-first-map-is-equiv-sequential-diagram c =
      eq-htpy-cocone-sequential-diagram A _ _
        ( ( htpy-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagram
            ( c)) ,
          ( coh-htpy-is-retraction-cocone-first-map-is-equiv-sequential-diagram
            ( c)))

  is-equiv-first-map-cocone-is-equiv-sequential-diagram :
    is-equiv first-map-cocone-sequential-diagram
  is-equiv-first-map-cocone-is-equiv-sequential-diagram =
    is-equiv-is-invertible
      ( cocone-first-map-is-equiv-sequential-diagram)
      ( is-section-cocone-first-map-is-equiv-sequential-diagram)
      ( is-retraction-cocone-first-map-is-equiv-sequential-diagram)

module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  (equivs : (n : ℕ) → is-equiv (map-sequential-diagram A n))
  where

  triangle-first-map-cocone-sequential-colimit-is-equiv :
    {l3 : Level} {Y : UU l3} →
    coherence-triangle-maps
      ( precomp (first-map-cocone-sequential-diagram c) Y)
      ( first-map-cocone-sequential-diagram)
      ( cocone-map-sequential-diagram c)
  triangle-first-map-cocone-sequential-colimit-is-equiv = refl-htpy

  is-equiv-first-map-cocone-sequential-colimit-is-equiv :
    is-equiv (first-map-cocone-sequential-diagram c)
  is-equiv-first-map-cocone-sequential-colimit-is-equiv =
    is-equiv-is-equiv-precomp
      ( first-map-cocone-sequential-diagram c)
      ( λ Y →
        is-equiv-left-map-triangle
          ( precomp (first-map-cocone-sequential-diagram c) Y)
          ( first-map-cocone-sequential-diagram)
          ( cocone-map-sequential-diagram c)
          ( triangle-first-map-cocone-sequential-colimit-is-equiv)
          ( up-c Y)
          ( is-equiv-first-map-cocone-is-equiv-sequential-diagram equivs))

  is-equiv-map-cocone-sequential-colimit-is-equiv :
    (n : ℕ) → is-equiv (map-cocone-sequential-diagram c n)
  is-equiv-map-cocone-sequential-colimit-is-equiv zero-ℕ =
    is-equiv-first-map-cocone-sequential-colimit-is-equiv
  is-equiv-map-cocone-sequential-colimit-is-equiv (succ-ℕ n) =
    is-equiv-right-map-triangle
      ( map-cocone-sequential-diagram c n)
      ( map-cocone-sequential-diagram c (succ-ℕ n))
      ( map-sequential-diagram A n)
      ( coherence-cocone-sequential-diagram c n)
      ( is-equiv-map-cocone-sequential-colimit-is-equiv n)
      ( equivs n)
```

### A sequential colimit of contractible types is contractible

A sequential diagram of contractible types consists of equivalences, as shown in
[`sequential-diagrams`](synthetic-homotopy-theory.sequential-diagrams.md), so
the inclusion maps into a colimit are equivalences as well, as shown above. In
particular, there is an equivalence `i₀ : A₀ ≃ X`, and since `A₀` is
contractible, it follows that `X` is contractible.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  where

  is-contr-sequential-colimit-is-contr-sequential-diagram :
    ((n : ℕ) → is-contr (family-sequential-diagram A n)) →
    is-contr X
  is-contr-sequential-colimit-is-contr-sequential-diagram contrs =
    is-contr-is-equiv'
      ( family-sequential-diagram A 0)
      ( map-cocone-sequential-diagram c 0)
      ( is-equiv-map-cocone-sequential-colimit-is-equiv
        ( up-c)
        ( is-equiv-sequential-diagram-is-contr contrs)
        ( 0))
      ( contrs 0)
```
