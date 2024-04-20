# The dependent pullback property of pushouts

```agda
module synthetic-homotopy-theory.dependent-pullback-property-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.constant-type-families
open import foundation.dependent-pair-types
open import foundation.dependent-sums-pullbacks
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.precomposition-functions
open import foundation.pullbacks
open import foundation.transport-along-identifications
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import orthogonal-factorization-systems.lifts-families-of-elements
open import orthogonal-factorization-systems.precomposition-lifts-families-of-elements

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pullback-property-pushouts
```

</details>

## Idea

The **dependent pullback property** of
[pushouts](synthetic-homotopy-theory.pushouts.md) asserts that the type of
sections of a type family over a pushout can be expressed as a
[pullback](foundation.pullbacks.md).

The fact that the dependent pullback property of pushouts is
[logically equivalent](foundation.logical-equivalences.md) to the
[dependent universal property](synthetic-homotopy-theory.dependent-universal-property-pushouts.md)
of pushouts is shown in
[`dependent-universal-property-pushouts`](synthetic-homotopy-theory.dependent-universal-property-pushouts.md).

## Definition

```agda
cone-dependent-pullback-property-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  let i = pr1 c
      j = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  cone
    ( λ (h : (a : A) → P (i a)) → λ (s : S) → tr P (H s) (h (f s)))
    ( λ (h : (b : B) → P (j b)) → λ s → h (g s))
    ( (x : X) → P x)
pr1 (cone-dependent-pullback-property-pushout f g (i , j , H) P) h a =
  h (i a)
pr1 (pr2 (cone-dependent-pullback-property-pushout f g (i , j , H) P)) h b =
  h (j b)
pr2 (pr2 (cone-dependent-pullback-property-pushout f g (i , j , H) P)) h =
  eq-htpy (λ s → apd h (H s))

dependent-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
dependent-pullback-property-pushout l {S} {A} {B} f g {X} (i , j , H) =
  (P : X → UU l) →
  is-pullback
    ( λ (h : (a : A) → P (i a)) → λ s → tr P (H s) (h (f s)))
    ( λ (h : (b : B) → P (j b)) → λ s → h (g s))
    ( cone-dependent-pullback-property-pushout f g (i , j , H) P)
```

## Properties

### The dependent pullback property is logically equivalent to the pullback property

Consider a [cocone](synthetic-homotopy-theory.cocones-under-spans.md)

```text
        g
    S -----> B
    |        |
  f |        | j
    ∨        ∨
    A -----> X  .
        i
```

The nondependent pullback property follows from the dependent one by applying
the dependent pullback property to the constant type family `λ _ → Y`.

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  where

  pullback-property-dependent-pullback-property-pushout :
    ({l : Level} → dependent-pullback-property-pushout l f g c) →
    ({l : Level} → pullback-property-pushout l f g c)
  pullback-property-dependent-pullback-property-pushout dpp-c Y =
    is-pullback-htpy
      ( λ h →
        eq-htpy
          ( λ s →
            inv
              ( tr-constant-type-family
                ( coherence-square-cocone f g c s)
                ( h (f s)))))
      ( refl-htpy)
      ( cone-dependent-pullback-property-pushout f g c (λ _ → Y))
      ( ( refl-htpy) ,
        ( refl-htpy) ,
        ( λ h →
          ( right-unit) ∙
          ( ap
            ( eq-htpy)
            ( eq-htpy
              ( λ s →
                left-transpose-eq-concat _ _ _
                  ( inv
                    ( apd-constant-type-family h
                      ( coherence-square-cocone f g c s))))) ∙
          ( eq-htpy-concat-htpy _ _))))
      ( dpp-c (λ _ → Y))
```

In the converse direction, we use the fact that by the
[type theoretic principle of choice](foundation.type-theoretic-principle-of-choice.md),
dependent functions distribute over Σ-types. That, and a handful of technical
lemmas about [transport](foundation.transport-along-identifications.md) in
[precomposed type families](foundation.precomposition-type-families.md) and
[precomposition](orthogonal-factorization-systems.precomposition-lifts-families-of-elements.md)
in
[lifts of families of elements](orthogonal-factorization-systems.lifts-families-of-elements.md),
allow us to construct the following
[commuting cube](foundation.commuting-cubes-of-maps.md):

```text
                                Σ (h : X → X) ((x : X) → P (h x))
                                       /        |        \
                                     /          |          \
                                   /            |            \
                                 /              |              \
                               /                |                \
                             /                  |                  \
                           /                    |                    \
                         ∨                      ∨                      ∨
  Σ (h : A → X) ((a : A) → P (h a))    X → Σ (x : X) (P x)    Σ (h : B → X) ((b : B) → P (h b))
                         |\             /               \             /|
                         |  \         /                   \         /  |
                         |    \     /                       \     /    |
                         |      \ /                           \ /      |
                         |      / \                           / \      |
                         |    /     \                       /     \    |
                         |  /         \                   /         \  |
                         ∨∨             ∨               ∨             ∨∨
         A → Σ (x : X) (P x)    Σ (h : S → X) ((s : S) → P (h s))    B → Σ (x : X) (P x)
                           \                    |                    /
                             \                  |                  /
                               \                |                /
                                 \              |              /
                                   \            |            /
                                     \          |          /
                                       \        |        /
                                         ∨      ∨      ∨
                                       S → Σ (x : X) (P x) .
```

The bottom square is the induced precomposition square for our fixed cocone, so
by the assumed pullback property, instantiated at the type `Σ (x : X) (P x)`,
it's a pullback. The top square is constructed by precomposition of maps on the
first component, and by precomposition of lifts of families of elements on the
second component. Since vertical maps are equivalences, by the principle of
choice, and the bottom square is a pullback, we conclude that the top square is
a pullback.

Observe that restricting the top square to its first component, we again get the
induced precomposition square, this time instantiated at `X`, so that is also a
pullback. Hence the top square is a pullback of total spaces over a pullback
square, which implies that we get a family of pullback squares of the fibers,
i.e. for every `h : X → X` we have a pullback

```text
    (x : X) → P (h x) ---------> (b : B) → P (h (j b))
            | ⌟                           |
            |                             |
            |                             |
            |                             |
            ∨                             ∨
  (a : A) → P (h (i a)) -----> (s : S) → P (h (j (g s))) ,
```

and instantiating for `id : X → X` gives us exactly a proof of the dependent
pullback property.

```agda
  cone-family-dependent-pullback-property :
    {l : Level} (P : X → UU l) →
    cone-family
      ( lift-family-of-elements P)
      ( precomp-lift-family-of-elements P f)
      ( precomp-lift-family-of-elements P g)
      ( cone-pullback-property-pushout f g c X)
      ( lift-family-of-elements P)
  pr1 (cone-family-dependent-pullback-property P γ) h =
    h ∘ horizontal-map-cocone f g c
  pr1 (pr2 (cone-family-dependent-pullback-property P γ)) h =
    h ∘ vertical-map-cocone f g c
  pr2 (pr2 (cone-family-dependent-pullback-property P γ)) =
    triangle-precomp-lift-family-of-elements-htpy P γ
      ( coherence-square-cocone f g c)

  is-pullback-cone-family-dependent-pullback-family :
    {l : Level} (P : X → UU l) →
    ({l : Level} → pullback-property-pushout l f g c) →
    (γ : X → X) →
    is-pullback
      ( ( tr
          ( lift-family-of-elements P)
          ( htpy-precomp (coherence-square-cocone f g c) X γ)) ∘
        ( precomp-lift-family-of-elements P f
          ( γ ∘ horizontal-map-cocone f g c)))
      ( precomp-lift-family-of-elements P g
        ( γ ∘ vertical-map-cocone f g c))
      ( cone-family-dependent-pullback-property P γ)
  is-pullback-cone-family-dependent-pullback-family P pp-c =
    is-pullback-family-is-pullback-tot
      ( lift-family-of-elements P)
      ( precomp-lift-family-of-elements P f)
      ( precomp-lift-family-of-elements P g)
      ( cone-pullback-property-pushout f g c X)
      ( cone-family-dependent-pullback-property P)
      ( pp-c X)
      ( is-pullback-top-is-pullback-bottom-cube-is-equiv
        ( precomp (horizontal-map-cocone f g c) (Σ X P))
        ( precomp (vertical-map-cocone f g c) (Σ X P))
        ( precomp f (Σ X P))
        ( precomp g (Σ X P))
        ( precomp-lifted-family-of-elements P (horizontal-map-cocone f g c))
        ( precomp-lifted-family-of-elements P (vertical-map-cocone f g c))
        ( precomp-lifted-family-of-elements P f)
        ( precomp-lifted-family-of-elements P g)
        ( map-inv-distributive-Π-Σ)
        ( map-inv-distributive-Π-Σ)
        ( map-inv-distributive-Π-Σ)
        ( map-inv-distributive-Π-Σ)
        ( htpy-precomp-lifted-family-of-elements P
          ( coherence-square-cocone f g c))
        ( refl-htpy)
        ( refl-htpy)
        ( refl-htpy)
        ( refl-htpy)
        ( htpy-precomp (coherence-square-cocone f g c) (Σ X P))
        ( coherence-htpy-precomp-coherence-square-precomp-map-inv-distributive-Π-Σ
          ( P)
          ( coherence-square-cocone f g c))
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( pp-c (Σ X P)))

  dependent-pullback-property-pullback-property-pushout :
    ({l : Level} → pullback-property-pushout l f g c) →
    ({l : Level} → dependent-pullback-property-pushout l f g c)
  dependent-pullback-property-pullback-property-pushout pp-c P =
    is-pullback-htpy'
      ( ( tr-lift-family-of-elements-precomp P id
          ( coherence-square-cocone f g c)) ·r
        ( precomp-lift-family-of-elements P f (horizontal-map-cocone f g c)))
      ( refl-htpy)
      ( cone-family-dependent-pullback-property P id)
      { c' = cone-dependent-pullback-property-pushout f g c P}
      ( ( refl-htpy) ,
        ( refl-htpy) ,
        ( ( right-unit-htpy) ∙h
          ( coherence-triangle-precomp-lift-family-of-elements P id
            ( coherence-square-cocone f g c))))
      ( is-pullback-cone-family-dependent-pullback-family P pp-c id)
```
