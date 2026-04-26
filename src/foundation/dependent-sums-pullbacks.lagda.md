# Dependent sums of pullbacks

```agda
module foundation.dependent-sums-pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.standard-pullbacks
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.families-of-equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.pullbacks
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.universal-property-pullbacks
```

</details>

## Properties

### Computing the standard pullback of a dependent sum

Squares of the form

```text
  Σ (x : A) (Q (f x)) ----> Σ (y : B) Q
      |                          |
      |                          |
  pr1 |                          | pr1
      |                          |
      ∨                          ∨
      A -----------------------> B
                   f
```

are pullbacks.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (Q : B → UU l3)
  where

  standard-pullback-Σ : UU (l1 ⊔ l3)
  standard-pullback-Σ = Σ A (λ x → Q (f x))

  cone-standard-pullback-Σ : cone f pr1 standard-pullback-Σ
  pr1 cone-standard-pullback-Σ = pr1
  pr1 (pr2 cone-standard-pullback-Σ) = map-Σ-map-base f Q
  pr2 (pr2 cone-standard-pullback-Σ) = refl-htpy

  inv-gap-cone-standard-pullback-Σ :
    standard-pullback f (pr1 {B = Q}) → standard-pullback-Σ
  pr1 (inv-gap-cone-standard-pullback-Σ (x , _)) = x
  pr2 (inv-gap-cone-standard-pullback-Σ (x , (.(f x) , q) , refl)) = q

  abstract
    is-section-inv-gap-cone-standard-pullback-Σ :
      is-section
        ( gap f pr1 cone-standard-pullback-Σ)
        ( inv-gap-cone-standard-pullback-Σ)
    is-section-inv-gap-cone-standard-pullback-Σ (x , (.(f x) , q) , refl) = refl

  abstract
    is-retraction-inv-gap-cone-standard-pullback-Σ :
      is-retraction
        ( gap f pr1 cone-standard-pullback-Σ)
        ( inv-gap-cone-standard-pullback-Σ)
    is-retraction-inv-gap-cone-standard-pullback-Σ = refl-htpy

  abstract
    is-pullback-cone-standard-pullback-Σ :
      is-pullback f pr1 cone-standard-pullback-Σ
    is-pullback-cone-standard-pullback-Σ =
      is-equiv-is-invertible
        inv-gap-cone-standard-pullback-Σ
        is-section-inv-gap-cone-standard-pullback-Σ
        is-retraction-inv-gap-cone-standard-pullback-Σ

  compute-standard-pullback-Σ :
    standard-pullback-Σ ≃ standard-pullback f pr1
  pr1 compute-standard-pullback-Σ = gap f pr1 cone-standard-pullback-Σ
  pr2 compute-standard-pullback-Σ = is-pullback-cone-standard-pullback-Σ
```

### A family of maps over a base map induces a pullback square if and only if it is a family of equivalences

Given a map `f : A → B` with a family of maps over it
`g : (x : A) → P x → Q (f x)`, then the square

```text
         map-Σ f g
  Σ A P ---------> Σ B Q
    |                |
    |                |
    ∨                ∨
    A -------------> B
             f
```

is a pullback if and only if `g` is a
[fiberwise equivalence](foundation-core.families-of-equivalences.md).

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {P : A → UU l3}
  (Q : B → UU l4) (f : A → B) (g : (x : A) → P x → Q (f x))
  where

  cone-map-Σ : cone f pr1 (Σ A P)
  pr1 cone-map-Σ = pr1
  pr1 (pr2 cone-map-Σ) = map-Σ Q f g
  pr2 (pr2 cone-map-Σ) = refl-htpy

  abstract
    is-pullback-is-fiberwise-equiv :
      is-fiberwise-equiv g → is-pullback f pr1 cone-map-Σ
    is-pullback-is-fiberwise-equiv is-equiv-g =
      is-equiv-comp
        ( gap f pr1 (cone-standard-pullback-Σ f Q))
        ( tot g)
        ( is-equiv-tot-is-fiberwise-equiv is-equiv-g)
        ( is-pullback-cone-standard-pullback-Σ f Q)

  abstract
    universal-property-pullback-is-fiberwise-equiv :
      is-fiberwise-equiv g →
      universal-property-pullback f pr1 cone-map-Σ
    universal-property-pullback-is-fiberwise-equiv is-equiv-g =
      universal-property-pullback-is-pullback f pr1
        ( cone-map-Σ)
        ( is-pullback-is-fiberwise-equiv is-equiv-g)

  abstract
    is-fiberwise-equiv-is-pullback :
      is-pullback f pr1 cone-map-Σ → is-fiberwise-equiv g
    is-fiberwise-equiv-is-pullback is-pullback-cone-map-Σ =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-right-factor
          ( gap f pr1 (cone-standard-pullback-Σ f Q))
          ( tot g)
          ( is-pullback-cone-standard-pullback-Σ f Q)
          ( is-pullback-cone-map-Σ))

  abstract
    is-fiberwise-equiv-universal-property-pullback :
      ( universal-property-pullback f pr1 cone-map-Σ) →
      is-fiberwise-equiv g
    is-fiberwise-equiv-universal-property-pullback up =
      is-fiberwise-equiv-is-pullback
        ( is-pullback-universal-property-pullback f pr1 cone-map-Σ up)
```

### Pullbacks are preserved by dependent sums

#### A family of squares over a pullback square is a family of pullback squares if and only if the total square is a pullback

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (PX : X → UU l5) {PA : A → UU l6} {PB : B → UU l7} {PC : C → UU l8}
  {f : A → X} {g : B → X}
  (f' : (a : A) → PA a → PX (f a)) (g' : (b : B) → PB b → PX (g b))
  (c : cone f g C) (c' : cone-family PX f' g' c PC)
  where

  tot-cone-cone-family :
    cone (map-Σ PX f f') (map-Σ PX g g') (Σ C PC)
  pr1 tot-cone-cone-family =
    map-Σ _ (vertical-map-cone f g c) (λ x → pr1 (c' x))
  pr1 (pr2 tot-cone-cone-family) =
    map-Σ _ (horizontal-map-cone f g c) (λ x → (pr1 (pr2 (c' x))))
  pr2 (pr2 tot-cone-cone-family) =
    htpy-map-Σ PX
      ( coherence-square-cone f g c)
      ( λ z →
        ( f' (vertical-map-cone f g c z)) ∘
        ( vertical-map-cone
          ( ( tr PX (coherence-square-cone f g c z)) ∘
            ( f' (vertical-map-cone f g c z)))
          ( g' (horizontal-map-cone f g c z))
          ( c' z)))
      ( λ z →
        coherence-square-cone
          ( ( tr PX (coherence-square-cone f g c z)) ∘
            ( f' (vertical-map-cone f g c z)))
          ( g' (horizontal-map-cone f g c z))
          ( c' z))

  map-standard-pullback-tot-cone-cone-fam-right-factor :
    Σ ( standard-pullback f g)
      ( λ t →
        standard-pullback
          ( tr PX (coherence-square-standard-pullback t) ∘
            f' (vertical-map-standard-pullback t))
          ( g' (horizontal-map-standard-pullback t))) →
    Σ ( Σ A PA)
      ( λ aa' → Σ (Σ B (λ b → f (pr1 aa') ＝ g b))
        ( λ bα → Σ (PB (pr1 bα))
          ( λ b' → tr PX (pr2 bα) (f' (pr1 aa') (pr2 aa')) ＝ g' (pr1 bα) b')))
  map-standard-pullback-tot-cone-cone-fam-right-factor =
    map-interchange-Σ-Σ
      ( λ a bα a' →
        Σ ( PB (pr1 bα))
          ( λ b' → tr PX (pr2 bα) (f' a a') ＝ g' (pr1 bα) b'))

  map-standard-pullback-tot-cone-cone-fam-left-factor :
    (aa' : Σ A PA) →
    Σ (Σ B (λ b → f (pr1 aa') ＝ g b))
      ( λ bα →
        Σ ( PB (pr1 bα))
          ( λ b' → tr PX (pr2 bα) (f' (pr1 aa') (pr2 aa')) ＝ g' (pr1 bα) b')) →
    Σ ( Σ B PB)
      ( λ bb' → Σ (f (pr1 aa') ＝ g (pr1 bb'))
        ( λ α → tr PX α (f' (pr1 aa') (pr2 aa')) ＝ g' (pr1 bb') (pr2 bb')))
  map-standard-pullback-tot-cone-cone-fam-left-factor aa' =
    ( map-interchange-Σ-Σ
      ( λ b α b' → tr PX α (f' (pr1 aa') (pr2 aa')) ＝ g' b b'))

  map-standard-pullback-tot-cone-cone-family :
    Σ ( standard-pullback f g)
      ( λ t →
        standard-pullback
          ( ( tr PX (coherence-square-standard-pullback t)) ∘
            ( f' (vertical-map-standard-pullback t)))
          ( g' (horizontal-map-standard-pullback t))) →
    standard-pullback (map-Σ PX f f') (map-Σ PX g g')
  map-standard-pullback-tot-cone-cone-family =
    ( tot
      (λ aa' →
        ( tot (λ bb' → eq-pair-Σ')) ∘
        ( map-standard-pullback-tot-cone-cone-fam-left-factor aa'))) ∘
    ( map-standard-pullback-tot-cone-cone-fam-right-factor)

  is-equiv-map-standard-pullback-tot-cone-cone-family :
    is-equiv map-standard-pullback-tot-cone-cone-family
  is-equiv-map-standard-pullback-tot-cone-cone-family =
    is-equiv-comp
      ( tot
        ( λ aa' →
          ( tot (λ bb' → eq-pair-Σ')) ∘
          ( map-standard-pullback-tot-cone-cone-fam-left-factor aa')))
      ( map-standard-pullback-tot-cone-cone-fam-right-factor)
      ( is-equiv-map-interchange-Σ-Σ
        ( λ a bα a' → Σ (PB (pr1 bα))
          ( λ b' → tr PX (pr2 bα) (f' a a') ＝ g' (pr1 bα) b')))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ aa' →
          is-equiv-comp
            ( tot (λ bb' → eq-pair-Σ'))
            ( map-standard-pullback-tot-cone-cone-fam-left-factor aa')
            ( is-equiv-map-interchange-Σ-Σ _)
            ( is-equiv-tot-is-fiberwise-equiv
              ( λ bb' →
                is-equiv-eq-pair-Σ
                  ( f (pr1 aa') , f' (pr1 aa') (pr2 aa'))
                  ( g (pr1 bb') , g' (pr1 bb') (pr2 bb'))))))

  triangle-standard-pullback-tot-cone-cone-family :
    ( gap (map-Σ PX f f') (map-Σ PX g g') tot-cone-cone-family) ~
    ( ( map-standard-pullback-tot-cone-cone-family) ∘
      ( map-Σ _
        ( gap f g c)
        ( λ x → gap
          ( ( tr PX (coherence-square-cone f g c x)) ∘
            ( f' (vertical-map-cone f g c x)))
          ( g' (horizontal-map-cone f g c x))
          ( c' x))))
  triangle-standard-pullback-tot-cone-cone-family = refl-htpy

  is-pullback-family-is-pullback-tot :
    is-pullback f g c →
    is-pullback (map-Σ PX f f') (map-Σ PX g g') tot-cone-cone-family →
    (x : C) →
    is-pullback
      ( ( tr PX (coherence-square-cone f g c x)) ∘
        ( f' (vertical-map-cone f g c x)))
      ( g' (horizontal-map-cone f g c x))
      ( c' x)
  is-pullback-family-is-pullback-tot is-pb-c is-pb-tot =
    is-fiberwise-equiv-is-equiv-map-Σ _
      ( gap f g c)
      ( λ x →
        gap
          ( ( tr PX (coherence-square-cone f g c x)) ∘
            ( f' (vertical-map-cone f g c x)))
          ( g' (horizontal-map-cone f g c x))
          ( c' x))
      ( is-pb-c)
      ( is-equiv-top-map-triangle
        ( gap (map-Σ PX f f') (map-Σ PX g g') tot-cone-cone-family)
        ( map-standard-pullback-tot-cone-cone-family)
        ( map-Σ _
          ( gap f g c)
          ( λ x →
            gap
              ( ( tr PX (coherence-square-cone f g c x)) ∘
                ( f' (vertical-map-cone f g c x)))
              ( g' (horizontal-map-cone f g c x))
              ( c' x)))
        ( triangle-standard-pullback-tot-cone-cone-family)
        ( is-equiv-map-standard-pullback-tot-cone-cone-family)
        ( is-pb-tot))

  is-pullback-tot-is-pullback-family :
    is-pullback f g c →
    ( (x : C) →
      is-pullback
        ( ( tr PX (coherence-square-cone f g c x)) ∘
          ( f' (vertical-map-cone f g c x)))
        ( g' (horizontal-map-cone f g c x))
        ( c' x)) →
    is-pullback
      (map-Σ PX f f') (map-Σ PX g g') tot-cone-cone-family
  is-pullback-tot-is-pullback-family is-pb-c is-pb-c' =
    is-equiv-left-map-triangle
      ( gap (map-Σ PX f f') (map-Σ PX g g') tot-cone-cone-family)
      ( map-standard-pullback-tot-cone-cone-family)
      ( map-Σ _
        ( gap f g c)
        ( λ x → gap
          ( ( tr PX (coherence-square-cone f g c x)) ∘
            ( f' (vertical-map-cone f g c x)))
          ( g' (horizontal-map-cone f g c x))
          ( c' x)))
      ( triangle-standard-pullback-tot-cone-cone-family)
      ( is-equiv-map-Σ _ is-pb-c is-pb-c')
      ( is-equiv-map-standard-pullback-tot-cone-cone-family)
```

#### A family of squares is a family of pullback squares if and only if the total square is a pullback

As a corollary of the previous result, a dependent sum of squares over the
constant diagram is a pullback square if and only if the family is a family of
pullback squares.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {I : UU l5} {A : I → UU l1} {B : I → UU l2} {X : I → UU l3} {Y : I → UU l4}
  (f : (i : I) → B i → Y i) (g : (i : I) → X i → Y i)
  (c : (i : I) → cone (f i) (g i) (A i))
  where

  tot-cone : cone (tot f) (tot g) (Σ I A)
  pr1 tot-cone = tot (λ i → vertical-map-cone (f i) (g i) (c i))
  pr1 (pr2 tot-cone) = tot (λ i → horizontal-map-cone (f i) (g i) (c i))
  pr2 (pr2 tot-cone) = tot-htpy (λ i → coherence-square-cone (f i) (g i) (c i))

  is-pullback-tot-is-pullback-family-id-cone :
    ((i : I) → is-pullback (f i) (g i) (c i)) →
    is-pullback (tot f) (tot g) tot-cone
  is-pullback-tot-is-pullback-family-id-cone =
    is-pullback-tot-is-pullback-family Y f g
      ( id-cone I)
      ( c)
      ( is-pullback-id-cone I)

  is-pullback-family-id-cone-is-pullback-tot :
    is-pullback (tot f) (tot g) tot-cone →
    (i : I) → is-pullback (f i) (g i) (c i)
  is-pullback-family-id-cone-is-pullback-tot =
    is-pullback-family-is-pullback-tot Y f g
      ( id-cone I)
      ( c)
      ( is-pullback-id-cone I)
```

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
