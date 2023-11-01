# Dependent cocones under spans

```agda
module synthetic-homotopy-theory.dependent-cocones-under-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.spans
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Idea

Consider a span `𝒮 := (A <-- S --> B)` and a
[cocone structure](synthetic-homotopy-theory.cocones-under-spans.md) `c` of `𝒮`
into a type `X`. Furthermore, consider a type family `P` over `X`. In this case
we may consider _dependent_ cocone structures on `P` over `c`.

A **dependent cocone** `d` over `(i , j , H)` on `P` consists of two dependent
functions

```text
  i' : (a : A) → P (i a)
  j' : (b : B) → P (j b)
```

and a family of
[dependent identifications](foundation.dependent-identifications.md)

```text
  (s : S) → dependent-identification P (H s) (i' (f s)) (j' (g s)).
```

## Definitions

### Dependent cocones

```agda
module _
  { l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3)
  {X : UU l4} (c : cocone-span s X) (P : X → UU l5)
  where

  dependent-cocone-span : UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
  dependent-cocone-span =
    Σ ( (a : domain-span s) → P (horizontal-map-cocone-span s c a))
      ( λ hA →
        Σ ( (b : codomain-span s) → P (vertical-map-cocone-span s c b))
          ( λ hB →
            (x : spanning-type-span s) →
            dependent-identification P
              ( coherence-square-cocone-span s c x)
              ( hA (left-map-span s x))
              ( hB (right-map-span s x))))

  module _
    (d : dependent-cocone-span)
    where

    horizontal-map-dependent-cocone-span :
      (a : domain-span s) → P (horizontal-map-cocone-span s c a)
    horizontal-map-dependent-cocone-span = pr1 d

    vertical-map-dependent-cocone-span :
      (b : codomain-span s) → P (vertical-map-cocone-span s c b)
    vertical-map-dependent-cocone-span = pr1 (pr2 d)

    coherence-square-dependent-cocone-span :
      (x : spanning-type-span s) →
      dependent-identification P
        ( coherence-square-cocone-span s c x)
        ( horizontal-map-dependent-cocone-span (left-map-span s x))
        ( vertical-map-dependent-cocone-span (right-map-span s x))
    coherence-square-dependent-cocone-span = pr2 (pr2 d)
```

### Postcomposing dependent cocones with maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3)
  {X : UU l4} (c : cocone-span s X) (P : X → UU l5)
  where

  dependent-cocone-span-map :
    ((x : X) → P x) → dependent-cocone-span s c P
  pr1 (dependent-cocone-span-map h) a =
    h (horizontal-map-cocone-span s c a)
  pr1 (pr2 (dependent-cocone-span-map h)) b =
    h (vertical-map-cocone-span s c b)
  pr2 (pr2 (dependent-cocone-span-map h)) x =
    apd h (coherence-square-cocone-span s c x)
```

## Properties

### Characterization of identifications of dependent cocones

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3)
  {X : UU l4} (c : cocone-span s X) (P : X → UU l5)
  (d : dependent-cocone-span s c P)
  where

  coherence-htpy-dependent-cocone-span :
    ( d' : dependent-cocone-span s c P)
    ( K :
      horizontal-map-dependent-cocone-span s c P d ~
      horizontal-map-dependent-cocone-span s c P d')
    ( L :
      vertical-map-dependent-cocone-span s c P d ~
      vertical-map-dependent-cocone-span s c P d') →
    UU (l3 ⊔ l5)
  coherence-htpy-dependent-cocone-span d' K L =
    (x : spanning-type-span s) →
    ( ( coherence-square-dependent-cocone-span s c P d x) ∙
      ( L (right-map-span s x))) ＝
    ( ( ap
        ( tr P (coherence-square-cocone-span s c x))
        ( K (left-map-span s x))) ∙
      ( coherence-square-dependent-cocone-span s c P d' x))

  htpy-dependent-cocone-span :
    (d' : dependent-cocone-span s c P) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
  htpy-dependent-cocone-span d' =
    Σ ( horizontal-map-dependent-cocone-span s c P d ~
        horizontal-map-dependent-cocone-span s c P d')
      ( λ K →
        Σ ( vertical-map-dependent-cocone-span s c P d ~
            vertical-map-dependent-cocone-span s c P d')
          ( coherence-htpy-dependent-cocone-span d' K))

  refl-htpy-dependent-cocone-span :
    htpy-dependent-cocone-span d
  pr1 refl-htpy-dependent-cocone-span = refl-htpy
  pr1 (pr2 refl-htpy-dependent-cocone-span) = refl-htpy
  pr2 (pr2 refl-htpy-dependent-cocone-span) = right-unit-htpy

  htpy-eq-dependent-cocone-span :
    (d' : dependent-cocone-span s c P) → d ＝ d' → htpy-dependent-cocone-span d'
  htpy-eq-dependent-cocone-span .d refl = refl-htpy-dependent-cocone-span

  module _
    (d' : dependent-cocone-span s c P)
    (p : d ＝ d')
    where

    horizontal-htpy-eq-dependent-cocone-span :
      horizontal-map-dependent-cocone-span s c P d ~
      horizontal-map-dependent-cocone-span s c P d'
    horizontal-htpy-eq-dependent-cocone-span =
      pr1 (htpy-eq-dependent-cocone-span d' p)

    vertical-htpy-eq-dependent-cocone-span :
      vertical-map-dependent-cocone-span s c P d ~
      vertical-map-dependent-cocone-span s c P d'
    vertical-htpy-eq-dependent-cocone-span =
      pr1 (pr2 (htpy-eq-dependent-cocone-span d' p))

    coherence-square-htpy-eq-dependent-cocone-span :
      coherence-htpy-dependent-cocone-span d'
        ( horizontal-htpy-eq-dependent-cocone-span)
        ( vertical-htpy-eq-dependent-cocone-span)
    coherence-square-htpy-eq-dependent-cocone-span =
      pr2 (pr2 (htpy-eq-dependent-cocone-span d' p))

  abstract
    is-torsorial-htpy-dependent-cocone-span :
      is-torsorial htpy-dependent-cocone-span
    is-torsorial-htpy-dependent-cocone-span =
      is-torsorial-Eq-structure
        ( λ α βγ K →
            Σ ( vertical-map-dependent-cocone-span s c P d ~ pr1 βγ)
              ( coherence-htpy-dependent-cocone-span (α , βγ) K))
        ( is-torsorial-htpy (horizontal-map-dependent-cocone-span s c P d))
        ( horizontal-map-dependent-cocone-span s c P d , refl-htpy)
        ( is-torsorial-Eq-structure
          ( λ β γ →
            coherence-htpy-dependent-cocone-span
              ( horizontal-map-dependent-cocone-span s c P d , β , γ)
              ( refl-htpy))
          ( is-torsorial-htpy (vertical-map-dependent-cocone-span s c P d))
          ( vertical-map-dependent-cocone-span s c P d , refl-htpy)
          ( is-contr-equiv
            ( Σ ( (x : spanning-type-span s) →
                  dependent-identification P
                    ( coherence-square-cocone-span s c x)
                    ( horizontal-map-dependent-cocone-span s c P d
                      ( left-map-span s x))
                    ( vertical-map-dependent-cocone-span s c P d
                      ( right-map-span s x)))
                ( λ γ → coherence-square-dependent-cocone-span s c P d ~ γ))
            ( equiv-tot (equiv-concat-htpy inv-htpy-right-unit-htpy))
            ( is-torsorial-htpy
              ( coherence-square-dependent-cocone-span s c P d))))

  abstract
    is-equiv-htpy-eq-dependent-cocone-span :
      (d' : dependent-cocone-span s c P) →
      is-equiv (htpy-eq-dependent-cocone-span d')
    is-equiv-htpy-eq-dependent-cocone-span =
      fundamental-theorem-id
        ( is-torsorial-htpy-dependent-cocone-span)
        ( htpy-eq-dependent-cocone-span)

    eq-htpy-dependent-cocone-span :
      (d' : dependent-cocone-span s c P) →
      htpy-dependent-cocone-span d' → d ＝ d'
    eq-htpy-dependent-cocone-span d' =
      map-inv-is-equiv (is-equiv-htpy-eq-dependent-cocone-span d')

    is-section-eq-htpy-dependent-cocone-span :
      (d' : dependent-cocone-span s c P) →
      htpy-eq-dependent-cocone-span d' ∘ eq-htpy-dependent-cocone-span d' ~ id
    is-section-eq-htpy-dependent-cocone-span d' =
      is-section-map-inv-is-equiv (is-equiv-htpy-eq-dependent-cocone-span d')

    is-retraction-eq-htpy-dependent-cocone-span :
      (d' : dependent-cocone-span s c P) →
      eq-htpy-dependent-cocone-span d' ∘ htpy-eq-dependent-cocone-span d' ~ id
    is-retraction-eq-htpy-dependent-cocone-span d' =
      is-retraction-map-inv-is-equiv (is-equiv-htpy-eq-dependent-cocone-span d')
```
