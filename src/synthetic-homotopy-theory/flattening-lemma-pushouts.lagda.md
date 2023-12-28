# The flattening lemma for pushouts

```agda
module synthetic-homotopy-theory.flattening-lemma-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-cubes-of-maps
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.spans
open import foundation.transport-along-identifications
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.26-descent
open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-span-diagrams
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.families-of-types-pushouts
open import synthetic-homotopy-theory.operations-cocones-under-span-diagrams
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The **flattening lemma** for [pushouts](synthetic-homotopy-theory.pushouts.md)
states that pushouts commute with
[dependent pair types](foundation.dependent-pair-types.md). More precisely,
given a pushout square

```text
      g
  S -----> B
  |        |
 f|        |j
  V      ⌜ V
  A -----> X
      i
```

with homotopy `H : i ∘ f ~ j ∘ g`, and for any type family `P` over `X`, the
commuting square

```text
  Σ (s : S), P(if(s)) ---> Σ (s : S), P(jg(s)) ---> Σ (b : B), P(j(b))
           |                                                 |
           |                                                 |
           V                                               ⌜ V
  Σ (a : A), P(i(a)) -----------------------------> Σ (x : X), P(x)
```

is again a pushout square.

## Definitions

### The statement of the flattening lemma for pushouts

```agda
module _
  { l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3)
  { X : UU l4} (c : cocone-span s X) (P : X → UU l5)
  where

  spanning-type-span-flattening-pushout : UU (l3 ⊔ l5)
  spanning-type-span-flattening-pushout =
    Σ ( spanning-type-span s)
      ( P ∘ horizontal-map-cocone-span s c ∘ left-map-span s)

  domain-span-flattening-pushout : UU (l1 ⊔ l5)
  domain-span-flattening-pushout =
    Σ ( domain-span s) (P ∘ horizontal-map-cocone-span s c)

  codomain-span-flattening-pushout : UU (l2 ⊔ l5)
  codomain-span-flattening-pushout =
    Σ ( codomain-span s) (P ∘ vertical-map-cocone-span s c)

  left-map-span-flattening-pushout :
    spanning-type-span-flattening-pushout → domain-span-flattening-pushout
  left-map-span-flattening-pushout =
    map-Σ-map-base (left-map-span s) (P ∘ horizontal-map-cocone-span s c)

  right-map-span-flattening-pushout :
    spanning-type-span-flattening-pushout → codomain-span-flattening-pushout
  right-map-span-flattening-pushout =
    map-Σ
      ( P ∘ vertical-map-cocone-span s c)
      ( right-map-span s)
      ( λ x → tr P (coherence-square-cocone-span s c x))

  span-flattening-pushout : span (l1 ⊔ l5) (l2 ⊔ l5) (l3 ⊔ l5)
  span-flattening-pushout =
    make-span
      ( left-map-span-flattening-pushout)
      ( right-map-span-flattening-pushout)

  horizontal-map-cocone-flattening-pushout :
    domain-span-flattening-pushout → Σ X P
  horizontal-map-cocone-flattening-pushout =
    map-Σ-map-base (horizontal-map-cocone-span s c) P

  vertical-map-cocone-flattening-pushout :
    codomain-span-flattening-pushout → Σ X P
  vertical-map-cocone-flattening-pushout =
    map-Σ-map-base (vertical-map-cocone-span s c) P

  coherence-square-cocone-flattening-pushout :
    coherence-square-maps
      ( right-map-span-flattening-pushout)
      ( left-map-span-flattening-pushout)
      ( vertical-map-cocone-flattening-pushout)
      ( horizontal-map-cocone-flattening-pushout)
  coherence-square-cocone-flattening-pushout =
    coherence-square-maps-map-Σ-map-base P
      ( right-map-span s)
      ( left-map-span s)
      ( vertical-map-cocone-span s c)
      ( horizontal-map-cocone-span s c)
      ( coherence-square-cocone-span s c)

  cocone-flattening-pushout :
    cocone-span span-flattening-pushout (Σ X P)
  pr1 cocone-flattening-pushout =
    horizontal-map-cocone-flattening-pushout
  pr1 (pr2 cocone-flattening-pushout) =
    vertical-map-cocone-flattening-pushout
  pr2 (pr2 cocone-flattening-pushout) =
    coherence-square-cocone-flattening-pushout

  statement-flattening-lemma-pushout : UUω
  statement-flattening-lemma-pushout =
    dependent-universal-property-pushout s c →
    universal-property-pushout span-flattening-pushout cocone-flattening-pushout
```

### The statement of the flattening lemma for pushouts, phrased using descent data

The above statement of the flattening lemma works with a provided type family
over the pushout. We can instead accept a definition of this family via descent
data for the pushout.

```agda
module _
  { l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3)
  { X : UU l4} (c : cocone-span s X)
  ( P : structure-type-family-pushout l5 s)
  ( Q : X → UU l5)
  ( e :
    equiv-structure-type-family-pushout s P
      ( structure-type-family-pushout-type-family s c Q))
  where

  spanning-type-span-flattening-descent-data-pushout : UU (l3 ⊔ l5)
  spanning-type-span-flattening-descent-data-pushout =
    Σ ( spanning-type-span s)
      ( left-type-family-structure-type-family-pushout s P ∘ left-map-span s)

  domain-span-flattening-descent-data-pushout : UU (l1 ⊔ l5)
  domain-span-flattening-descent-data-pushout =
    Σ (domain-span s) (left-type-family-structure-type-family-pushout s P)

  codomain-span-flattening-descent-data-pushout : UU (l2 ⊔ l5)
  codomain-span-flattening-descent-data-pushout =
    Σ (codomain-span s) (right-type-family-structure-type-family-pushout s P)

  left-map-span-flattening-descent-data-pushout :
    spanning-type-span-flattening-descent-data-pushout →
    domain-span-flattening-descent-data-pushout
  left-map-span-flattening-descent-data-pushout =
    map-Σ-map-base
      ( left-map-span s)
      ( left-type-family-structure-type-family-pushout s P)

  right-map-span-flattening-descent-data-pushout :
    spanning-type-span-flattening-descent-data-pushout →
    codomain-span-flattening-descent-data-pushout
  right-map-span-flattening-descent-data-pushout =
    map-Σ
      ( right-type-family-structure-type-family-pushout s P)
      ( right-map-span s)
      ( map-matching-equiv-structure-type-family-pushout s P)

  span-flattening-descent-data-pushout : span (l1 ⊔ l5) (l2 ⊔ l5) (l3 ⊔ l5)
  span-flattening-descent-data-pushout =
    make-span
      left-map-span-flattening-descent-data-pushout
      right-map-span-flattening-descent-data-pushout

  horizontal-map-cocone-flattening-descent-data-pushout :
    domain-span-flattening-descent-data-pushout → Σ X Q
  horizontal-map-cocone-flattening-descent-data-pushout =
    map-Σ Q
      ( horizontal-map-cocone-span s c)
      ( map-left-equiv-equiv-structure-type-family-pushout s P
        ( structure-type-family-pushout-type-family s c Q)
        ( e))

  vertical-map-cocone-flattening-descent-data-pushout :
    codomain-span-flattening-descent-data-pushout → Σ X Q
  vertical-map-cocone-flattening-descent-data-pushout =
    map-Σ Q
      ( vertical-map-cocone-span s c)
      ( map-right-equiv-equiv-structure-type-family-pushout s P
        ( structure-type-family-pushout-type-family s c Q)
        ( e))

  coherence-square-cocone-flattening-descent-data-pushout :
    coherence-square-maps
      ( right-map-span-flattening-descent-data-pushout)
      ( left-map-span-flattening-descent-data-pushout)
      ( vertical-map-cocone-flattening-descent-data-pushout)
      ( horizontal-map-cocone-flattening-descent-data-pushout)
  coherence-square-cocone-flattening-descent-data-pushout =
    htpy-map-Σ Q
      ( coherence-square-cocone-span s c)
      ( λ x →
        map-left-equiv-equiv-structure-type-family-pushout s P
          ( structure-type-family-pushout-type-family s c Q)
          ( e)
          ( left-map-span s x))
      ( λ x →
        inv-htpy
          ( coherence-equiv-structure-type-family-pushout s P
            ( structure-type-family-pushout-type-family s c Q)
            ( e)
            ( x)))

  cocone-flattening-descent-data-pushout :
    cocone-span (span-flattening-descent-data-pushout) (Σ X Q)
  pr1 cocone-flattening-descent-data-pushout =
    horizontal-map-cocone-flattening-descent-data-pushout
  pr1 (pr2 cocone-flattening-descent-data-pushout) =
    vertical-map-cocone-flattening-descent-data-pushout
  pr2 (pr2 cocone-flattening-descent-data-pushout) =
    coherence-square-cocone-flattening-descent-data-pushout

  statement-flattening-lemma-descent-data-pushout : UUω
  statement-flattening-lemma-descent-data-pushout =
    dependent-universal-property-pushout s c →
    universal-property-pushout
      ( span-flattening-descent-data-pushout)
      ( cocone-flattening-descent-data-pushout)
```

## Properties

### Proof of the flattening lemma for pushouts

The proof uses the theorem that maps from `Σ`-types are equivalent to dependent
maps over the index type, for which we can invoke the dependent universal
property of the indexing pushout.

```agda
module _
  { l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3)
  { X : UU l4} (c : cocone-span s X) (P : X → UU l5)
  where

  cocone-span-map-flattening-pushout :
    {l : Level} (Y : UU l) →
    (Σ X P → Y) → cocone-span (span-flattening-pushout s c P) Y
  cocone-span-map-flattening-pushout Y =
    cocone-span-map
      ( span-flattening-pushout s c P)
      ( cocone-flattening-pushout s c P)

  comparison-dependent-cocone-ind-Σ-cocone :
    { l : Level} (Y : UU l) →
    Σ ( (a : domain-span s) → P (horizontal-map-cocone-span s c a) → Y)
      ( λ k →
        Σ ( (b : codomain-span s) → P (vertical-map-cocone-span s c b) → Y)
          ( λ l →
            ( x : spanning-type-span s)
            ( t : P (horizontal-map-cocone-span s c (left-map-span s x))) →
            ( k (left-map-span s x) t) ＝
            ( l ( right-map-span s x)
                ( tr P (coherence-square-cocone-span s c x) t)))) ≃
    dependent-cocone-span s c (λ x → P x → Y)
  comparison-dependent-cocone-ind-Σ-cocone Y =
    equiv-tot
      ( λ k →
        equiv-tot
          ( λ l →
            equiv-Π-equiv-family
              ( equiv-htpy-dependent-function-dependent-identification-function-type
                ( Y)
                ( coherence-square-cocone-span s c)
                ( k ∘ left-map-span s)
                ( l ∘ right-map-span s))))

  triangle-comparison-dependent-cocone-ind-Σ-cocone :
    { l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( dependent-cocone-span-map s c (λ x → P x → Y))
      ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
      ( map-equiv equiv-ev-pair³ ∘ cocone-span-map-flattening-pushout Y ∘ ind-Σ)
  triangle-comparison-dependent-cocone-ind-Σ-cocone Y h =
    eq-pair-Σ
      ( refl)
      ( eq-pair-Σ
        ( refl)
        ( eq-htpy
          ( inv-htpy
            ( compute-equiv-htpy-dependent-function-dependent-identification-function-type
              ( Y)
              ( coherence-square-cocone-span s c)
              ( h)))))

  flattening-lemma-pushout :
    statement-flattening-lemma-pushout s c P
  flattening-lemma-pushout dup-pushout Y =
    is-equiv-left-factor
      ( cocone-span-map-flattening-pushout Y)
      ( ind-Σ)
      ( is-equiv-right-factor
        ( map-equiv equiv-ev-pair³)
        ( cocone-span-map-flattening-pushout Y ∘ ind-Σ)
        ( is-equiv-map-equiv equiv-ev-pair³)
        ( is-equiv-top-map-triangle
          ( dependent-cocone-span-map s c (λ x → P x → Y))
          ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
          ( map-equiv equiv-ev-pair³ ∘ cocone-span-map-flattening-pushout Y ∘ ind-Σ)
          ( triangle-comparison-dependent-cocone-ind-Σ-cocone Y)
          ( is-equiv-map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
          ( dup-pushout (λ x → P x → Y))))
      ( is-equiv-ind-Σ)
```

### Proof of the descent data statement of the flattening lemma

The proof is carried out by constructing a commuting cube, which has
equivalences for vertical maps, the `cocone-flattening-pushout` square for the
bottom, and the `cocone-flattening-descent-data-pushout` square for the top.

The bottom is a pushout by the above flattening lemma, which implies that the
top is also a pushout.

The other parts of the cube are defined naturally, and come from the following
map of spans:

```text
  Σ (a : A) (PA a) <------- Σ (s : S) (PA (f s)) -----> Σ (b : B) (PB b)
         |                           |                         |
         |                           |                         |
         v                           v                         v
Σ (a : A) (P (i a)) <---- Σ (s : S) (P (i (f s))) ---> Σ (b : B) (P (j b))
```

where the vertical maps are equivalences given fiberwise by the equivalence of
descent data.

```agda
module _
  { l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3)
  { X : UU l4} (c : cocone-span s X)
  ( P : structure-type-family-pushout l5 s)
  ( Q : X → UU l5)
  ( e :
    equiv-structure-type-family-pushout s P
      ( structure-type-family-pushout-type-family s c Q))
  where

  coherence-cube-flattening-lemma-descent-data-pushout :
    coherence-cube-maps
      ( left-map-span-flattening-pushout s c Q)
      ( right-map-span-flattening-pushout s c Q)
      ( horizontal-map-cocone-flattening-pushout s c Q)
      ( vertical-map-cocone-flattening-pushout s c Q)
      ( left-map-span-flattening-descent-data-pushout s c P Q e)
      ( right-map-span-flattening-descent-data-pushout s c P Q e)
      ( horizontal-map-cocone-flattening-descent-data-pushout s c P Q e)
      ( vertical-map-cocone-flattening-descent-data-pushout s c P Q e)
      ( tot (λ x → map-equiv (pr1 e (left-map-span s x))))
      ( tot (λ a → map-equiv (pr1 e a)))
      ( tot (λ b → map-equiv (pr1 (pr2 e) b)))
      ( id)
      ( coherence-square-cocone-flattening-descent-data-pushout s c P Q e)
      ( refl-htpy)
      ( htpy-map-Σ
        ( Q ∘ vertical-map-cocone-span s c)
        ( refl-htpy)
        ( λ x →
          ( tr Q (coherence-square-cocone-span s c x)) ∘
          ( map-equiv (pr1 e (left-map-span s x))))
        ( λ x → inv-htpy (pr2 (pr2 e) x)))
      ( refl-htpy)
      ( refl-htpy)
      ( coherence-square-cocone-flattening-pushout s c Q)
  coherence-cube-flattening-lemma-descent-data-pushout (s , t) =
    ( ap-id
      ( coherence-square-cocone-flattening-descent-data-pushout s c P Q e
        ( s , t))) ∙
    ( triangle-eq-pair-Σ Q
      ( coherence-square-cocone-span s c s)
      ( inv (pr2 (pr2 e) s t))) ∙
    ( ap
      ( eq-pair-Σ (coherence-square-cocone-span s c s) refl ∙_)
      ( inv
        ( ( right-unit) ∙
          ( compute-ap-map-Σ-map-base-eq-pair-Σ
            ( vertical-map-cocone-span s c)
            ( Q)
            ( refl)
            ( inv (pr2 (pr2 e) s t))))))

  flattening-lemma-descent-data-pushout :
    statement-flattening-lemma-descent-data-pushout s c P Q e
  flattening-lemma-descent-data-pushout dup-pushout =
    universal-property-pushout-top-universal-property-pushout-bottom-cube-is-equiv
      ( left-map-span-flattening-pushout s c Q)
      ( right-map-span-flattening-pushout s c Q)
      ( horizontal-map-cocone-flattening-pushout s c Q)
      ( vertical-map-cocone-flattening-pushout s c Q)
      ( left-map-span-flattening-descent-data-pushout s c P Q e)
      ( right-map-span-flattening-descent-data-pushout s c P Q e)
      ( horizontal-map-cocone-flattening-descent-data-pushout s c P Q e)
      ( vertical-map-cocone-flattening-descent-data-pushout s c P Q e)
      ( tot (λ x → map-equiv (pr1 e (f x))))
      ( tot (λ a → map-equiv (pr1 e a)))
      ( tot (λ b → map-equiv (pr1 (pr2 e) b)))
      ( id)
      ( coherence-square-cocone-flattening-descent-data-pushout s c P Q e)
      ( refl-htpy)
      ( htpy-map-Σ
        ( Q ∘ vertical-map-cocone-span s c)
        ( refl-htpy)
        ( λ x →
          tr Q (coherence-square-cocone-span s c x) ∘ (map-equiv (pr1 e (f x))))
        ( λ x → inv-htpy (pr2 (pr2 e) x)))
      ( refl-htpy)
      ( refl-htpy)
      ( coherence-square-cocone-flattening-pushout s c Q)
      ( coherence-cube-flattening-lemma-descent-data-pushout)
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ x → is-equiv-map-equiv (pr1 e (f x))))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ a → is-equiv-map-equiv (pr1 e a)))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ b → is-equiv-map-equiv (pr1 (pr2 e) b)))
      ( is-equiv-id)
      ( flattening-lemma-pushout s c Q dup-pushout)
```
