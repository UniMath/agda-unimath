# The flattening lemma for sequential colimits

```agda
module synthetic-homotopy-theory.flattening-lemma-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-double-arrows
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.equivalences-coforks
open import synthetic-homotopy-theory.flattening-lemma-coequalizers
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-coequalizers
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

The
{{#concept "flattening lemma" Disambiguation="sequential colimits" Agda=flattening-lemma-sequential-colimit}}
for
[sequential colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md)
states that sequential colimits commute with
[dependent pair types](foundation.dependent-pair-types.md). Specifically, given
a [cocone](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md)

```text
  A₀ ---> A₁ ---> A₂ ---> ⋯ ---> X
```

with the universal property of sequential colimits, and a family `P : X → 𝓤`, we
obtain a cocone

```text
  Σ (a : A₀) P(i₀ a) ---> Σ (a : A₁) P(i₁ a) ---> ⋯ ---> Σ (x : X) P(x) ,
```

which is again a sequential colimit.

The result may be read as
`colimₙ (Σ (a : Aₙ) P(iₙ a)) ≃ Σ (a : colimₙ Aₙ) P(a)`.

## Definitions

### The sequential diagram for the flattening lemma

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  ( P : X → UU l3)
  where

  sequential-diagram-flattening-lemma : sequential-diagram (l1 ⊔ l3)
  pr1 sequential-diagram-flattening-lemma n =
    Σ ( family-sequential-diagram A n)
      ( P ∘ map-cocone-sequential-diagram c n)
  pr2 sequential-diagram-flattening-lemma n =
    map-Σ
      ( P ∘ map-cocone-sequential-diagram c (succ-ℕ n))
      ( map-sequential-diagram A n)
      ( λ a → tr P (coherence-cocone-sequential-diagram c n a))

  cocone-sequential-diagram-flattening-lemma :
    cocone-sequential-diagram sequential-diagram-flattening-lemma (Σ X P)
  pr1 cocone-sequential-diagram-flattening-lemma n =
    map-Σ-map-base (map-cocone-sequential-diagram c n) P
  pr2 cocone-sequential-diagram-flattening-lemma n =
    coherence-triangle-maps-map-Σ-map-base P
      ( map-cocone-sequential-diagram c n)
      ( map-cocone-sequential-diagram c (succ-ℕ n))
      ( map-sequential-diagram A n)
      ( coherence-cocone-sequential-diagram c n)
```

### Statement of the flattening lemma

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  ( P : X → UU l3)
  where

  statement-flattening-lemma-sequential-colimit : UUω
  statement-flattening-lemma-sequential-colimit =
    dependent-universal-property-sequential-colimit c →
    universal-property-sequential-colimit
      ( cocone-sequential-diagram-flattening-lemma c P)
```

## Properties

### Proof of the flattening lemma

Similarly to the proof of the
[flattening lemma for coequalizers](synthetic-homotopy-theory.flattening-lemma-coequalizers.md),
this proof uses the fact that sequential colimits correspond to certain
coequalizers, which is recorded in
[`synthetic-homotopy-theory.dependent-universal-property-sequential-colimits`](synthetic-homotopy-theory.dependent-universal-property-sequential-colimits.md),
so it suffices to invoke the flattening lemma for coequalizers.

**Proof:** The diagram we construct is

```text
                               ------->
  Σ (n : ℕ) Σ (a : Aₙ) P(iₙ a) -------> Σ (n : ℕ) Σ (a : Aₙ) P(iₙ a) ----> Σ (x : X) P(x)
             |                                     |                            |
 inv-assoc-Σ | ≃                       inv-assoc-Σ | ≃                       id | ≃
             |                                     |                            |
             V                --------->           V                            V
   Σ ((n, a) : Σ ℕ A) P(iₙ a) ---------> Σ ((n, a) : Σ ℕ A) P(iₙ a) -----> Σ (x : X) P(x) ,
```

where the top is the cofork corresponding to the cocone for the flattening
lemma, and the bottom is the cofork obtained by flattening the cofork
corresponding to the given base cocone.

By assumption, the original cocone is a sequential colimit, which implies that
its corresponding cofork is a coequalizer. The flattening lemma for coequalizers
implies that the bottom cofork is a coequalizer, which in turn implies that the
top cofork is a coequalizer, hence the flattening of the original cocone is a
sequential colimit.

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  ( P : X → UU l3)
  where

  equiv-double-arrow-flattening-lemma-sequential-colimit :
    equiv-double-arrow
      ( double-arrow-sequential-diagram
        ( sequential-diagram-flattening-lemma c P))
      ( double-arrow-flattening-lemma-coequalizer
        ( double-arrow-sequential-diagram A)
        ( P)
        ( cofork-cocone-sequential-diagram A c))
  pr1 equiv-double-arrow-flattening-lemma-sequential-colimit =
    inv-associative-Σ
      ( ℕ)
      ( family-sequential-diagram A)
      ( P ∘ ind-Σ (map-cocone-sequential-diagram c))
  pr1 (pr2 equiv-double-arrow-flattening-lemma-sequential-colimit) =
    inv-associative-Σ
      ( ℕ)
      ( family-sequential-diagram A)
      ( P ∘ ind-Σ (map-cocone-sequential-diagram c))
  pr1 (pr2 (pr2 equiv-double-arrow-flattening-lemma-sequential-colimit)) =
    refl-htpy
  pr2 (pr2 (pr2 equiv-double-arrow-flattening-lemma-sequential-colimit)) =
    refl-htpy

  equiv-cofork-flattening-lemma-sequential-colimit :
    equiv-cofork
      ( cofork-cocone-sequential-diagram _
        ( cocone-sequential-diagram-flattening-lemma c P))
      ( cofork-flattening-lemma-coequalizer
        ( double-arrow-sequential-diagram A)
        ( P)
        ( cofork-cocone-sequential-diagram A c))
      ( equiv-double-arrow-flattening-lemma-sequential-colimit)
  pr1 equiv-cofork-flattening-lemma-sequential-colimit = id-equiv
  pr1 (pr2 equiv-cofork-flattening-lemma-sequential-colimit) =
    refl-htpy
  pr2 (pr2 equiv-cofork-flattening-lemma-sequential-colimit) =
    inv-htpy
      ( ( right-unit-htpy) ∙h
        ( right-unit-htpy) ∙h
        ( left-unit-law-left-whisker-comp
          ( coh-cofork _
            ( cofork-cocone-sequential-diagram _
              ( cocone-sequential-diagram-flattening-lemma c P)))))

  abstract
    flattening-lemma-sequential-colimit :
      statement-flattening-lemma-sequential-colimit c P
    flattening-lemma-sequential-colimit dup-c =
      universal-property-sequential-colimit-universal-property-coequalizer
        ( cocone-sequential-diagram-flattening-lemma c P)
        ( universal-property-coequalizer-top-universal-property-coequalizer-bottom-hom-arrow-is-equiv
          ( _)
          ( cofork-cocone-sequential-diagram _
            ( cocone-sequential-diagram-flattening-lemma c P))
          ( _)
          ( cofork-flattening-lemma-coequalizer _
            ( P)
            ( cofork-cocone-sequential-diagram A c))
          ( equiv-double-arrow-flattening-lemma-sequential-colimit)
          ( equiv-cofork-flattening-lemma-sequential-colimit)
          ( flattening-lemma-coequalizer _
            ( P)
            ( cofork-cocone-sequential-diagram A c)
            ( dependent-universal-property-coequalizer-dependent-universal-property-sequential-colimit
              ( c)
              ( dup-c))))
```
