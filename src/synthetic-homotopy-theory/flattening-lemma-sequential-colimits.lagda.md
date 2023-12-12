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
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.flattening-lemma-coequalizers
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-coequalizers
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

The {{#concept "flattening lemma" Disambiguation="sequential colimits"}} for
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
      ( P ∘ map-cocone-sequential-diagram A c n)
  pr2 sequential-diagram-flattening-lemma n =
    map-Σ
      ( P ∘ map-cocone-sequential-diagram A c (succ-ℕ n))
      ( map-sequential-diagram A n)
      ( λ a → tr P (coherence-triangle-cocone-sequential-diagram A c n a))

  cocone-sequential-diagram-flattening-lemma :
    cocone-sequential-diagram sequential-diagram-flattening-lemma (Σ X P)
  pr1 cocone-sequential-diagram-flattening-lemma n =
    map-Σ-map-base (map-cocone-sequential-diagram A c n) P
  pr2 cocone-sequential-diagram-flattening-lemma n =
    coherence-triangle-maps-map-Σ-map-base P
      ( map-cocone-sequential-diagram A c n)
      ( map-cocone-sequential-diagram A c (succ-ℕ n))
      ( map-sequential-diagram A n)
      ( coherence-triangle-cocone-sequential-diagram A c n)
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
    dependent-universal-property-sequential-colimit A c →
    universal-property-sequential-colimit
      ( sequential-diagram-flattening-lemma c P)
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
                             --------->
  Σ ((n, a) : Σ ℕ A) P(iₙ a) ---------> Σ ((n, a) : Σ ℕ A) P(iₙ a) -----> Σ (x : X) P(x)
            |                                     |                            |
    assoc-Σ | ≃                           assoc-Σ | ≃                       id | ≃
            |                                     |                            |
            V               ---------->           V                            V
  Σ (n : ℕ, a : Aₙ) P(iₙ a) ----------> Σ (n : ℕ, a : Aₙ) P(iₙ a) ------> Σ (x : X) P(x) ,
```

where the top is the cofork obtained by coforkification of the cocone for the
flattening lemma, and the bottom is the cofork obtained by flattening the
coforkification of the original cocone.

By assumption, the original cocone is a sequential colimit, which implies that
its coforkification is a coequalizer. The flattening lemma for coequalizers
implies that the bottom cofork is a coequalizer, which in turn implies that the
top cofork is a coequalizer, hence the flattening of the original cocone is a
sequential colimit.

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  ( P : X → UU l3)
  where

  abstract
    flattening-lemma-sequential-colimit :
      statement-flattening-lemma-sequential-colimit c P
    flattening-lemma-sequential-colimit dup-c =
      universal-property-sequential-colimit-universal-property-coequalizer
        ( sequential-diagram-flattening-lemma c P)
        ( cocone-sequential-diagram-flattening-lemma c P)
        ( universal-property-coequalizer-top-universal-property-coequalizer-bottom-hom-arrow-is-equiv
          ( map-inv-associative-Σ ℕ
            ( family-sequential-diagram A)
            ( P ∘ ind-Σ (map-cocone-sequential-diagram A c)))
          ( map-inv-associative-Σ ℕ
            ( family-sequential-diagram A)
            ( P ∘ ind-Σ (map-cocone-sequential-diagram A c)))
          ( id)
          ( ( bottom-map-cofork-cocone-sequential-diagram
              ( sequential-diagram-flattening-lemma c P)) ,
            ( bottom-map-cofork-flattening-lemma-coequalizer _ _
              ( P)
              ( cofork-cocone-sequential-diagram A c)) ,
            ( refl-htpy))
          ( ( top-map-cofork-cocone-sequential-diagram
              ( sequential-diagram-flattening-lemma c P)) ,
            ( top-map-cofork-flattening-lemma-coequalizer _ _
              ( P)
              ( cofork-cocone-sequential-diagram A c)) ,
            ( refl-htpy))
          ( ( map-cofork _ _
              ( cofork-cocone-sequential-diagram
                ( sequential-diagram-flattening-lemma c P)
                ( cocone-sequential-diagram-flattening-lemma c P))) ,
            ( map-cofork _ _
              ( cofork-flattening-lemma-coequalizer _ _ P
                ( cofork-cocone-sequential-diagram A c))) ,
            ( refl-htpy))
          ( ind-Σ
            ( coherence-triangle-cocone-sequential-diagram
              ( sequential-diagram-flattening-lemma c P)
              ( cocone-sequential-diagram-flattening-lemma c P)) ,
            ( coherence-cofork _ _
              ( cofork-flattening-lemma-coequalizer _ _ P
                ( cofork-cocone-sequential-diagram A c))) ,
            ( ind-Σ (λ n → ind-Σ (λ a p → ap-id _ ∙ inv right-unit))))
          ( is-equiv-map-equiv
            ( inv-associative-Σ ℕ
              ( family-sequential-diagram A)
              ( P ∘ ind-Σ (map-cocone-sequential-diagram A c))))
          ( is-equiv-map-inv-associative-Σ ℕ
            ( family-sequential-diagram A)
            ( P ∘ ind-Σ (map-cocone-sequential-diagram A c)))
          ( is-equiv-id)
          ( flattening-lemma-coequalizer
            ( bottom-map-cofork-cocone-sequential-diagram A)
            ( top-map-cofork-cocone-sequential-diagram A)
            ( P)
            ( cofork-cocone-sequential-diagram A c)
            ( dependent-universal-property-coequalizer-dependent-universal-property-sequential-colimit
              ( A)
              ( c)
              ( dup-c))))
```
