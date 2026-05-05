# The flattening lemma for sequential colimits

```agda
module synthetic-homotopy-theory.flattening-lemma-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-double-arrows
open import foundation.function-types
open import foundation.homotopies
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrows
open import synthetic-homotopy-theory.families-descent-data-sequential-colimits
open import synthetic-homotopy-theory.flattening-lemma-coequalizers
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.total-cocones-families-sequential-diagrams
open import synthetic-homotopy-theory.total-sequential-diagrams
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

with the universal property of sequential colimits, and a family `P : X → 𝒰`,
the induced cocone under the
[total sequential diagram](synthetic-homotopy-theory.total-sequential-diagrams.md)

```text
  Σ (a : A₀) P(i₀ a) ---> Σ (a : A₁) P(i₁ a) ---> ⋯ ---> Σ (x : X) P(x)
```

is again a sequential colimit.

The result may be read as
`colimₙ (Σ (a : Aₙ) P(iₙ a)) ≃ Σ (a : colimₙ Aₙ) P(a)`.

More generally, given a type family `P : X → 𝒰` and
[descent data](synthetic-homotopy-theory.descent-data-sequential-colimits.md)
`B`
[associated to it](synthetic-homotopy-theory.families-descent-data-sequential-colimits.md),
we have that the induced cocone

```text
  Σ A₀ B₀ ---> Σ A₁ B₁ ---> ⋯ ---> Σ X P
```

is a sequential colimit.

## Theorems

### Flattening lemma for sequential colimits

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
             ∨                --------->           ∨                            ∨
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
        ( total-sequential-diagram-family-cocone-sequential-diagram c P))
      ( double-arrow-flattening-lemma-coequalizer
        ( double-arrow-sequential-diagram A)
        ( P)
        ( cofork-cocone-sequential-diagram c))
  pr1 equiv-double-arrow-flattening-lemma-sequential-colimit =
    inv-associative-Σ
  pr1 (pr2 equiv-double-arrow-flattening-lemma-sequential-colimit) =
    inv-associative-Σ
  pr1 (pr2 (pr2 equiv-double-arrow-flattening-lemma-sequential-colimit)) =
    refl-htpy
  pr2 (pr2 (pr2 equiv-double-arrow-flattening-lemma-sequential-colimit)) =
    refl-htpy

  equiv-cofork-flattening-lemma-sequential-colimit :
    equiv-cofork-equiv-double-arrow
      ( cofork-cocone-sequential-diagram
        ( total-cocone-family-cocone-sequential-diagram c P))
      ( cofork-flattening-lemma-coequalizer
        ( double-arrow-sequential-diagram A)
        ( P)
        ( cofork-cocone-sequential-diagram c))
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
            ( cofork-cocone-sequential-diagram
              ( total-cocone-family-cocone-sequential-diagram c P)))))

  abstract
    flattening-lemma-sequential-colimit :
      universal-property-sequential-colimit c →
      universal-property-sequential-colimit
        ( total-cocone-family-cocone-sequential-diagram c P)
    flattening-lemma-sequential-colimit up-c =
      universal-property-sequential-colimit-universal-property-coequalizer
        ( total-cocone-family-cocone-sequential-diagram c P)
        ( universal-property-coequalizer-equiv-cofork-equiv-double-arrow
          ( cofork-cocone-sequential-diagram
            ( total-cocone-family-cocone-sequential-diagram c P))
          ( cofork-flattening-lemma-coequalizer _
            ( P)
            ( cofork-cocone-sequential-diagram c))
          ( equiv-double-arrow-flattening-lemma-sequential-colimit)
          ( equiv-cofork-flattening-lemma-sequential-colimit)
          ( flattening-lemma-coequalizer _
            ( P)
            ( cofork-cocone-sequential-diagram c)
            ( universal-property-coequalizer-universal-property-sequential-colimit
              ( c)
              ( up-c))))
```

### Flattening lemma for sequential colimits with descent data

**Proof:** We have shown in
[`total-cocones-families-sequential-diagrams`](synthetic-homotopy-theory.total-cocones-families-sequential-diagrams.md)
that given a family `P : X → 𝒰` with its descent data `B`, there is an
[equivalence of cocones](synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams.md)

```text
     Σ A₀ B₀ ---------> Σ A₁ B₁ ------> ⋯ -----> Σ X P
        |                  |                       |
        | ≃                | ≃                     | ≃
        ∨                  ∨                       ∨
  Σ A₀ (P ∘ i₀) ---> Σ A₁ (P ∘ i₁) ---> ⋯ -----> Σ X P .
```

The bottom cocone is a sequential colimit by the flattening lemma, and the
universal property of sequential colimits is preserved by equivalences, as shown
in
[`universal-property-sequential-colimits`](synthetic-homotopy-theory.universal-property-sequential-colimits.md).

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {X : UU l2} (c : cocone-sequential-diagram A X)
  (P : family-with-descent-data-sequential-colimit c l3)
  where

  abstract
    flattening-lemma-descent-data-sequential-colimit :
      universal-property-sequential-colimit c →
      universal-property-sequential-colimit
        ( total-cocone-family-with-descent-data-sequential-colimit P)
    flattening-lemma-descent-data-sequential-colimit up-c =
      universal-property-sequential-colimit-equiv-cocone-equiv-sequential-diagram
        ( equiv-total-sequential-diagram-family-with-descent-data-sequential-colimit
          ( P))
        ( equiv-total-cocone-family-with-descent-data-sequential-colimit P)
        ( flattening-lemma-sequential-colimit c
          ( family-cocone-family-with-descent-data-sequential-colimit P)
          ( up-c))
```
