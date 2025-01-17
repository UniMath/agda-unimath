# Functoriality stuff

```agda
{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}

module synthetic-homotopy-theory.functoriality-stuff where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
-- open import foundation.commuting-squares-of-maps
-- open import foundation.commuting-triangles-of-maps
-- open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
-- open import foundation.function-extensionality
open import foundation.function-types
-- open import foundation.functoriality-dependent-function-types
open import foundation.homotopies
-- open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.transport-along-identifications
-- open import foundation.transposition-identifications-along-equivalences
open import foundation.universe-levels
-- open import foundation.whiskering-homotopies-composition
-- open import foundation.whiskering-homotopies-concatenation

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-sequential-diagrams
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.descent-data-sequential-colimits
open import synthetic-homotopy-theory.functoriality-sequential-colimits
open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.stuff-over
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

## Theorem

```agda
module _
  {l1 l2 : Level}
  {A : sequential-diagram l1}
  (P : descent-data-sequential-colimit A l2)
  where

  section-descent-data-sequential-colimit : UU (l1 ⊔ l2)
  section-descent-data-sequential-colimit =
    Σ ( (n : ℕ) (a : family-sequential-diagram A n) →
        family-descent-data-sequential-colimit P n a)
      ( λ s →
        (n : ℕ) (a : family-sequential-diagram A n) →
        map-family-descent-data-sequential-colimit P n a (s n a) ＝
        s (succ-ℕ n) (map-sequential-diagram A n a))

module _
  {l1 l2 l3 : Level}
  {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  (P : X → UU l3)
  where

  sect-family-sect-dd-sequential-colimit :
    section-descent-data-sequential-colimit
      ( descent-data-family-cocone-sequential-diagram c P) →
    ((x : X) → P x)
  sect-family-sect-dd-sequential-colimit s =
    map-dependent-universal-property-sequential-colimit
      ( dependent-universal-property-universal-property-sequential-colimit _ up-c)
      ( s)
```

```agda
module big-thm
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : sequential-diagram l1}
  {B : sequential-diagram l2}
  {X : UU l3} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {Y : UU l4} {c' : cocone-sequential-diagram B Y}
  (up-c' : universal-property-sequential-colimit c')
  (H : hom-sequential-diagram A B)
  where

  -- the squares induce a map

  f∞ : X → Y
  f∞ = map-sequential-colimit-hom-sequential-diagram up-c c' H

  Cn : (n : ℕ) →
    f∞ ∘ map-cocone-sequential-diagram c n ~
    map-cocone-sequential-diagram c' n ∘ map-hom-sequential-diagram B H n
  Cn =
    htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' H

  module _
    (P : X → UU l5) (Q : Y → UU l6)
    (f'∞ : {x : X} → P x → Q (f∞ x))
    where

    An : ℕ → UU l1
    An = family-sequential-diagram A
    Bn : ℕ → UU l2
    Bn = family-sequential-diagram B
    an : {n : ℕ} → An n → An (succ-ℕ n)
    an = map-sequential-diagram A _
    bn : {n : ℕ} → Bn n → Bn (succ-ℕ n)
    bn = map-sequential-diagram B _
    fn : {n : ℕ} → An n → Bn n
    fn = map-hom-sequential-diagram B H _
    Hn : {n : ℕ} → bn {n} ∘ fn ~ fn ∘ an
    Hn = naturality-map-hom-sequential-diagram B H _

    -- a map-over induces squares-over

    -- first, the sequences-over:
    𝒟P : descent-data-sequential-colimit A l5
    𝒟P = descent-data-family-cocone-sequential-diagram c P
    𝒫 = dependent-sequential-diagram-descent-data 𝒟P
    𝒟Q : descent-data-sequential-colimit B l6
    𝒟Q = descent-data-family-cocone-sequential-diagram c' Q
    𝒬 = dependent-sequential-diagram-descent-data 𝒟Q

    Pn : {n : ℕ} → An n → UU l5
    Pn = family-descent-data-sequential-colimit 𝒟P _
    Qn : {n : ℕ} → Bn n → UU l6
    Qn = family-descent-data-sequential-colimit 𝒟Q _

    pn : {n : ℕ} (a : An n) → Pn a → Pn (an a)
    pn = map-family-descent-data-sequential-colimit 𝒟P _
    qn : {n : ℕ} (b : Bn n) → Qn b → Qn (bn b)
    qn = map-family-descent-data-sequential-colimit 𝒟Q _

    -- then, the maps over homs
    f'∞n : {n : ℕ} (a : An n) → Pn a → Qn (fn a)
    f'∞n a =
      ( tr Q
        ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c'
          ( H)
          ( _)
          ( a))) ∘
      ( f'∞)

    -- then, the squares-over
    f'∞n-square-over :
      {n : ℕ} →
      square-over {Q4 = Qn} (an {n}) fn fn bn (pn _) (f'∞n _) (f'∞n _) (qn _) Hn
    f'∞n-square-over p = {!qn!}

    thm :
      (sA : section-dependent-sequential-diagram A 𝒫) →
      (sB : section-dependent-sequential-diagram B 𝒬) →
      (S : (n : ℕ) →
        section-map-over (fn {n}) (f'∞n _)
          ( map-section-dependent-sequential-diagram A 𝒫 sA n)
          ( map-section-dependent-sequential-diagram B 𝒬 sB n)) →
      ((n : ℕ) →
        section-square-over (an {n}) fn fn bn (pn _) (f'∞n _) (f'∞n _) (qn _)
          ( map-section-dependent-sequential-diagram A 𝒫 sA n)
          ( map-section-dependent-sequential-diagram B 𝒬 sB n)
          ( map-section-dependent-sequential-diagram A 𝒫 sA (succ-ℕ n))
          ( map-section-dependent-sequential-diagram B 𝒬 sB (succ-ℕ n))
          ( naturality-map-section-dependent-sequential-diagram A 𝒫 sA n)
          ( S n)
          ( S (succ-ℕ n))
          ( naturality-map-section-dependent-sequential-diagram B 𝒬 sB n)
          ( Hn)
          ( f'∞n-square-over)) →
      section-map-over f∞ f'∞
        ( sect-family-sect-dd-sequential-colimit up-c P sA)
        ( sect-family-sect-dd-sequential-colimit up-c' Q sB)
    thm sA sB S α =
      map-dependent-universal-property-sequential-colimit
        ( dependent-universal-property-universal-property-sequential-colimit _ up-c)
        ( ( λ n a →
            ap f'∞
              ( pr1
                ( htpy-dependent-cocone-dependent-universal-property-sequential-colimit
                  ( dependent-universal-property-universal-property-sequential-colimit _ up-c)
                  ( sA)) n a) ∙
            map-equiv
              ( inv-equiv-ap-emb (emb-equiv (equiv-tr Q (Cn n a))))
              ( S n a ∙
                inv
                  ( apd sB∞ (Cn n a) ∙
                    pr1
                      ( htpy-dependent-cocone-dependent-universal-property-sequential-colimit
                        ( dependent-universal-property-universal-property-sequential-colimit _ up-c')
                        ( sB)) n (fn a)))) ,
          {!!})
      where
        sA∞ : (x : X) → P x
        sA∞ = sect-family-sect-dd-sequential-colimit up-c P sA
        sB∞ : (y : Y) → Q y
        sB∞ = sect-family-sect-dd-sequential-colimit up-c' Q sB
```
