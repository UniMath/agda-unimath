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
-- open import foundation.binary-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
-- open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
-- open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.implicit-function-types
open import foundation.postcomposition-functions
open import foundation.precomposition-dependent-functions
open import foundation.transport-along-identifications
-- open import foundation.transposition-identifications-along-equivalences
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
-- open import foundation.whiskering-homotopies-concatenation

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-sequential-diagrams
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.descent-data-sequential-colimits
open import synthetic-homotopy-theory.functoriality-sequential-colimits
open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.stuff-over
open import synthetic-homotopy-theory.universal-property-sequential-colimits

open import foundation.binary-homotopies
open import foundation.commuting-squares-of-homotopies
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
```

</details>

## Theorem

-- ```agda
module _
  {l1 l2 : Level}
  {A : sequential-diagram l1}
  (P : descent-data-sequential-colimit A l2)
  where

  section-descent-data-sequential-colimit : UU (l1 ⊔ l2)
  section-descent-data-sequential-colimit =
    section-dependent-sequential-diagram A
      ( dependent-sequential-diagram-descent-data P)

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

module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  (c : cocone-sequential-diagram A X)
  (P : X → UU l3)
  where
  open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams

  section-descent-data-section-family-cocone-sequential-colimit :
    ((x : X) → P x) →
    section-descent-data-sequential-colimit
      ( descent-data-family-cocone-sequential-diagram c P)
  section-descent-data-section-family-cocone-sequential-colimit =
    dependent-cocone-map-sequential-diagram c P
```

-- ```agda
-- module big-thm
--   {l1 l2 l3 l4 l5 l6 : Level}
--   {A : sequential-diagram l1}
--   {B : sequential-diagram l2}
--   {X : UU l3} {c : cocone-sequential-diagram A X}
--   (up-c : universal-property-sequential-colimit c)
--   {Y : UU l4} {c' : cocone-sequential-diagram B Y}
--   (up-c' : universal-property-sequential-colimit c')
--   (H : hom-sequential-diagram A B)
--   where

--   -- the squares induce a map

--   f∞ : X → Y
--   f∞ = map-sequential-colimit-hom-sequential-diagram up-c c' H

--   Cn : (n : ℕ) →
--     f∞ ∘ map-cocone-sequential-diagram c n ~
--     map-cocone-sequential-diagram c' n ∘ map-hom-sequential-diagram B H n
--   Cn =
--     htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' H

--   module _
--     (P : X → UU l5) (Q : Y → UU l6)
--     (f'∞ : {x : X} → P x → Q (f∞ x))
--     where

--     An : ℕ → UU l1
--     An = family-sequential-diagram A
--     Bn : ℕ → UU l2
--     Bn = family-sequential-diagram B
--     an : {n : ℕ} → An n → An (succ-ℕ n)
--     an = map-sequential-diagram A _
--     bn : {n : ℕ} → Bn n → Bn (succ-ℕ n)
--     bn = map-sequential-diagram B _
--     fn : {n : ℕ} → An n → Bn n
--     fn = map-hom-sequential-diagram B H _
--     Hn : {n : ℕ} → bn {n} ∘ fn ~ fn ∘ an
--     Hn = naturality-map-hom-sequential-diagram B H _

--     -- a map-over induces squares-over

--     -- first, the sequences-over:
--     𝒟P : descent-data-sequential-colimit A l5
--     𝒟P = descent-data-family-cocone-sequential-diagram c P
--     𝒫 = dependent-sequential-diagram-descent-data 𝒟P
--     𝒟Q : descent-data-sequential-colimit B l6
--     𝒟Q = descent-data-family-cocone-sequential-diagram c' Q
--     𝒬 = dependent-sequential-diagram-descent-data 𝒟Q

--     Pn : {n : ℕ} → An n → UU l5
--     Pn = family-descent-data-sequential-colimit 𝒟P _
--     Qn : {n : ℕ} → Bn n → UU l6
--     Qn = family-descent-data-sequential-colimit 𝒟Q _

--     pn : {n : ℕ} (a : An n) → Pn a → Pn (an a)
--     pn = map-family-descent-data-sequential-colimit 𝒟P _
--     qn : {n : ℕ} (b : Bn n) → Qn b → Qn (bn b)
--     qn = map-family-descent-data-sequential-colimit 𝒟Q _

--     -- then, the maps over homs
--     f'∞n : {n : ℕ} (a : An n) → Pn a → Qn (fn a)
--     f'∞n a =
--       ( tr Q
--         ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c'
--           ( H)
--           ( _)
--           ( a))) ∘
--       ( f'∞)

--     -- then, the squares-over
--     f'∞n-square-over :
--       {n : ℕ} →
--       square-over {Q4 = Qn} (an {n}) fn fn bn (pn _) (f'∞n _) (f'∞n _) (qn _) Hn
--     f'∞n-square-over {n} {a} =
--       pasting-vertical-coherence-square-maps
--         ( tr P (coherence-cocone-sequential-diagram c n a))
--         ( f'∞)
--         ( f'∞)
--         ( tr Q (ap f∞ (coherence-cocone-sequential-diagram c n a)))
--         ( tr Q (htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' H _ a))
--         ( tr Q (htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' H _ (an a)))
--         ( ( tr
--             ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
--             ( Hn a)) ∘
--           ( tr Q (coherence-cocone-sequential-diagram c' n (fn a))))
--         ( λ q →
--           substitution-law-tr Q f∞ (coherence-cocone-sequential-diagram c n a) ∙
--           inv (preserves-tr (λ p → f'∞ {p}) (coherence-cocone-sequential-diagram c n a) q))
--         ( ( inv-htpy
--             ( λ q →
--               ( tr-concat
--                 ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--                   up-c c' H n a)
--                 ( _)
--                 ( q)) ∙
--               ( tr-concat
--                 ( coherence-cocone-sequential-diagram c' n (fn a))
--                 ( ap (map-cocone-sequential-diagram c' (succ-ℕ n)) (Hn a))
--                 ( tr Q
--                   ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--                     up-c c' H n a)
--                   ( q))) ∙
--               ( substitution-law-tr Q
--                 ( map-cocone-sequential-diagram c' (succ-ℕ n))
--                 ( Hn a)))) ∙h
--           ( λ q →
--             ap
--               ( λ p → tr Q p q)
--               ( inv
--                 ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' H n a))) ∙h
--           ( tr-concat
--             ( ap f∞ (coherence-cocone-sequential-diagram c n a))
--             ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--               up-c c' H (succ-ℕ n) (an a))))

--     thm :
--       (sA : section-dependent-sequential-diagram A 𝒫) →
--       (sB : section-dependent-sequential-diagram B 𝒬) →
--       (S : (n : ℕ) →
--         section-map-over (fn {n}) (f'∞n _)
--           ( map-section-dependent-sequential-diagram A 𝒫 sA n)
--           ( map-section-dependent-sequential-diagram B 𝒬 sB n)) →
--       ((n : ℕ) →
--         section-square-over (an {n}) fn fn bn (pn _) (f'∞n _) (f'∞n _) (qn _)
--           ( map-section-dependent-sequential-diagram A 𝒫 sA n)
--           ( map-section-dependent-sequential-diagram B 𝒬 sB n)
--           ( map-section-dependent-sequential-diagram A 𝒫 sA (succ-ℕ n))
--           ( map-section-dependent-sequential-diagram B 𝒬 sB (succ-ℕ n))
--           ( naturality-map-section-dependent-sequential-diagram A 𝒫 sA n)
--           ( S n)
--           ( S (succ-ℕ n))
--           ( naturality-map-section-dependent-sequential-diagram B 𝒬 sB n)
--           ( Hn)
--           ( f'∞n-square-over)) →
--       section-map-over f∞ f'∞
--         ( sect-family-sect-dd-sequential-colimit up-c P sA)
--         ( sect-family-sect-dd-sequential-colimit up-c' Q sB)
--     thm sA sB S α =
--       map-dependent-universal-property-sequential-colimit
--         ( dependent-universal-property-universal-property-sequential-colimit _ up-c)
--         ( tS ,
--           ( λ n a →
--             map-compute-dependent-identification-eq-value
--               ( f'∞ ∘ sA∞)
--               ( sB∞ ∘ f∞)
--               ( coherence-cocone-sequential-diagram c n a)
--               ( tS n a)
--               ( tS (succ-ℕ n) (an a))
--               ( {!f'∞n-square-over!})))
--       where
--         sA∞ : (x : X) → P x
--         sA∞ = sect-family-sect-dd-sequential-colimit up-c P sA
--         sB∞ : (y : Y) → Q y
--         sB∞ = sect-family-sect-dd-sequential-colimit up-c' Q sB
--         tS :
--           (n : ℕ) →
--           (f'∞ ∘ sA∞ ∘ (map-cocone-sequential-diagram c n)) ~
--           (sB∞ ∘ f∞ ∘ map-cocone-sequential-diagram c n)
--         tS n a =
--           ap f'∞
--             ( pr1
--               ( htpy-dependent-cocone-dependent-universal-property-sequential-colimit
--                 ( dependent-universal-property-universal-property-sequential-colimit _ up-c)
--                 ( sA)) n a) ∙
--           map-equiv
--             ( inv-equiv-ap-emb (emb-equiv (equiv-tr Q (Cn n a))))
--             ( S n a ∙
--               inv
--                 ( apd sB∞ (Cn n a) ∙
--                   pr1
--                     ( htpy-dependent-cocone-dependent-universal-property-sequential-colimit
--                       ( dependent-universal-property-universal-property-sequential-colimit _ up-c')
--                       ( sB)) n (fn a)))
```

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {B : dependent-sequential-diagram A l2}
  (s t : section-dependent-sequential-diagram A B)
  where

  htpy-section-dependent-sequential-diagram : UU (l1 ⊔ l2)
  htpy-section-dependent-sequential-diagram =
    Σ ((n : ℕ) →
        map-section-dependent-sequential-diagram A B s n ~
        map-section-dependent-sequential-diagram A B t n)
      ( λ H →
        (n : ℕ) →
        coherence-square-homotopies
          ( map-dependent-sequential-diagram B n _ ·l H n)
          ( naturality-map-section-dependent-sequential-diagram A B s n)
          ( naturality-map-section-dependent-sequential-diagram A B t n)
          ( H (succ-ℕ n) ·r map-sequential-diagram A n))

module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {B : dependent-sequential-diagram A l2}
  (s : section-dependent-sequential-diagram A B)
  where

  refl-htpy-section-dependent-sequential-diagram :
    htpy-section-dependent-sequential-diagram s s
  pr1 refl-htpy-section-dependent-sequential-diagram n =
    refl-htpy
  pr2 refl-htpy-section-dependent-sequential-diagram n =
    right-unit-htpy

  htpy-eq-section-dependent-sequential-diagram :
    (t : section-dependent-sequential-diagram A B) →
    s ＝ t → htpy-section-dependent-sequential-diagram s t
  htpy-eq-section-dependent-sequential-diagram .s refl =
    refl-htpy-section-dependent-sequential-diagram

  abstract
    is-torsorial-htpy-section-dependent-sequential-diagram :
      is-torsorial (htpy-section-dependent-sequential-diagram s)
    is-torsorial-htpy-section-dependent-sequential-diagram =
      is-torsorial-Eq-structure
        ( is-torsorial-binary-htpy _)
        ( pr1 s , λ n → refl-htpy)
        ( is-torsorial-binary-htpy _)

    is-equiv-htpy-eq-section-dependent-sequential-diagram :
      (t : section-dependent-sequential-diagram A B) →
      is-equiv (htpy-eq-section-dependent-sequential-diagram t)
    is-equiv-htpy-eq-section-dependent-sequential-diagram =
      fundamental-theorem-id
        ( is-torsorial-htpy-section-dependent-sequential-diagram)
        ( htpy-eq-section-dependent-sequential-diagram)

  equiv-htpy-eq-section-dependent-sequential-diagram :
    (t : section-dependent-sequential-diagram A B) →
    (s ＝ t) ≃
    htpy-section-dependent-sequential-diagram s t
  equiv-htpy-eq-section-dependent-sequential-diagram t =
    ( htpy-eq-section-dependent-sequential-diagram t ,
      is-equiv-htpy-eq-section-dependent-sequential-diagram t)

  eq-htpy-section-dependent-sequential-diagram :
    (t : section-dependent-sequential-diagram A B) →
    htpy-section-dependent-sequential-diagram s t →
    s ＝ t
  eq-htpy-section-dependent-sequential-diagram t =
    map-inv-equiv (equiv-htpy-eq-section-dependent-sequential-diagram t)

module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  (B : descent-data-sequential-colimit A l2)
  (s t : section-descent-data-sequential-colimit B)
  where

  eq-htpy-section-descent-data-sequential-colimit :
    htpy-section-dependent-sequential-diagram s t →
    s ＝ t
  eq-htpy-section-descent-data-sequential-colimit =
    eq-htpy-section-dependent-sequential-diagram s t

module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  (P : X → UU l3)
  (let P' = descent-data-family-cocone-sequential-diagram c P)
  (s t : section-descent-data-sequential-colimit P')
  where

  htpy-colimit-htpy-diagram-section :
    htpy-section-dependent-sequential-diagram s t →
    sect-family-sect-dd-sequential-colimit up-c P s ~
    sect-family-sect-dd-sequential-colimit up-c P t
  htpy-colimit-htpy-diagram-section H =
    htpy-eq
      ( ap
        ( sect-family-sect-dd-sequential-colimit up-c P)
        ( eq-htpy-section-dependent-sequential-diagram s t H))
```

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1} {X : UU l2}
  {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  (P : X → UU l3)
  where

  htpy-section-out-of-sequential-colimit : (s t : (x : X) → P x) → UU (l1 ⊔ l3)
  htpy-section-out-of-sequential-colimit s t =
    htpy-section-dependent-sequential-diagram
      ( section-descent-data-section-family-cocone-sequential-colimit c P s)
      ( section-descent-data-section-family-cocone-sequential-colimit c P t)

  equiv-htpy-section-out-of-sequential-colimit :
    (s t : (x : X) → P x) →
    htpy-section-out-of-sequential-colimit s t ≃ (s ~ t)
  equiv-htpy-section-out-of-sequential-colimit s t =
    ( inv-equiv
      ( equiv-dependent-universal-property-sequential-colimit
        ( dependent-universal-property-universal-property-sequential-colimit c
          ( up-c)))) ∘e
    ( equiv-tot
      ( λ H →
        equiv-Π-equiv-family
          ( λ n →
            equiv-Π-equiv-family
              ( λ a →
                compute-dependent-identification-eq-value s t
                  ( coherence-cocone-sequential-diagram c n a)
                  ( H n a)
                  ( H (succ-ℕ n) (map-sequential-diagram A n a))))))

  -- (2.i)
  htpy-htpy-section-out-of-sequential-colimit :
    (s t : (x : X) → P x) →
    htpy-section-out-of-sequential-colimit s t → (s ~ t)
  htpy-htpy-section-out-of-sequential-colimit s t =
    map-equiv (equiv-htpy-section-out-of-sequential-colimit s t)
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : sequential-diagram l1} {X : UU l2}
  {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {B : sequential-diagram l3} {Y : UU l4}
  {c' : cocone-sequential-diagram B Y}
  (up-c' : universal-property-sequential-colimit c')
  (Q : Y → UU l5)
  (let Q' = descent-data-family-cocone-sequential-diagram c' Q)
  (f : hom-sequential-diagram A B)
  (let f∞ = map-sequential-colimit-hom-sequential-diagram up-c c' f)
  (let P = Q ∘ f∞)
  (let P' = descent-data-family-cocone-sequential-diagram c P)
  (let C = htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f)
  (s : section-descent-data-sequential-colimit Q')
  (let s∞ = sect-family-sect-dd-sequential-colimit up-c' Q s)
  -- remove later
  (t : section-descent-data-sequential-colimit P')
  (let t∞ = sect-family-sect-dd-sequential-colimit up-c P t)
  where

  private
    γ :
      (n : ℕ) (a : family-sequential-diagram A n) →
      coherence-square-maps
        ( tr (Q ∘ f∞) (coherence-cocone-sequential-diagram c n a))
        ( tr Q (C n a))
        ( tr Q (C (succ-ℕ n) (map-sequential-diagram A n a)))
        ( ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a)) ∘
          ( tr Q
            ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a))))
    γ n a q =
      inv
        ( ( tr-concat
            ( C n a)
            ( _)
            ( q)) ∙
          ( tr-concat
            ( coherence-cocone-sequential-diagram c' n (map-hom-sequential-diagram B f n a))
            ( ap (map-cocone-sequential-diagram c' (succ-ℕ n)) _)
            ( _)) ∙
          ( substitution-law-tr Q
            ( map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a))) ∙
      ap
        ( λ p → tr Q p q)
        ( inv
          ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f n a)) ∙
      tr-concat
        ( ap f∞ (coherence-cocone-sequential-diagram c n a))
        ( C (succ-ℕ n) (map-sequential-diagram A n a))
        ( q) ∙
      ap
        ( tr Q (C (succ-ℕ n) (map-sequential-diagram A n a)))
        ( substitution-law-tr Q f∞ (coherence-cocone-sequential-diagram c n a))

    γ-flip :
      (n : ℕ) (a : family-sequential-diagram A n) →
      coherence-square-maps
        ( ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a)) ∘
          ( tr Q
            ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a))))
        ( tr Q (inv (C n a)))
        ( tr Q (inv (C (succ-ℕ n) (map-sequential-diagram A n a))))
        ( tr (Q ∘ f∞) (coherence-cocone-sequential-diagram c n a))
    γ-flip n a =
      vertical-inv-equiv-coherence-square-maps
        ( tr (Q ∘ f∞) (coherence-cocone-sequential-diagram c n a))
        ( equiv-tr Q (C n a))
        ( equiv-tr Q (C (succ-ℕ n) (map-sequential-diagram A n a)))
        ( ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a)) ∘
          ( tr Q
            ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a))))
        ( γ n a)

  comp-over-diagram :
    section-descent-data-sequential-colimit
      ( descent-data-family-cocone-sequential-diagram c (Q ∘ f∞))
  pr1 comp-over-diagram n a =
    tr Q
      ( inv (C n a))
      ( map-section-dependent-sequential-diagram _ _ s n
        (map-hom-sequential-diagram B f n a))
  pr2 comp-over-diagram n a =
    ( γ-flip n a
      ( map-section-dependent-sequential-diagram _ _ s n
        ( map-hom-sequential-diagram B f n a))) ∙
    ( ap
      ( tr Q (inv (C (succ-ℕ n) (map-sequential-diagram A n a))))
      ( ( ap
          ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a))
          ( naturality-map-section-dependent-sequential-diagram _ _ s n
            ( map-hom-sequential-diagram B f n a))) ∙
        ( apd
          ( map-section-dependent-sequential-diagram _ _ s (succ-ℕ n))
          ( naturality-map-hom-sequential-diagram B f n a))))

  lemma-1-1 :
    htpy-section-dependent-sequential-diagram
      ( section-descent-data-section-family-cocone-sequential-colimit c P
        ( sect-family-sect-dd-sequential-colimit up-c P comp-over-diagram))
      ( comp-over-diagram)
  lemma-1-1 =
    htpy-dependent-cocone-dependent-universal-property-sequential-colimit
      ( dependent-universal-property-universal-property-sequential-colimit _ up-c)
      ( comp-over-diagram)

  -- needs work
  lemma-1-2 :
    htpy-section-dependent-sequential-diagram
      ( section-descent-data-section-family-cocone-sequential-colimit c P
        ( s∞ ∘ f∞))
      ( comp-over-diagram)
  pr1 lemma-1-2 n a = {!!}
  pr2 lemma-1-2 = {!!}

  lemma-1 :
    s∞ ∘ f∞ ~ sect-family-sect-dd-sequential-colimit up-c P comp-over-diagram
  lemma-1 =
    htpy-htpy-section-out-of-sequential-colimit up-c P _ _
      ( concat-htpy-dependent-cocone-sequential-diagram P
        ( lemma-1-2)
        ( inv-htpy-dependent-cocone-sequential-diagram P lemma-1-1))

  -- needs work, needs another input
  lemma-2 : htpy-section-dependent-sequential-diagram t comp-over-diagram
  pr1 lemma-2 = {!!}
  pr2 lemma-2 = {!!}

  theorem : t∞ ~ s∞ ∘ f∞
  theorem =
    htpy-colimit-htpy-diagram-section up-c P t comp-over-diagram lemma-2 ∙h
    inv-htpy lemma-1
```

