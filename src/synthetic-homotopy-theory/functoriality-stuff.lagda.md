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
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (s : (a : A) → B a) (t : (a : A) → C a)
  (e : (a : A) → B a ≃ C a)
  (H : (a : A) → map-equiv (e a) (s a) ＝ t a)
  where
  open import foundation.action-on-identifications-binary-functions

  invert-fiberwise-triangle : (a : A) → s a ＝ map-inv-equiv (e a) (t a)
  invert-fiberwise-triangle a =
    inv (is-retraction-map-inv-equiv (e a) (s a)) ∙
    ap (map-inv-equiv (e a)) (H a)

  invert-fiberwise-triangle' : (a : A) → map-inv-equiv (e a) (t a) ＝ s a
  invert-fiberwise-triangle' a =
    ap (map-inv-equiv (e a)) (inv (H a)) ∙
    is-retraction-map-inv-equiv (e a) (s a)

  compute-inv-invert-fiberwise-triangle :
    (a : A) →
    inv (invert-fiberwise-triangle a) ＝
    invert-fiberwise-triangle' a
  compute-inv-invert-fiberwise-triangle a =
    distributive-inv-concat
      ( inv (is-retraction-map-inv-equiv (e a) (s a)))
      ( ap (map-inv-equiv (e a)) (H a)) ∙
    ap-binary (_∙_)
      ( inv (ap-inv (map-inv-equiv (e a)) (H a)))
      ( inv-inv (is-retraction-map-inv-equiv (e a) (s a)))

  compute-inv-invert-fiberwise-triangle' :
    (a : A) →
    inv (invert-fiberwise-triangle' a) ＝
    invert-fiberwise-triangle a
  compute-inv-invert-fiberwise-triangle' a =
    distributive-inv-concat
      ( ap (map-inv-equiv (e a)) (inv (H a)))
      ( is-retraction-map-inv-equiv (e a) (s a)) ∙
    ap
      ( inv (is-retraction-map-inv-equiv (e a) (s a)) ∙_)
      ( ap inv (ap-inv (map-inv-equiv (e a)) (H a)) ∙ inv-inv _)
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2}
  {P : A → UU l3} {Q : B → UU l4} {P' : A → UU l5} {Q' : B → UU l6}
  (f : A → B)
  (s : (a : A) → P a) (t : (b : B) → Q b)
  (s' : (a : A) → P' a) (t' : (b : B) → Q' b)
  (f' : {a : A} → P a → Q (f a))
  (f'' : {a : A} → P' a → Q' (f a))
  (e : {a : A} → P a ≃ P' a)
  (let g = λ {a} → map-equiv (e {a}))
  (let inv-g = λ {a} → map-inv-equiv (e {a}))
  (j : {b : B} → Q b ≃ Q' b)
  (let h = λ {b} → map-equiv (j {b}))
  (let inv-h = λ {b} → map-inv-equiv (j {b}))
  (T : (a : A) → f' (s a) ＝ t (f a))
  (G : {a : A} (p : P a) → f'' (g p) ＝ h (f' p))
  (let
    inv-G =
      λ {a} (p : P' a) →
        vertical-inv-equiv-coherence-square-maps f' e j f'' G p)
  (F : (b : B) → h (t b) ＝ t' b)
  (let inv-F = invert-fiberwise-triangle t t' (λ b → j {b}) F)
  (let inv-F' = invert-fiberwise-triangle' t t' (λ b → j {b}) F)
  (H : (a : A) → g (s a) ＝ s' a)
  (let inv-H = invert-fiberwise-triangle s s' (λ a → e {a}) H)
  -- (X : (a : A) → f'' (g (s a)) ＝ t' (f a))
  (X : (a : A) → f'' (s' a) ＝ t' (f a))
  -- (α : (a : A) → G (s a) ∙ (ap h (T a) ∙ F (f a)) ＝ X a)
  (α : (a : A) → G (s a) ∙ (ap h (T a) ∙ F (f a)) ＝ ap f'' (H a) ∙ X a)
  where

  opaque
    transpose-sq :
      (a : A) →
      T a ∙ inv-F (f a) ＝
      ap f' (inv-H a) ∙
      ( inv-G (s' a) ∙
        ap inv-h (X a))
    transpose-sq a =
      ap
        ( T a ∙_)
        ( inv (compute-inv-invert-fiberwise-triangle' t t' (λ b → j {b}) F (f a))) ∙
      right-transpose-eq-concat'
        ( T a)
        ( _)
        ( inv-F' (f a))
        ( [g])
      where
      [i] :
        ap f' (is-retraction-map-inv-equiv e (s a)) ＝
        ( pasting-vertical-coherence-square-maps f' g h f'' inv-g inv-h f'
            G inv-G (s a) ∙
          is-retraction-map-inv-equiv j (f' (s a)))
      [i] =
        inv right-unit ∙
        left-inverse-law-pasting-vertical-coherence-square-maps f' e j f'' G (s a)
      [a] :
        ap inv-h (G (s a) ∙ (ap h (T a) ∙ F (f a))) ＝
        ap inv-h (ap f'' (H a) ∙ X a)
      [a] = ap (ap inv-h) (α a)
      [b] : ap inv-h (G (s a)) ∙
            ap inv-h (ap h (T a) ∙ F (f a)) ＝
            ap inv-h (ap f'' (H a) ∙ X a)
      [b] = inv (ap-concat inv-h (G (s a)) (ap h (T a) ∙ F (f a))) ∙ [a]
      [c] :
        ap inv-h (G (s a)) ∙
        ( ap (inv-h ∘ h) (T a) ∙ ap inv-h (F (f a))) ＝
        ap inv-h (ap f'' (H a) ∙ X a)
      [c] =
        ap
          ( ap inv-h (G (s a)) ∙_)
          ( ap (_∙ ap inv-h (F (f a))) (ap-comp inv-h h (T a)) ∙
            inv (ap-concat inv-h (ap h (T a)) (F (f a)))) ∙
        [b]
      [d] :
        pasting-vertical-coherence-square-maps f' g h f'' inv-g inv-h f' G inv-G (s a) ∙
        ( ap (inv-h ∘ h) (T a) ∙ ap inv-h (F (f a))) ＝
        inv-G (g (s a)) ∙ ap inv-h (ap f'' (H a) ∙ X a)
      [d] = assoc _ _ _ ∙ ap (inv-G (g (s a)) ∙_) [c]
      [f'] :
        inv-G (g (s a)) ∙
        ap inv-h (ap f'' (H a)) ＝
        ap f' (ap inv-g (H a)) ∙
        inv-G (s' a)
      [f'] =
        nat-coherence-square-maps f'' inv-g inv-h f' inv-G (H a)
      [e] :
        ap f' (is-retraction-map-inv-equiv e (s a)) ＝
        ap f' (ap inv-g (H a)) ∙
        inv-G (s' a) ∙
        ap inv-h (X a) ∙
        ap inv-h (inv (F (f a))) ∙
        inv (ap (inv-h ∘ h) (T a)) ∙
        is-retraction-map-inv-equiv j (f' (s a))
      [e] =
        [i] ∙
        ap
          ( _∙ is-retraction-map-inv-equiv j (f' (s a)))
          ( right-transpose-eq-concat _ _ _ [d] ∙
            ( ( ap
                ( _ ∙_)
                ( ( distributive-inv-concat
                    ( ap (inv-h ∘ h) (T a))
                    ( ap inv-h (F (f a)))) ∙
                  ( ap (_∙ _) (inv (ap-inv inv-h (F (f a))))))) ∙
              ( inv (assoc _ _ _)) ∙
              ( ap
                ( λ p → p ∙ _ ∙ _)
                ( ap (_ ∙_) (ap-concat inv-h (ap f'' (H a)) (X a)) ∙
                  inv (assoc _ _ _) ∙
                  ap (_∙ ap inv-h (X a)) [f']))))
      [f] :
        inv (ap (inv-h ∘ h) (T a)) ∙
        is-retraction-map-inv-equiv j (f' (s a)) ＝
        is-retraction-map-inv-equiv j (t (f a)) ∙ inv (T a)
      [f] =
        inv
          ( nat-htpy (is-retraction-map-inv-equiv j) (inv (T a)) ∙
            ap (_∙ is-retraction-map-inv-equiv j (f' (s a))) (ap-inv (inv-h ∘ h) (T a))) ∙
        ap
          ( is-retraction-map-inv-equiv j (t (f a)) ∙_)
          ( ap-id (inv (T a)))
      open import foundation.commuting-squares-of-identifications
      open import foundation.commuting-triangles-of-identifications
      [g] :
        T a ＝
        ap f' (inv-H a) ∙
        ( inv-G (s' a) ∙
          ap inv-h (X a)) ∙
        inv-F' (f a)
      [g] =
        left-transpose-eq-concat _ _ _
          ( inv-right-transpose-eq-concat _ _ _
            ( [e] ∙
            left-whisker-concat-coherence-square-identifications
              ( ap f' (ap inv-g (H a)) ∙ inv-G (s' a) ∙ ap inv-h (X a) ∙ ap inv-h (inv (F (f a))))
              ( is-retraction-map-inv-equiv j (t (f a)))
              ( inv (ap (inv-h ∘ h) (T a)))
              ( inv (T a))
              ( is-retraction-map-inv-equiv j (f' (s a)))
              ( [f]))) ∙
        ap
          ( _∙ (ap f' (ap inv-g (H a)) ∙ _ ∙ _ ∙ _ ∙ _))
          ( inv (ap-inv f' (is-retraction-map-inv-equiv e (s a)))) ∙
        inv (assoc _ _ _) ∙
        ap
          (_∙ is-retraction-map-inv-equiv j (t (f a)))
          ( inv (assoc _ _ _)) ∙
        assoc _ _ _ ∙
        ap
          ( _∙ inv-F' (f a))
          ( inv (assoc _ _ _) ∙
            ap
              ( _∙ ap inv-h (X a))
              ( right-whisker-concat-coherence-triangle-identifications'
                ( ap f' (inv-H a))
                ( ap f' (ap inv-g (H a)))
                ( ap f' (inv (is-retraction-map-inv-equiv e (s a))))
                ( inv-G (s' a))
                ( inv (ap-concat f' _ _))) ∙
            assoc _ _ _)

module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {P1 : UU l1} {P2 : UU l2} {P3 : UU l3} {P4 : UU l4}
  {Q1 : P1 → UU l5} {Q2 : P2 → UU l6} {Q3 : P3 → UU l7} {Q4 : P4 → UU l8}
  (g1 : P1 → P3) (f1 : P1 → P2) (f2 : P3 → P4) (g2 : P2 → P4)
  (g1' : {p : P1} → Q1 p → Q3 (g1 p))
  (e1' : (p : P1) → Q1 p ≃ Q2 (f1 p))
  (let f1' = λ {p} → map-equiv (e1' p))
  (let inv-f1' = λ {p} → map-inv-equiv (e1' p))
  (e2' : (p : P3) → Q3 p ≃ Q4 (f2 p))
  (let f2' = λ {p} → map-equiv (e2' p))
  (let inv-f2' = λ {p} → map-inv-equiv (e2' p))
  (g2' : {p : P2} → Q2 p → Q4 (g2 p))
  (s1 : (p : P1) → Q1 p) (s2 : (p : P2) → Q2 p) (s3 : (p : P3) → Q3 p)
  (s4 : (p : P4) → Q4 p)
  (G1 : (p : P1) → g1' (s1 p) ＝ s3 (g1 p))
  (F1 : (p : P1) → f1' (s1 p) ＝ s2 (f1 p))
  (F2 : (p : P3) → f2' (s3 p) ＝ s4 (f2 p))
  (G2 : (p : P2) → g2' (s2 p) ＝ s4 (g2 p))
  (H : coherence-square-maps g1 f1 f2 g2)
  (H' : square-over {Q4 = Q4} _ _ _ _ g1' f1' f2' g2' H)
  where

  opaque
    -- good luck if you ever need to unfold this...
    flop-section :
      section-square-over {Q4 = Q4}
        _ _ _ _ g1' f1' f2' g2'
        _ _ _ s4 G1 F1 F2 G2
        H H' →
      (p : P1) →
      G1 p ∙ invert-fiberwise-triangle s3 (s4 ∘ f2) e2' F2 (g1 p) ＝
      ap g1' (invert-fiberwise-triangle s1 (s2 ∘ f1) e1' F1 p) ∙
      vertical-inv-equiv-coherence-square-maps g1' (e1' p) (e2' (g1 p)) (tr Q4 (H p) ∘ g2') H' (s2 (f1 p)) ∙
      ap (inv-f2' ∘ tr Q4 (H p)) (G2 (f1 p)) ∙
      ap inv-f2' (apd s4 (H p))
    flop-section α p =
      [i] p ∙
      left-whisker-concat-coherence-triangle-identifications
        ( _)
        ( ap inv-f2' (ap (tr Q4 (H p)) (G2 (f1 p)) ∙ apd s4 (H p)))
        ( ap inv-f2' (apd s4 (H p)))
        ( ap (inv-f2' ∘ tr Q4 (H p)) (G2 (f1 p)))
        ( ap-concat inv-f2' _ (apd s4 (H p)) ∙
          ap (_∙ _) (inv (ap-comp inv-f2' (tr Q4 (H p)) (G2 (f1 p)))))
      where
      open import foundation.commuting-triangles-of-identifications
      [i] : (a : P1) →
            G1 a ∙
            invert-fiberwise-triangle s3 (s4 ∘ f2) (λ b → e2' b) F2 (g1 a)
            ＝
            ap g1'
            (invert-fiberwise-triangle s1 (s2 ∘ f1) (λ a₁ → e1' a₁) F1 a)
            ∙
            vertical-inv-equiv-coherence-square-maps g1' (e1' a) (e2' (g1 a))
              (tr Q4 (H a) ∘ g2') H' ((s2 ∘ f1) a)
              ∙
              ap (map-inv-equiv (e2' (g1 a)))
              (ap (tr Q4 (H a)) (G2 (f1 a)) ∙ apd s4 (H a))
      [i] =
        transpose-sq g1 s1 s3 (s2 ∘ f1) (s4 ∘ f2) g1' (λ {a} → tr Q4 (H a) ∘ g2')
          ( e1' _) (e2' _) G1 H' F2 F1
          (λ p → ap (tr Q4 (H p)) (G2 (f1 p)) ∙ apd s4 (H p))
          (inv-htpy-assoc-htpy _ _ _ ∙h α ∙h assoc-htpy _ _ _) ∙h
        inv-htpy-assoc-htpy _ _ _
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
  (let f∞n = λ n a → tr Q (C n a))
  (s : section-descent-data-sequential-colimit Q')
  (let s∞ = sect-family-sect-dd-sequential-colimit up-c' Q s)
  where

  private
    abstract
      γ :
        (n : ℕ) (a : family-sequential-diagram A n) →
        coherence-square-maps
          ( tr (Q ∘ f∞) (coherence-cocone-sequential-diagram c n a))
          ( f∞n n a)
          ( f∞n (succ-ℕ n) (map-sequential-diagram A n a))
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
  pr1 comp-over-diagram n =
    tr Q (inv (C n _)) ∘
    map-section-dependent-sequential-diagram _ _ s n ∘
    map-hom-sequential-diagram B f n
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

  module _
    (t : section-descent-data-sequential-colimit P')
    (let t∞ = sect-family-sect-dd-sequential-colimit up-c P t)
    (F :
      (n : ℕ) (a : family-sequential-diagram A n) →
      f∞n n a (map-section-dependent-sequential-diagram _ _ t n a) ＝
      map-section-dependent-sequential-diagram _ _ s n
        ( map-hom-sequential-diagram B f n a))
    (cubes :
      (n : ℕ) →
      section-square-over
        ( map-sequential-diagram A n)
        ( map-hom-sequential-diagram B f n)
        ( map-hom-sequential-diagram B f (succ-ℕ n))
        ( map-sequential-diagram B n)
        ( λ {a} → tr (Q ∘ f∞) (coherence-cocone-sequential-diagram c n a))
        ( λ {a} → f∞n n a)
        ( λ {a} → f∞n (succ-ℕ n) a)
        ( λ {b} → tr Q (coherence-cocone-sequential-diagram c' n b))
        ( map-section-dependent-sequential-diagram _ _ t n)
        ( map-section-dependent-sequential-diagram _ _ s n)
        ( map-section-dependent-sequential-diagram _ _ t (succ-ℕ n))
        ( map-section-dependent-sequential-diagram _ _ s (succ-ℕ n))
        ( naturality-map-section-dependent-sequential-diagram _ _ t n)
        ( F n)
        ( F (succ-ℕ n))
        ( naturality-map-section-dependent-sequential-diagram _ _ s n)
        ( naturality-map-hom-sequential-diagram B f n)
        ( λ {a} → γ n a))
    where

    lemma-2 : htpy-section-dependent-sequential-diagram t comp-over-diagram
    pr1 lemma-2 n =
      invert-fiberwise-triangle
        ( map-section-dependent-sequential-diagram _ _ t n)
        ( map-section-dependent-sequential-diagram _ _ s n ∘ map-hom-sequential-diagram B f n)
        ( λ a → equiv-tr Q (C n a))
        ( F n)
    pr2 lemma-2 n a =
      flop-section
        ( map-sequential-diagram A n)
        ( map-hom-sequential-diagram B f n)
        ( map-hom-sequential-diagram B f (succ-ℕ n))
        ( map-sequential-diagram B n)
        ( λ {a} → tr (Q ∘ f∞) (coherence-cocone-sequential-diagram c n a))
        ( λ a → equiv-tr Q (C n a))
        ( λ a → equiv-tr Q (C (succ-ℕ n) a))
        ( λ {b} → tr Q (coherence-cocone-sequential-diagram c' n b))
        ( map-section-dependent-sequential-diagram _ _ t n)
        ( map-section-dependent-sequential-diagram _ _ s n)
        ( map-section-dependent-sequential-diagram _ _ t (succ-ℕ n))
        ( map-section-dependent-sequential-diagram _ _ s (succ-ℕ n))
        ( naturality-map-section-dependent-sequential-diagram _ _ t n)
        ( F n)
        ( F (succ-ℕ n))
        ( naturality-map-section-dependent-sequential-diagram _ _ s n)
        ( naturality-map-hom-sequential-diagram B f n)
        ( λ {a} → γ n a)
        ( cubes n)
        ( a) ∙
      assoc _ _ _ ∙
      ap
        ( ap
          ( tr P (coherence-cocone-sequential-diagram c n a))
          ( pr1 lemma-2 n a) ∙
          γ-flip n a (map-section-dependent-sequential-diagram _ _ s n (map-hom-sequential-diagram B f n a)) ∙_)
        ( ( ap
            ( _∙
              ap
                ( tr Q (inv (C (succ-ℕ n) (map-sequential-diagram A n a))))
                ( apd
                  ( map-section-dependent-sequential-diagram _ _ s (succ-ℕ n))
                  ( naturality-map-hom-sequential-diagram B f n a)))
            ( ap-comp
              ( tr Q (inv (C (succ-ℕ n) (map-sequential-diagram A n a))))
              ( tr
                ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
                ( naturality-map-hom-sequential-diagram B f n a))
              ( naturality-map-section-dependent-sequential-diagram _ _ s n
                ( map-hom-sequential-diagram B f n a)))) ∙
          inv
          ( ( ap-concat
              ( tr Q (inv (C (succ-ℕ n) (map-sequential-diagram A n a))))
              ( _)
              ( _)))) ∙
      assoc _ _ _

    theorem : t∞ ~ s∞ ∘ f∞
    theorem =
      htpy-colimit-htpy-diagram-section up-c P t comp-over-diagram lemma-2 ∙h
      inv-htpy lemma-1
```

