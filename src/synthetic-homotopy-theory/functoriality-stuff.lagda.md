# Functoriality stuff

```agda
{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}

module synthetic-homotopy-theory.functoriality-stuff where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
-- open import foundation.binary-homotopies
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-identifications
open import foundation.commuting-triangles-of-maps
-- open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.families-of-equivalences
open import foundation.fiberwise-equivalence-induction
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
open import foundation.transposition-identifications-along-equivalences
```

</details>

## Theorem

```agda
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

  section-descent-data-section-family-cocone-sequential-colimit :
    ((x : X) → P x) →
    section-descent-data-sequential-colimit
      ( descent-data-family-cocone-sequential-diagram c P)
  section-descent-data-section-family-cocone-sequential-colimit =
    dependent-cocone-map-sequential-diagram c P
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

  -- the rest of the proof relies on the implementation of
  -- map-eq-transpose-equiv', which is probably not the best idea
  invert-fiberwise-triangle : (a : A) → s a ＝ map-inv-equiv (e a) (t a)
  invert-fiberwise-triangle a = map-eq-transpose-equiv' (e a) (H a)

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
  (X : (a : A) → f'' (s' a) ＝ t' (f a))
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
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3}
  (f : A → B) (s : (b : B) → C b)
  where

  apd-left :
    {x y : A} (p : x ＝ y) →
    apd (s ∘ f) p ＝ inv (substitution-law-tr C f p) ∙ apd s (ap f p)
  apd-left refl = refl

  apd-left' :
    {x y : A} (p : x ＝ y) →
    substitution-law-tr C f p ∙ apd (s ∘ f) p ＝ apd s (ap f p)
  apd-left' refl = refl

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (s : (a : A) → B a) (f : {a : A} → B a → C a)
  where

  apd-right :
    {x y : A} (p : x ＝ y) →
    apd (f ∘ s) p ＝ inv (preserves-tr (λ a → f {a}) p (s x)) ∙ ap f (apd s p)
  apd-right refl = refl
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (s : (a : A) → B a)
  where

  apd-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    ap (tr B q) (apd s p) ∙ apd s q ＝ inv (tr-concat p q (s x)) ∙ apd s (p ∙ q)
  apd-concat refl q = refl

  apd-concat' :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) →
    apd s (p ∙ q) ＝ tr-concat p q (s x) ∙ ap (tr B q) (apd s p) ∙ apd s q
  apd-concat' refl q = refl
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (s : (a : A) → B a)
  where

  apd-apd :
    {x y : A} (p q : x ＝ y) (α : p ＝ q) →
    ap (λ r → tr B r (s x)) (inv α) ∙ apd s p ＝ apd s q
  apd-apd p q refl = refl

  apd-apd' :
    {x y : A} (p q : x ＝ y) (α : p ＝ q) →
    apd s p ＝ ap (λ r → tr B r (s x)) α ∙ apd s q
  apd-apd' p q refl = refl
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g : (a : A) → B a} (H : f ~ g)
  where

  inv-dep-nat-htpy :
    {x y : A} (p : x ＝ y) →
    apd f p ∙ H y ＝
    ap (tr B p) (H x) ∙ apd g p
  inv-dep-nat-htpy {x = x} {y = y} p =
    map-inv-compute-dependent-identification-eq-value f g p (H x) (H y)
      ( apd H p)
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2}
  {P : A → UU l3} {Q : B → UU l4}
  (f : A → B) (sA : (a : A) → P a) (sB : (b : B) → Q b)
  (f' : {a : A} → P a → Q (f a))
  where

  convenient-square : UU (l1 ⊔ l4)
  convenient-square = sB ∘ f ~ f' ∘ sA

  convenient-square' : UU (l1 ⊔ l4)
  convenient-square' = f' ∘ sA ~ sB ∘ f

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {P : C → UU l5} {Q : D → UU l6}
  (f : A → B) (hA : A → C) (hB : B → D) (g : C → D)
  (sA : (c : C) → P c) (sB : (d : D) → Q d) (f' : {c : C} → P c → Q (g c))
  where

  pasting-squares :
    (H : coherence-square-maps hA f g hB) →
    convenient-square g sA sB f' →
    (a : A) → tr Q (H a) (sB (hB (f a))) ＝ f' (sA (hA a))
  pasting-squares H K a =
    apd sB (H a) ∙ K (hA a)

  pasting-squares' :
    (H : coherence-square-maps' hA f g hB) →
    convenient-square' g sA sB f' →
    (a : A) → tr Q (H a) (f' (sA (hA a))) ＝ sB (hB (f a))
  pasting-squares' H K a =
    ap (tr Q (H a)) (K (hA a)) ∙ apd sB (H a)
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  {A' : UU l4} {B' : UU l5} {C' : UU l6}
  (f : A → C) (g : B → C) (h : A → B)
  (f' : A' → C') (g' : B' → C') (h' : A' → B')
  (hA : A → A') (hB : B → B') (hC : C → C')
  (left : hC ∘ f ~ f' ∘ hA)
  (right : hC ∘ g ~ g' ∘ hB)
  (back : h' ∘ hA ~ hB ∘ h)
  (bottom : f ~ g ∘ h)
  (top : f' ~ g' ∘ h')
  where

  convenient-prism : UU (l1 ⊔ l6)
  convenient-prism =
    left ∙h (top ·r hA) ∙h (g' ·l back) ~
    (hC ·l bottom) ∙h (right ·r h)
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  {P : A → UU l4} {Q : B → UU l5} {R : C → UU l6}
  (f : A → C) (g : B → C) (h : A → B)
  (f' : {a : A} → P a → R (f a))
  (g' : {b : B} → Q b → R (g b))
  (h' : {a : A} → P a → Q (h a))
  (sA : (a : A) → P a) (sB : (b : B) → Q b) (sC : (c : C) → R c)
  (left : sC ∘ f ~ f' ∘ sA)
  (right : sC ∘ g ~ g' ∘ sB)
  (back : h' ∘ sA ~ sB ∘ h)
  (bottom : f ~ g ∘ h)
  (top : htpy-over R bottom f' (g' ∘ h'))
  where

  fiberwise-prism : UU (l1 ⊔ l6)
  fiberwise-prism =
    (a : A) →
    ( ap (tr R (bottom a)) (left a) ∙
      top (sA a) ∙
      ap g' (back a)) ＝
    ( apd sC (bottom a) ∙
      right (h a))
```

TODO: this should be parameterized by a fiberwise map, not equivalence

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : sequential-diagram l1} {X : UU l2}
  {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {B : sequential-diagram l3} {Y : UU l4}
  (c' : cocone-sequential-diagram B Y)
  (f : hom-sequential-diagram A B)
  (let f∞ = map-sequential-colimit-hom-sequential-diagram up-c c' f)
  (let
    C = htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f)
  (P : X → UU l5)
  (let P' = descent-data-family-cocone-sequential-diagram c P)
  (Q : Y → UU l6)
  (let Q' = descent-data-family-cocone-sequential-diagram c' Q)
  (e : fam-equiv P (Q ∘ f∞))
  where

  equiv-over-diagram-equiv-over-colimit :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-descent-data-sequential-colimit P' n a ≃
    family-descent-data-sequential-colimit Q' n
      ( map-hom-sequential-diagram B f n a)
  equiv-over-diagram-equiv-over-colimit n a =
    equiv-tr Q (C n a) ∘e
    e (map-cocone-sequential-diagram c n a)

  map-over-diagram-equiv-over-colimit :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-descent-data-sequential-colimit P' n a →
    family-descent-data-sequential-colimit Q' n
      ( map-hom-sequential-diagram B f n a)
  map-over-diagram-equiv-over-colimit n a =
    map-equiv (equiv-over-diagram-equiv-over-colimit n a)

  opaque
    γ-base' :
      (n : ℕ) (a : family-sequential-diagram A n) →
      coherence-square-maps
        ( tr Q (ap f∞ (coherence-cocone-sequential-diagram c n a)))
        ( tr Q (C n a))
        ( tr Q (C (succ-ℕ n) (map-sequential-diagram A n a)))
        ( ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a)) ∘
          ( tr Q
            ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a))))
    γ-base' n a q =
      inv
        ( substitution-law-tr Q
          ( map-cocone-sequential-diagram c' (succ-ℕ n))
          ( naturality-map-hom-sequential-diagram B f n a)) ∙
      inv
        ( tr-concat
          ( coherence-cocone-sequential-diagram c' n
            ( map-hom-sequential-diagram B f n a))
          ( ap
            ( map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a))
          ( tr Q (C n a) q)) ∙
      inv
        ( tr-concat (C n a) _ q) ∙
      ap
        ( λ p → tr Q p q)
        ( inv
          ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f n a)) ∙
      tr-concat
        ( ap f∞ (coherence-cocone-sequential-diagram c n a))
        ( C (succ-ℕ n) (map-sequential-diagram A n a))
        ( q)

  opaque
    γ' :
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
    γ' n a q =
      γ-base' n a q ∙
      ap
        ( tr Q (C (succ-ℕ n) (map-sequential-diagram A n a)))
        ( substitution-law-tr Q f∞ (coherence-cocone-sequential-diagram c n a))

  opaque
    square-over-diagram-square-over-colimit :
      (n : ℕ) (a : family-sequential-diagram A n) →
      coherence-square-maps
        ( tr P (coherence-cocone-sequential-diagram c n a))
        ( map-over-diagram-equiv-over-colimit n a)
        ( map-over-diagram-equiv-over-colimit
          ( succ-ℕ n)
          ( map-sequential-diagram A n a))
        ( ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a)) ∘
          ( tr Q
            ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a))))
    square-over-diagram-square-over-colimit n a =
      pasting-vertical-coherence-square-maps
        ( tr P (coherence-cocone-sequential-diagram c n a))
        ( map-fam-equiv e (map-cocone-sequential-diagram c n a))
        ( map-fam-equiv e (map-cocone-sequential-diagram c (succ-ℕ n) (map-sequential-diagram A n a)))
        ( tr (Q ∘ f∞) (coherence-cocone-sequential-diagram c n a))
        ( tr Q (C n a))
        ( tr Q (C (succ-ℕ n) (map-sequential-diagram A n a)))
        ( ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a)) ∘
          ( tr Q
            ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a))))
        ( inv-htpy
          ( preserves-tr
            ( map-fam-equiv e)
            ( coherence-cocone-sequential-diagram c n a)))
        ( γ' n a)

module _
  {l1 l2 l3 l4 l5 : Level}
  {A : sequential-diagram l1} {X : UU l2}
  {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {B : sequential-diagram l3} {Y : UU l4}
  (c' : cocone-sequential-diagram B Y)
  (f : hom-sequential-diagram A B)
  (let f∞ = map-sequential-colimit-hom-sequential-diagram up-c c' f)
  (Q : Y → UU l5)
  where

  opaque
    unfolding square-over-diagram-square-over-colimit

    compute-square-over-diagram-id :
      (n : ℕ) (a : family-sequential-diagram A n) →
      square-over-diagram-square-over-colimit up-c c' f (Q ∘ f∞) Q id-fam-equiv n a ~
      γ' up-c c' f (Q ∘ f∞) Q id-fam-equiv n a
    compute-square-over-diagram-id n a q =
      ap
        ( λ r →
          γ' up-c c' f (Q ∘ f∞) Q id-fam-equiv n a q ∙
          ap (tr Q _) (inv r))
        ( compute-preserves-tr-id (coherence-cocone-sequential-diagram c n a) q) ∙
      right-unit
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where
  open import foundation.dependent-identifications

  compute-inv-dependent-identification-inv :
    {x y : A} (p : x ＝ y) {x' : B x} {y' : B y}
    (q : y' ＝ tr B p x') →
    inv-dependent-identification B p (inv q) ＝
    map-eq-transpose-equiv-inv' (equiv-tr B p) q
  compute-inv-dependent-identification-inv refl q = inv-inv q ∙ inv (right-unit ∙ ap-id q)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (e : A ≃ B)
  where

  compute-eq-transpose-equiv-inv-concat' :
    {x : A} {b c : B} (p : b ＝ c) (q : c ＝ map-equiv e x) →
    map-eq-transpose-equiv-inv' e (p ∙ q) ＝
    ap (map-inv-equiv e) p ∙ map-eq-transpose-equiv-inv' e q
  compute-eq-transpose-equiv-inv-concat' refl q = refl
```

```agda
module _
  {l1 l2 : Level}
  {A : UU l1}
  {P : A → UU l2}
  where
  open import foundation.dependent-identifications

  compute-lemma'' :
    {x y : A} (p : x ＝ y) →
    {x' : P x} {y' z' : P y}
    (K : dependent-identification P p x' y')
    (H : y' ＝ z') →
    inv-dependent-identification P p (K ∙ H) ＝
    ap
      ( tr P (inv p))
      ( inv H) ∙
    inv-dependent-identification P p K
  compute-lemma'' refl K refl = ap inv right-unit

module _
  {l1 l2 l5 l6 : Level}
  {A : UU l1} {B : UU l2}
  {P : A → UU l5} {Q : UU l6} -- {Q : B → UU l6}
  where
  open import foundation.dependent-identifications

  compute-lemma :
    {x y : A} (p : x ＝ y) →
    {u v : Q} (H : u ＝ v) →
    (f : Q → P y)
    {x' : P x} (K : dependent-identification P p x' (f u)) →
    inv-dependent-identification P p (K ∙ ap f H) ＝
    ap
      ( tr P (inv p) ∘ f)
      ( inv H) ∙
    inv-dependent-identification P p K
  compute-lemma p H f K =
    compute-lemma'' p K (ap f H) ∙
    ap
      ( _∙ inv-dependent-identification P p K)
      ( ap
          ( ap (tr P (inv p)))
          ( inv (ap-inv f H)) ∙
        inv (ap-comp (tr P (inv p)) f (inv H)))

  compute-lemma' :
    {x y : A} (p : x ＝ y) →
    {u v : Q} (H : u ＝ v) →
    (f : Q → P y) →
    {x' : P x} (K : f v ＝ tr P p x') →
    inv-dependent-identification P p (inv (ap f H ∙ K)) ＝
    ap
      ( tr P (inv p) ∘ f)
      ( H) ∙
    inv-dependent-identification P p (inv K)
  compute-lemma' refl refl f K = refl
    -- ap
    --   ( inv-dependent-identification P p)
    --   ( distributive-inv-concat (ap f H) K ∙ ap (inv K ∙_) (inv (ap-inv f H))) ∙
    -- compute-lemma p (inv H) f (inv K) ∙
    -- ap
    --   ( λ r → ap (tr P (inv p) ∘ f) r ∙ inv-dependent-identification P p (inv K))
    --   ( inv-inv H)
```

```agda

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : A → UU l2}
  {X : UU l3} {Y : X → UU l4}
  where

  compute-left-whisker-transpose :
    {s : A → X} (s' : {a : A} → B a → Y (s a))
    {x y : A} (p : y ＝ x)
    {x' : B x} {y' : B y} (p' : x' ＝ tr B p y') →
    left-whisk-dependent-identification {B' = Y} s' (inv p)
      ( map-eq-transpose-equiv-inv' (equiv-tr B p) p') ＝
    ap
      ( λ r → tr Y r (s' x'))
      ( ap-inv s p) ∙
    inv
      ( map-eq-transpose-equiv
        ( equiv-tr Y (ap s p))
        ( left-whisk-dependent-identification {B' = Y} s' p
          ( inv p')))
  compute-left-whisker-transpose s' refl refl =
    inv (ap inv (compute-refl-eq-transpose-equiv id-equiv))

open import synthetic-homotopy-theory.zigzags-sequential-diagrams
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : sequential-diagram l1} {X : UU l2}
  {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {B : sequential-diagram l3} {Y : UU l4}
  (c' : cocone-sequential-diagram B Y)
  (z : zigzag-sequential-diagram A B)
  (let f = hom-diagram-zigzag-sequential-diagram z)
  (let f∞ = map-sequential-colimit-hom-sequential-diagram up-c c' f)
  (let
    C = htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f)
  (P : X → UU l5)
  (let P' = descent-data-family-cocone-sequential-diagram c P)
  (Q : Y → UU l5)
  (let Q' = descent-data-family-cocone-sequential-diagram c' Q)
  (e : fam-equiv P (Q ∘ f∞))
  where

  inv-map-over-diagram-equiv-zigzag' :
    (n : ℕ) (a : family-sequential-diagram A n) →
    family-descent-data-sequential-colimit Q' n
      ( map-zigzag-sequential-diagram z n a) →
    family-descent-data-sequential-colimit P' n a
  inv-map-over-diagram-equiv-zigzag' n a =
    map-inv-fam-equiv e
      ( map-cocone-sequential-diagram c n a) ∘
    tr Q (inv (C n a))


  inv-map-over-diagram-equiv-zigzag :
    (n : ℕ) (b : family-sequential-diagram B n) →
    family-descent-data-sequential-colimit Q' n b →
    family-descent-data-sequential-colimit P' (succ-ℕ n)
      ( inv-map-zigzag-sequential-diagram z n b)
  inv-map-over-diagram-equiv-zigzag n b =
    inv-map-over-diagram-equiv-zigzag' (succ-ℕ n)
      ( inv-map-zigzag-sequential-diagram z n b) ∘
    tr
      ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
      ( lower-triangle-zigzag-sequential-diagram z n b) ∘
    tr Q
      ( coherence-cocone-sequential-diagram c' n b)

  opaque
    inv-upper-triangle-over' :
      (n : ℕ) (a : family-sequential-diagram A n) →
      tr
        ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
        ( lower-triangle-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a)) ∘
      tr
        ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
        ( inv (naturality-map-hom-diagram-zigzag-sequential-diagram z n a)) ∘
      map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n) (map-sequential-diagram A n a) ~
      map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n) (inv-map-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a)) ∘
      tr
        ( family-descent-data-sequential-colimit P' (succ-ℕ n))
        ( upper-triangle-zigzag-sequential-diagram z n a)
    inv-upper-triangle-over' n a p =
      inv
        ( ( preserves-tr
            ( map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n))
            ( upper-triangle-zigzag-sequential-diagram z n a)
            ( p)) ∙
        ( inv
          ( substitution-law-tr
            ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
            ( map-zigzag-sequential-diagram z (succ-ℕ n))
            ( upper-triangle-zigzag-sequential-diagram z n a))) ∙
        ( ap
          ( λ r →
            tr
              ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
              ( r)
              ( map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n)
                ( map-sequential-diagram A n a)
                ( p)))
          ( inv
            ( ap
              ( _∙ lower-triangle-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a))
              ( distributive-inv-concat
                ( lower-triangle-zigzag-sequential-diagram z n
                  ( map-zigzag-sequential-diagram z n a))
                ( ap
                  ( map-zigzag-sequential-diagram z (succ-ℕ n))
                  ( inv (upper-triangle-zigzag-sequential-diagram z n a)))) ∙
            assoc _ _ _ ∙
            ap
              ( inv (ap (map-zigzag-sequential-diagram z (succ-ℕ n)) (inv (upper-triangle-zigzag-sequential-diagram z n a))) ∙_)
              ( left-inv (lower-triangle-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a))) ∙
            right-unit ∙
            ap inv (ap-inv _ _) ∙
            inv-inv _))) ∙
        ( tr-concat
          ( inv (naturality-map-hom-diagram-zigzag-sequential-diagram z n a))
          ( lower-triangle-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a))
          ( map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n) (map-sequential-diagram A n a) p)))
      -- inv
      --   ( tr-concat
      --     ( inv (naturality-map-hom-diagram-zigzag-sequential-diagram z n a))
      --     ( lower-triangle-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a))
      --     ( map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n) (map-sequential-diagram A n a) p)) ∙
      -- {!preserves-tr
      --   ( map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n))
      --   ( )!}

  opaque
    upper-triangle-over' :
      (n : ℕ) (a : family-sequential-diagram A n) →
      map-inv-fam-equiv e _ ∘
      tr Q (inv (C (succ-ℕ n) _)) ∘
      tr
        ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
        ( lower-triangle-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a)) ∘
      tr
        ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
        ( inv (naturality-map-hom-diagram-zigzag-sequential-diagram z n a)) ∘
      map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n) (map-sequential-diagram A n a) ~
      tr
        ( family-descent-data-sequential-colimit P' (succ-ℕ n))
        ( upper-triangle-zigzag-sequential-diagram z n a)
    upper-triangle-over' n a p =
      map-eq-transpose-equiv-inv'
        ( e _)
        ( map-eq-transpose-equiv-inv'
          ( equiv-tr Q (C (succ-ℕ n) _))
          ( inv-upper-triangle-over' n a p))

  inv-upper-triangle-over :
    (n : ℕ) (a : family-sequential-diagram A n) →
    coherence-square-maps
      ( map-family-descent-data-sequential-colimit P' n a)
      ( map-over-diagram-equiv-over-colimit up-c c' f P Q e n a)
      ( tr
        ( family-descent-data-sequential-colimit P' (succ-ℕ n))
        ( upper-triangle-zigzag-sequential-diagram z n a))
      ( inv-map-over-diagram-equiv-zigzag n (map-zigzag-sequential-diagram z n a))
  inv-upper-triangle-over n a p =
    ap
      ( inv-map-over-diagram-equiv-zigzag' (succ-ℕ n) _ ∘
        tr
          ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
          ( lower-triangle-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a)))
      ( inv
        ( is-retraction-map-inv-equiv
          ( equiv-tr
            ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
            ( naturality-map-hom-diagram-zigzag-sequential-diagram z n a))
          ( _)) ∙
        ap
          ( tr
            ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
            ( inv
              ( naturality-map-hom-diagram-zigzag-sequential-diagram z n a)))
          ( square-over-diagram-square-over-colimit up-c c' f P Q e n a p)) ∙
    upper-triangle-over' n a (map-family-descent-data-sequential-colimit P' n a p)

  upper-triangle-over :
    (n : ℕ) →
    htpy-over
      ( family-descent-data-sequential-colimit P' (succ-ℕ n))
      ( upper-triangle-zigzag-sequential-diagram z n)
      ( map-family-descent-data-sequential-colimit P' n _)
      ( inv-map-over-diagram-equiv-zigzag n _ ∘
        map-over-diagram-equiv-over-colimit up-c c' f P Q e n _)
  upper-triangle-over n {a} p =
    inv (inv-upper-triangle-over n a p)

  opaque
    lower-triangle-over' :
      (n : ℕ) (a : family-sequential-diagram A n)
      (q :
        family-descent-data-sequential-colimit Q' n
          ( map-zigzag-sequential-diagram z n a)) →
      q ＝
      map-over-diagram-equiv-over-colimit up-c c' f P Q e n a
        ( inv-map-over-diagram-equiv-zigzag' n a q)
    lower-triangle-over' n a q =
      inv
        ( is-section-map-inv-equiv
          ( equiv-tr Q (C n a))
          ( q)) ∙
      ap
        ( tr Q (C n a))
        ( inv
          ( is-section-map-inv-equiv
            ( e (map-cocone-sequential-diagram c n a))
            ( tr Q (inv (C n a)) q)))

  lower-triangle-over :
    (n : ℕ) →
    htpy-over
      ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
      ( lower-triangle-zigzag-sequential-diagram z n)
      ( map-family-descent-data-sequential-colimit Q' n _)
      ( map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n) _ ∘
        inv-map-over-diagram-equiv-zigzag n _)
  lower-triangle-over n {b} q =
    -- this could change to alternatives
    -- map-inv-eq-transpose-equiv-inv doesn't compute well
    lower-triangle-over'
      ( succ-ℕ n)
      ( inv-map-zigzag-sequential-diagram z n b)
      ( tr
         ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
         ( lower-triangle-zigzag-sequential-diagram z n b)
         ( map-family-descent-data-sequential-colimit Q' n b q))

  trivial-pasting :
    (n : ℕ) →
    htpy-over
      ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
      ( naturality-map-hom-diagram-zigzag-sequential-diagram z n)
      ( tr
        ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
        ( inv (naturality-map-hom-diagram-zigzag-sequential-diagram z n _)) ∘
        map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n) _)
      ( map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n) _)
  trivial-pasting n =
    concat-htpy-over
      ( lower-triangle-zigzag-sequential-diagram z n ·r
        ( map-zigzag-sequential-diagram z n))
      ( ( map-zigzag-sequential-diagram z (succ-ℕ n)) ·l
        ( inv-htpy (upper-triangle-zigzag-sequential-diagram z n)))
      ( λ p →
        lower-triangle-over' (succ-ℕ n) _
          ( tr
            ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
            ( lower-triangle-zigzag-sequential-diagram z n _)
            ( tr
              ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
              ( inv (naturality-map-hom-diagram-zigzag-sequential-diagram z n _))
              ( map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n)
                ( map-sequential-diagram A n _)
                ( p)))))
      ( left-whisk-htpy-over
        ( inv-htpy (upper-triangle-zigzag-sequential-diagram z n))
        ( λ p →
          map-eq-transpose-equiv-inv'
            ( equiv-tr
              ( family-descent-data-sequential-colimit P' (succ-ℕ n))
              ( upper-triangle-zigzag-sequential-diagram z n _))
            ( upper-triangle-over' n _ p))
        ( map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n) _))

  abstract
    open import foundation.dependent-identifications
    is-trivial-trivial-pasting :
      (n : ℕ) (a : family-sequential-diagram A n) →
      trivial-pasting n {a} ~
      is-section-map-inv-equiv
        ( equiv-tr
          ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
          ( naturality-map-hom-diagram-zigzag-sequential-diagram z n a)) ·r
        map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n) (map-sequential-diagram A n a)
    is-trivial-trivial-pasting n a p =
      ap
        ( λ K' →
          concat-dependent-identification _ _ _
          ( lower-triangle-over' (succ-ℕ n) _ _)
          ( K'))
        ( compute-left-whisker-transpose
          ( λ {a} → map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n) a)
          ( upper-triangle-zigzag-sequential-diagram z n a)
          ( upper-triangle-over' n a p)) ∙
      {!!}
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (e : A ≃ B)
  where

  inv-coherence-map-inv-is-equiv :
    (a : A) →
    ap (map-equiv e) (inv (is-retraction-map-inv-equiv e a)) ＝
    inv (is-section-map-inv-equiv e (map-equiv e a))
  inv-coherence-map-inv-is-equiv a =
    ap-inv (map-equiv e) (is-retraction-map-inv-equiv e a) ∙
    ap inv (inv (coherence-map-inv-equiv e a))

  left-inv-is-retraction-map-inv-equiv :
    (a : A) →
    inv (is-section-map-inv-equiv e (map-equiv e a)) ∙
    ap (map-equiv e) (is-retraction-map-inv-equiv e a) ＝
    refl
  left-inv-is-retraction-map-inv-equiv a =
    ap
      ( inv (is-section-map-inv-equiv e (map-equiv e a)) ∙_)
      ( inv (coherence-map-inv-equiv e a)) ∙
    left-inv (is-section-map-inv-equiv e (map-equiv e a))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (e : A ≃ B)
  where
  concat-inv-coherence-map-inv-is-equiv :
    {x : A} {y : B} (p : map-equiv e x ＝ y) →
    ap (map-equiv e) (inv (is-retraction-map-inv-equiv e x) ∙ ap (map-inv-equiv e) p) ＝
    p ∙ inv (is-section-map-inv-equiv e y)
  concat-inv-coherence-map-inv-is-equiv refl =
    ap (ap (map-equiv e)) right-unit ∙ inv-coherence-map-inv-is-equiv e _

module _
  {l1 l2 l3 l4 l5 : Level}
  {A : sequential-diagram l1} {X : UU l2}
  {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {B : sequential-diagram l3} {Y : UU l4}
  (c' : cocone-sequential-diagram B Y)
  (z : zigzag-sequential-diagram A B)
  (let f = hom-diagram-zigzag-sequential-diagram z)
  (let g = inv-hom-diagram-zigzag-sequential-diagram z)
  (let f∞ = map-sequential-colimit-hom-sequential-diagram up-c c' f)
  (let
    C = htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f)
  (Q : Y → UU l5)
  (let Q' = descent-data-family-cocone-sequential-diagram c' Q)
  (let P = Q ∘ f∞)
  (let P' = descent-data-family-cocone-sequential-diagram c P)
  where

  open import foundation.dependent-identifications

  opaque
    -- TODO: Maybe this goes through for general equivalences immediately?
    -- I haven't tried yet
    compute-square-over-zigzag-square-over-colimit-id :
      (n : ℕ) (a : family-sequential-diagram A n) →
      pasting-triangles-over
        ( map-sequential-diagram A n)
        ( map-hom-sequential-diagram B f n)
        ( map-hom-sequential-diagram B f (succ-ℕ n))
        ( map-sequential-diagram B n)
        ( map-family-descent-data-sequential-colimit P' n _)
        ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv n _)
        ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv (succ-ℕ n) _)
        ( map-family-descent-data-sequential-colimit Q' n _)
        ( map-hom-sequential-diagram _ g n)
        ( inv-map-over-diagram-equiv-zigzag up-c c' z P Q id-fam-equiv n _)
        ( inv-htpy (upper-triangle-zigzag-sequential-diagram z n))
        ( lower-triangle-zigzag-sequential-diagram z n)
        ( inv-htpy-over
          ( family-descent-data-sequential-colimit P' (succ-ℕ n))
          ( upper-triangle-zigzag-sequential-diagram z n)
          _ _
          ( upper-triangle-over up-c c' z P Q id-fam-equiv n))
        ( lower-triangle-over up-c c' z P Q id-fam-equiv n)
        { a} ~
      square-over-diagram-square-over-colimit up-c c' f P Q id-fam-equiv n a
    compute-square-over-zigzag-square-over-colimit-id n a p =
      compute-concat-dependent-identification
        ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
        _ _ _ _ ∙
      ( ap
        ( ( ( tr-concat
              ( lower-triangle-zigzag-sequential-diagram z n _)
              ( ap (map-zigzag-sequential-diagram z (succ-ℕ n)) (inv (upper-triangle-zigzag-sequential-diagram z n a)))
              ( _)) ∙
            ( ap
              ( tr (family-descent-data-sequential-colimit Q' (succ-ℕ n)) _)
              ( lower-triangle-over up-c c' z (Q ∘ f∞) Q id-fam-equiv n _))) ∙_)
        ( ( compute-left-whisk-dependent-identification
            ( map-over-diagram-equiv-over-colimit up-c c' (hom-diagram-zigzag-sequential-diagram z) (Q ∘ f∞) Q id-fam-equiv (succ-ℕ n) _)
            ( inv (upper-triangle-zigzag-sequential-diagram z n a))
            ( _)) ∙
          ap
            ( λ r →
              substitution-law-tr
                ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                ( map-zigzag-sequential-diagram z (succ-ℕ n))
                ( inv (upper-triangle-zigzag-sequential-diagram z n a)) ∙
              inv
                ( preserves-tr
                  ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv (succ-ℕ n))
                  ( inv (upper-triangle-zigzag-sequential-diagram z n a))
                  ( _)) ∙
              ap
                ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv (succ-ℕ n) (map-sequential-diagram A n a))
                ( r))
            ( ( compute-inv-dependent-identification-inv
                ( upper-triangle-zigzag-sequential-diagram z n a)
                ( inv-upper-triangle-over up-c c' z (Q ∘ f∞) Q id-fam-equiv n a p)) ∙
              ( compute-eq-transpose-equiv-inv-concat'
                ( equiv-tr
                  ( family-descent-data-sequential-colimit P' (succ-ℕ n))
                  ( upper-triangle-zigzag-sequential-diagram z n a))
                ( _)
                ( _))))) ∙
      inv (assoc _ _ _) ∙
      ap
        ( ( tr-concat
            ( lower-triangle-zigzag-sequential-diagram z n _)
            ( ap (map-zigzag-sequential-diagram z (succ-ℕ n)) (inv (upper-triangle-zigzag-sequential-diagram z n a)))
            ( map-family-descent-data-sequential-colimit Q' n
              ( map-zigzag-sequential-diagram z n a)
              ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv n a p)) ∙
            ap
              ( tr
                ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                ( ap _ (inv (upper-triangle-zigzag-sequential-diagram z n a))))
              ( lower-triangle-over up-c c' z P Q id-fam-equiv n _) ∙
            ( substitution-law-tr
              ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
              ( map-zigzag-sequential-diagram z (succ-ℕ n))
              ( inv (upper-triangle-zigzag-sequential-diagram z n a)) ∙
              inv
                ( preserves-tr
                  ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv (succ-ℕ n))
                  ( inv (upper-triangle-zigzag-sequential-diagram z n a))
                  ( _)))) ∙_)
        ( ap-concat
          ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv (succ-ℕ n) (map-sequential-diagram A n a))
          ( _)
          ( _) ∙
          ap
            (_∙
              ap
                ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv (succ-ℕ n) (map-sequential-diagram A n a))
                ( map-eq-transpose-equiv-inv'
                  ( equiv-tr
                    ( family-descent-data-sequential-colimit P' (succ-ℕ n))
                    ( upper-triangle-zigzag-sequential-diagram z n a))
                  ( upper-triangle-over' up-c c' z P Q id-fam-equiv n a _)))
            ( inv
              ( ap-comp
                ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv (succ-ℕ n) (map-sequential-diagram A n a))
                ( tr
                  ( family-descent-data-sequential-colimit P' (succ-ℕ n))
                  ( inv (upper-triangle-zigzag-sequential-diagram z n a)))
                ( _)) ∙
              inv
                ( ap-comp
                  ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv (succ-ℕ n) (map-sequential-diagram A n a) ∘
                    tr (family-descent-data-sequential-colimit P' (succ-ℕ n)) (inv (upper-triangle-zigzag-sequential-diagram z n a)))
                  ( tr Q
                      ( inv (C (succ-ℕ n) _)) ∘
                    tr
                      ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                      ( lower-triangle-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a)))
                  ( _)))) ∙
      inv (assoc _ _ _) ∙
      ap
        ( _∙
          ap
            ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv (succ-ℕ n) (map-sequential-diagram A n a))
            ( map-eq-transpose-equiv-inv'
              ( equiv-tr
                ( family-descent-data-sequential-colimit P' (succ-ℕ n))
                ( upper-triangle-zigzag-sequential-diagram z n a))
              ( upper-triangle-over' up-c c' z P Q id-fam-equiv n a _)))
        ( nat-htpy
            ( λ (q : family-descent-data-sequential-colimit Q' (succ-ℕ n) (map-sequential-diagram B n (map-zigzag-sequential-diagram z n a))) →
              tr-concat
                ( lower-triangle-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a))
                ( ap (map-zigzag-sequential-diagram z (succ-ℕ n)) (inv (upper-triangle-zigzag-sequential-diagram z n a)))
                ( q) ∙
              ap
                ( tr
                  ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                  ( ap (map-zigzag-sequential-diagram z (succ-ℕ n)) (inv (upper-triangle-zigzag-sequential-diagram z n a))))
                ( lower-triangle-over' up-c c' z P Q id-fam-equiv (succ-ℕ n) _
                  ( tr
                    ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                    ( lower-triangle-zigzag-sequential-diagram z n
                      ( map-zigzag-sequential-diagram z n a))
                    ( q))) ∙
              ( substitution-law-tr
                ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                ( map-zigzag-sequential-diagram z (succ-ℕ n))
                ( inv (upper-triangle-zigzag-sequential-diagram z n a)) ∙
                inv
                  ( preserves-tr
                    ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv (succ-ℕ n))
                    ( inv (upper-triangle-zigzag-sequential-diagram z n a))
                    ( inv-map-over-diagram-equiv-zigzag' up-c c' z P Q id-fam-equiv (succ-ℕ n)
                      ( inv-map-zigzag-sequential-diagram z n
                        ( map-zigzag-sequential-diagram z n a))
                      ( tr
                        ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                        ( lower-triangle-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a))
                        ( q))))))
            ( _) ∙
            ap
              ( _∙
                ( tr-concat _ _ _ ∙
                  ap
                    ( tr
                      ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                      ( ap
                        ( map-zigzag-sequential-diagram z (succ-ℕ n))
                        ( inv (upper-triangle-zigzag-sequential-diagram z n a))))
                    ( lower-triangle-over' up-c c' z P Q id-fam-equiv (succ-ℕ n) _ _)∙
                  ( substitution-law-tr
                    ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                    ( map-zigzag-sequential-diagram z (succ-ℕ n))
                    ( inv (upper-triangle-zigzag-sequential-diagram z n a)) ∙
                    inv
                      ( preserves-tr
                        ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv (succ-ℕ n))
                        ( inv (upper-triangle-zigzag-sequential-diagram z n a))
                        ( inv-map-over-diagram-equiv-zigzag' up-c c' z P Q id-fam-equiv (succ-ℕ n)
                          ( inv-map-zigzag-sequential-diagram z n
                            ( map-zigzag-sequential-diagram z n a))
                          ( _))))))
              ( concat-inv-coherence-map-inv-is-equiv
                ( equiv-tr
                  ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                  ( naturality-map-hom-diagram-zigzag-sequential-diagram z n a))
                ( square-over-diagram-square-over-colimit up-c c' f P Q id-fam-equiv n a p))) ∙
      assoc _ _ _ ∙
      assoc _ _ _ ∙
      ap
        ( square-over-diagram-square-over-colimit up-c c' f P Q id-fam-equiv n a p ∙_)
        ( ap
          ( inv
            ( is-section-map-inv-equiv
              ( equiv-tr
                ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                ( naturality-map-hom-diagram-zigzag-sequential-diagram z n a))
              ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv (succ-ℕ n)
                ( map-sequential-diagram A n a)
                ( map-family-descent-data-sequential-colimit P' n a p))) ∙_)
          ( assoc _ _ _ ∙
            inv
              ( compute-concat-dependent-identification
                ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                ( lower-triangle-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a))
                ( ap (map-zigzag-sequential-diagram z (succ-ℕ n)) (inv (upper-triangle-zigzag-sequential-diagram z n a)))
                ( lower-triangle-over' up-c c' z P Q id-fam-equiv (succ-ℕ n)
                  ( inv-map-zigzag-sequential-diagram z n
                    ( map-zigzag-sequential-diagram z n a))
                  ( tr
                    ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                    ( lower-triangle-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a))
                    ( tr
                      ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                      ( inv (naturality-map-hom-diagram-zigzag-sequential-diagram z n a))
                      ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv (succ-ℕ n)
                        ( map-sequential-diagram A n a)
                        ( map-family-descent-data-sequential-colimit P' n a p)))))
                ( _)) ∙
              ap
                ( concat-dependent-identification
                  ( family-descent-data-sequential-colimit Q' (succ-ℕ n))
                  ( lower-triangle-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a))
                  ( ap
                    ( map-zigzag-sequential-diagram z (succ-ℕ n))
                    ( inv (upper-triangle-zigzag-sequential-diagram z n a)))
                  ( lower-triangle-over' up-c c' z P Q id-fam-equiv (succ-ℕ n)
                    ( inv-map-zigzag-sequential-diagram z n (map-zigzag-sequential-diagram z n a))
                    ( _)))
                ( inv
                  ( compute-left-whisk-dependent-identification
                    ( map-over-diagram-equiv-over-colimit up-c c' f P Q id-fam-equiv (succ-ℕ n) _)
                    ( inv (upper-triangle-zigzag-sequential-diagram z n a))
                    ( map-eq-transpose-equiv-inv'
                      ( equiv-tr
                        ( family-descent-data-sequential-colimit P' (succ-ℕ n))
                        ( upper-triangle-zigzag-sequential-diagram z n a))
                      ( upper-triangle-over' up-c c' z P Q id-fam-equiv n a
                        ( map-family-descent-data-sequential-colimit P' n _ p))))) ∙
              is-trivial-trivial-pasting up-c c' z P Q id-fam-equiv n a
                ( map-family-descent-data-sequential-colimit P' n _ p)) ∙
          ( left-inv _)) ∙
      right-unit
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : sequential-diagram l1} {X : UU l2}
  {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {B : sequential-diagram l3} {Y : UU l4}
  (c' : cocone-sequential-diagram B Y)
  (z : zigzag-sequential-diagram A B)
  (let f = hom-diagram-zigzag-sequential-diagram z)
  (let f∞ = map-sequential-colimit-hom-sequential-diagram up-c c' f)
  (let
    C = htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f)
  (P : X → UU l5)
  (let P' = descent-data-family-cocone-sequential-diagram c P)
  (Q : Y → UU l5)
  (let Q' = descent-data-family-cocone-sequential-diagram c' Q)
  (e : fam-equiv P (Q ∘ f∞))
  where

  opaque
    compute-square-over-zigzag-square-over-colimit :
      (n : ℕ) (a : family-sequential-diagram A n) →
      pasting-triangles-over
        ( map-sequential-diagram A n)
        ( map-hom-sequential-diagram B f n)
        ( map-hom-sequential-diagram B f (succ-ℕ n))
        ( map-sequential-diagram B n)
        ( map-family-descent-data-sequential-colimit P' n _)
        ( map-over-diagram-equiv-over-colimit up-c c' f P Q e n _)
        ( map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n) _)
        ( map-family-descent-data-sequential-colimit Q' n _)
        ( inv-map-zigzag-sequential-diagram z n)
        ( inv-map-over-diagram-equiv-zigzag up-c c' z P Q e n _)
        ( inv-htpy (upper-triangle-zigzag-sequential-diagram z n))
        ( lower-triangle-zigzag-sequential-diagram z n)
        ( inv-htpy-over
          ( family-descent-data-sequential-colimit P' (succ-ℕ n))
          ( upper-triangle-zigzag-sequential-diagram z n)
          _ _
          ( upper-triangle-over up-c c' z P Q e n))
        ( lower-triangle-over up-c c' z P Q e n)
        { a} ~
      square-over-diagram-square-over-colimit up-c c' f P Q e n a
    compute-square-over-zigzag-square-over-colimit =
      ind-fam-equiv'
        ( λ P e →
          let P' = descent-data-family-cocone-sequential-diagram c P in
          (n : ℕ) (a : family-sequential-diagram A n) →
          pasting-triangles-over
            ( map-sequential-diagram A n)
            ( map-hom-sequential-diagram B f n)
            ( map-hom-sequential-diagram B f (succ-ℕ n))
            ( map-sequential-diagram B n)
            ( map-family-descent-data-sequential-colimit P' n _)
            ( map-over-diagram-equiv-over-colimit up-c c' f P Q e n _)
            ( map-over-diagram-equiv-over-colimit up-c c' f P Q e (succ-ℕ n) _)
            ( map-family-descent-data-sequential-colimit Q' n _)
            ( inv-map-zigzag-sequential-diagram z n)
            ( inv-map-over-diagram-equiv-zigzag up-c c' z P Q e n _)
            ( inv-htpy (upper-triangle-zigzag-sequential-diagram z n))
            ( lower-triangle-zigzag-sequential-diagram z n)
            ( inv-htpy-over
              ( family-descent-data-sequential-colimit P' (succ-ℕ n))
              ( upper-triangle-zigzag-sequential-diagram z n)
              _ _
              ( upper-triangle-over up-c c' z P Q e n))
            ( lower-triangle-over up-c c' z P Q e n)
            { a} ~
          square-over-diagram-square-over-colimit up-c c' f P Q e n a)
        ( compute-square-over-zigzag-square-over-colimit-id up-c c' z Q)
      ( e)
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
  (let
    dup-c' =
      dependent-universal-property-universal-property-sequential-colimit _ up-c')
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
  (let
    𝒞 =
      htpy-dependent-cocone-dependent-universal-property-sequential-colimit
        ( dup-c')
        ( s))
  (let C' = htpy-htpy-dependent-cocone-sequential-diagram Q 𝒞)
  where

  opaque
    unfolding square-over-diagram-square-over-colimit
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
    γ = γ' up-c c' f P Q id-fam-equiv

    -- compute-γ :
    --   (n : ℕ) (a : family-sequential-diagram A n) →
    --   square-over-diagram-square-over-colimit up-c c' f (Q ∘ f∞) Q id-fam-equiv n a ~ γ n a
    -- compute-γ n a p =
    --   ap
    --     ( γ n a p ∙_)
    --     ( ap
    --       ( λ r → ap (tr Q (C (succ-ℕ n) (map-sequential-diagram A n a))) (inv r))
    --       ( compute-preserves-tr-id (coherence-cocone-sequential-diagram c n a) p)) ∙
    --   right-unit

  opaque
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
  pr1 lemma-1-2 n =
    invert-fiberwise-triangle
      ( s∞ ∘ f∞ ∘ map-cocone-sequential-diagram c n)
      ( map-section-dependent-sequential-diagram _ _ s n ∘ map-hom-sequential-diagram B f n)
      ( λ a → equiv-tr Q (C n a))
      ( λ a → apd s∞ (C n a) ∙ C' n (map-hom-sequential-diagram B f n a))
  pr2 lemma-1-2 n = [i]
    where
    goal =
      (pr2
       (section-descent-data-section-family-cocone-sequential-colimit c P
        (s∞ ∘ f∞))
       n
       ∙h
       invert-fiberwise-triangle
       (s∞ ∘ f∞ ∘ pr1 c (succ-ℕ n))
       (pr1 s (succ-ℕ n) ∘ pr1 f (succ-ℕ n))
       (λ a₁ →
          equiv-tr Q
          (C (succ-ℕ n) a₁))
       (λ a₁ →
          apd s∞ (C (succ-ℕ n) a₁) ∙
          C' (succ-ℕ n) (pr1 f (succ-ℕ n) a₁))
       ·r pr2 A n)
      ~
      ((λ {v} v₁ →
          pr2 (dependent-sequential-diagram-descent-data P') n v v₁) ·l
       invert-fiberwise-triangle
       (s∞ ∘ f∞ ∘ pr1 c n)
       (pr1 s n ∘ pr1 f n)
       (λ a₁ →
          equiv-tr Q
          (C n a₁))
       (λ a₁ →
          apd s∞
          (C n a₁) ∙
          C' n (pr1 f n a₁))
       ∙h
       (λ a₁ →
          γ-flip n a₁ (pr1 s n (pr1 f n a₁)) ∙
          ap
          (tr Q
           (inv
            (C (succ-ℕ n) (pr2 A n a₁))))
          (ap (tr (Q ∘ pr1 c' (succ-ℕ n)) (pr2 f n a₁))
           (pr2 s n (pr1 f n a₁))
           ∙ apd (pr1 s (succ-ℕ n)) (pr2 f n a₁))))

    opaque
      [step-1] :
        (a : family-sequential-diagram A n) →
        ap
          ( tr Q (C (succ-ℕ n) (map-sequential-diagram A n a)))
          ( substitution-law-tr Q f∞ (coherence-cocone-sequential-diagram c n a)) ∙
        ap
          ( tr Q (C (succ-ℕ n) (map-sequential-diagram A n a)))
          ( apd (s∞ ∘ f∞) (coherence-cocone-sequential-diagram c n a)) ＝
        ap
          ( tr Q (C (succ-ℕ n) (map-sequential-diagram A n a)))
          ( apd s∞ (ap f∞ (coherence-cocone-sequential-diagram c n a)))
      [step-1] a =
        inv
          ( ap-concat
            ( tr Q (C (succ-ℕ n) (map-sequential-diagram A n a)))
            ( substitution-law-tr Q f∞ (coherence-cocone-sequential-diagram c n a))
            ( apd (s∞ ∘ f∞) (coherence-cocone-sequential-diagram c n a))) ∙
        ap
          ( ap (tr Q (C (succ-ℕ n) (map-sequential-diagram A n a))))
          ( apd-left' f∞ s∞ (coherence-cocone-sequential-diagram c n a))
      [step-2] :
        (a : family-sequential-diagram A n) →
        tr-concat
          ( ap f∞ (coherence-cocone-sequential-diagram c n a))
          ( C (succ-ℕ n) (map-sequential-diagram A n a))
          ( s∞ (f∞ (map-cocone-sequential-diagram c n a))) ∙
        ap
          ( tr Q (C (succ-ℕ n) (map-sequential-diagram A n a)))
          ( apd s∞ (ap f∞ (coherence-cocone-sequential-diagram c n a))) ∙
        apd s∞ (C (succ-ℕ n) (map-sequential-diagram A n a)) ＝
        apd s∞
          ( ap f∞ (coherence-cocone-sequential-diagram c n a) ∙
            C (succ-ℕ n) (map-sequential-diagram A n a))
      [step-2] a =
        inv
          ( apd-concat' s∞
            ( ap f∞ (coherence-cocone-sequential-diagram c n a))
            ( C (succ-ℕ n) (map-sequential-diagram A n a)))
      [step-3] :
        (a : family-sequential-diagram A n) →
        ap
          ( λ p → tr Q p (s∞ (f∞ (map-cocone-sequential-diagram c n a))))
          ( inv
            ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f n a)) ∙
        apd s∞
          ( ap f∞ (coherence-cocone-sequential-diagram c n a) ∙
            C (succ-ℕ n) (map-sequential-diagram A n a)) ＝
        apd s∞
          ( C n a ∙
            ( ( coherence-cocone-sequential-diagram c' n
                ( map-hom-sequential-diagram B f n a)) ∙
              ( ap
                ( map-cocone-sequential-diagram c' (succ-ℕ n))
                ( naturality-map-hom-sequential-diagram B f n a))))
      [step-3] a =
        apd-apd s∞ _ _
          ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f n a)
      [step-4] :
        (a : family-sequential-diagram A n) →
        inv
          ( tr-concat (C n a) _ (s∞ (f∞ (map-cocone-sequential-diagram c n a)))) ∙
        apd s∞
          ( C n a ∙
            ( ( coherence-cocone-sequential-diagram c' n
                ( map-hom-sequential-diagram B f n a)) ∙
              ( ap
                ( map-cocone-sequential-diagram c' (succ-ℕ n))
                ( naturality-map-hom-sequential-diagram B f n a)))) ＝
        ap
          ( tr Q (coherence-cocone-sequential-diagram c' n (map-hom-sequential-diagram B f n a) ∙ ap (map-cocone-sequential-diagram c' (succ-ℕ n)) (naturality-map-hom-sequential-diagram B f n a)))
          ( apd s∞ (C n a)) ∙
        apd s∞ (coherence-cocone-sequential-diagram c' n (map-hom-sequential-diagram B f n a) ∙ ap (map-cocone-sequential-diagram c' (succ-ℕ n)) (naturality-map-hom-sequential-diagram B f n a))
      [step-4] a =
        inv
          ( apd-concat s∞
            ( C n a)
            ( _))
      [step-5] :
        (a : family-sequential-diagram A n) →
        inv
          ( tr-concat
            ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a))
            ( ap
              ( map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a))
            ( tr Q (C n a) (s∞ (f∞ (map-cocone-sequential-diagram c n a))))) ∙
        ap
          ( tr Q (coherence-cocone-sequential-diagram c' n (map-hom-sequential-diagram B f n a) ∙ ap (map-cocone-sequential-diagram c' (succ-ℕ n)) (naturality-map-hom-sequential-diagram B f n a)))
          ( apd s∞ (C n a)) ＝
        ap
          ( tr Q
            ( ap
              ( map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a)) ∘
            tr Q
              ( coherence-cocone-sequential-diagram c' n
                ( map-hom-sequential-diagram B f n a)))
          ( apd s∞ (C n a)) ∙
        inv
          ( tr-concat
            ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a))
            ( ap
              ( map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a))
            ( s∞ (map-cocone-sequential-diagram c' n (map-hom-sequential-diagram B f n a))))
      [step-5] a =
        nat-htpy
          ( inv-htpy
            ( tr-concat
              ( coherence-cocone-sequential-diagram c' n
                ( map-hom-sequential-diagram B f n a))
              ( ap
                ( map-cocone-sequential-diagram c' (succ-ℕ n))
                ( naturality-map-hom-sequential-diagram B f n a))))
          ( apd s∞ (C n a))
      [step-6] :
        (a : family-sequential-diagram A n) →
        inv
          ( tr-concat
            ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a))
            ( ap
              ( map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a))
            ( s∞ (map-cocone-sequential-diagram c' n (map-hom-sequential-diagram B f n a)))) ∙
        apd s∞
          ( ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a)) ∙
            ( ap
              ( map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a))) ＝
        ap
          ( tr Q
            ( ap
              ( map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a)))
          ( apd s∞
            ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a))) ∙
        apd s∞
          ( ap
            ( map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a))
      [step-6] a = inv (apd-concat s∞ _ _)
      [step-7] :
        (a : family-sequential-diagram A n) →
        inv
          ( substitution-law-tr Q
            ( map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a)) ∙
        ap
          ( tr Q
            ( ap
              ( map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a)) ∘
            tr Q
              ( coherence-cocone-sequential-diagram c' n
                ( map-hom-sequential-diagram B f n a)))
          ( apd s∞ (C n a)) ＝
        ap
          ( tr (Q ∘ pr1 c' (succ-ℕ n)) (pr2 f n a) ∘
            tr Q
              ( coherence-cocone-sequential-diagram c' n
                ( map-hom-sequential-diagram B f n a)))
          ( apd s∞ (C n a)) ∙
        inv
        ( substitution-law-tr Q
          ( map-cocone-sequential-diagram c' (succ-ℕ n))
          ( naturality-map-hom-sequential-diagram B f n a))
      [step-7] a =
        nat-htpy
          ( inv-htpy
            ( λ q →
              substitution-law-tr Q
                ( map-cocone-sequential-diagram c' (succ-ℕ n))
                ( naturality-map-hom-sequential-diagram B f n a)
                ))
          ( apd s∞ (C n a))
      [step-8] :
        (a : family-sequential-diagram A n) →
        inv
          ( substitution-law-tr Q
            ( map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a)) ∙
        ap
          ( tr Q
            ( ap
              ( map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a)))
          ( apd s∞
            ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a))) ＝
        ap
          ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a))
          ( apd s∞
            ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a))) ∙
        inv
          ( substitution-law-tr Q
            ( map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a))
      [step-8] a =
        nat-htpy
          ( inv-htpy
            ( λ _ →
              substitution-law-tr Q
                ( map-cocone-sequential-diagram c' (succ-ℕ n))
                ( naturality-map-hom-sequential-diagram B f n a)))
          ( apd s∞
            ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a)))
      [step-9] :
        (a : family-sequential-diagram A n) →
        inv
          ( substitution-law-tr Q
            ( map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a)) ∙
        apd s∞
          ( ap
            ( map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a)) ＝
        apd
          ( s∞ ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
          ( naturality-map-hom-sequential-diagram B f n a)
      [step-9] a =
        inv
          ( apd-left
            ( map-cocone-sequential-diagram c' (succ-ℕ n))
            ( s∞)
            ( naturality-map-hom-sequential-diagram B f n a))
      [step-10] :
        (a : family-sequential-diagram A n) →
        apd
          ( s∞ ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
          ( naturality-map-hom-sequential-diagram B f n a) ∙
        C'
          ( succ-ℕ n)
          ( map-hom-sequential-diagram B f
            ( succ-ℕ n)
            ( map-sequential-diagram A n a)) ＝
        ap
          ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a))
          ( C'
            ( succ-ℕ n)
            ( map-sequential-diagram B n
              ( map-hom-sequential-diagram B f n a))) ∙
        apd
          ( map-section-dependent-sequential-diagram _ _ s (succ-ℕ n))
          ( naturality-map-hom-sequential-diagram B f n a)
      [step-10] a =
        inv-dep-nat-htpy
          ( C' (succ-ℕ n))
          ( naturality-map-hom-sequential-diagram B f n a)
      [step-11] :
        (a : family-sequential-diagram A n) →
        ap
          ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a))
          ( apd s∞
            ( coherence-cocone-sequential-diagram c' n
              ( map-hom-sequential-diagram B f n a))) ∙
        ap
          ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a))
          ( C'
            ( succ-ℕ n)
            ( map-sequential-diagram B n
              ( map-hom-sequential-diagram B f n a))) ＝
        ap
          ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a))
          ( ap
              ( tr Q
                ( coherence-cocone-sequential-diagram c' n
                  ( map-hom-sequential-diagram B f n a)))
              ( C' n (map-hom-sequential-diagram B f n a)) ∙
            naturality-map-section-dependent-sequential-diagram _ _ s n
              ( map-hom-sequential-diagram B f n a))
      [step-11] a =
        inv
          ( ap-concat
            ( tr
              ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a))
            ( apd s∞
              ( coherence-cocone-sequential-diagram c' n
                ( map-hom-sequential-diagram B f n a)))
            ( C'
              ( succ-ℕ n)
              ( map-sequential-diagram B n
                ( map-hom-sequential-diagram B f n a)))) ∙
        ap
          ( ap
            ( tr
              ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a)))
          ( pr2 𝒞 n (map-hom-sequential-diagram B f n a))
      [step-12] :
        (a : family-sequential-diagram A n) →
        ap
          ( tr
              ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a) ∘
            tr Q
              ( coherence-cocone-sequential-diagram c' n
                ( map-hom-sequential-diagram B f n a)))
          ( apd s∞ (C n a)) ∙
        ap
          ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a))
          ( ap
              ( tr Q
                ( coherence-cocone-sequential-diagram c' n
                  ( map-hom-sequential-diagram B f n a)))
              ( C' n (map-hom-sequential-diagram B f n a)) ∙
            naturality-map-section-dependent-sequential-diagram _ _ s n
              ( map-hom-sequential-diagram B f n a)) ＝
        ap
          ( tr
              ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a) ∘
            tr Q
              ( coherence-cocone-sequential-diagram c' n
                ( map-hom-sequential-diagram B f n a)))
          ( apd s∞ (C n a) ∙
            C' n (map-hom-sequential-diagram B f n a)) ∙
        ap
          ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a))
          ( naturality-map-section-dependent-sequential-diagram _ _ s n
            ( map-hom-sequential-diagram B f n a))
      open import foundation.whiskering-identifications-concatenation
      [step-12] a =
        left-whisker-concat-coherence-triangle-identifications
          ( ap _ (apd s∞ (C n a)))
          _ _ _
          ( ap-concat
            ( tr
              ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a))
            ( ap
              ( tr Q
                ( coherence-cocone-sequential-diagram c' n
                  ( map-hom-sequential-diagram B f n a)))
              ( C' n (map-hom-sequential-diagram B f n a)))
            ( naturality-map-section-dependent-sequential-diagram _ _ s n
              ( map-hom-sequential-diagram B f n a)) ∙
            right-whisker-concat
              ( inv
                ( ap-comp
                  ( tr
                    ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
                    ( naturality-map-hom-sequential-diagram B f n a))
                  ( tr Q
                    ( coherence-cocone-sequential-diagram c' n
                      ( map-hom-sequential-diagram B f n a)))
                  ( C' n (map-hom-sequential-diagram B f n a))))
              ( _)) ∙
        right-whisker-concat
          ( inv
            (ap-concat
              ( tr
                  ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
                  ( naturality-map-hom-sequential-diagram B f n a) ∘
                tr Q
                  ( coherence-cocone-sequential-diagram c' n
                    ( map-hom-sequential-diagram B f n a)))
              ( apd s∞ (C n a))
              ( C' n (map-hom-sequential-diagram B f n a))))
          ( _)

    opaque
      unfolding γ γ' γ-base' γ-flip

      [i] : goal
      [i] =
        transpose-sq
          ( map-sequential-diagram A n)
          ( s∞ ∘ f∞ ∘ map-cocone-sequential-diagram c n)
          ( s∞ ∘ f∞ ∘ map-cocone-sequential-diagram c (succ-ℕ n))
          ( map-section-dependent-sequential-diagram _ _ s n ∘ map-hom-sequential-diagram B f n)
          ( map-section-dependent-sequential-diagram _ _ s (succ-ℕ n) ∘ map-hom-sequential-diagram B f (succ-ℕ n))
          ( λ q → tr (Q ∘ f∞) (coherence-cocone-sequential-diagram c n _) q)
          ( ( tr
              ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n _)) ∘
            ( tr Q
              ( coherence-cocone-sequential-diagram c' n
                ( map-hom-sequential-diagram B f n _))))
          ( λ {a} → equiv-tr Q (C n a))
          ( λ {a} → equiv-tr Q (C (succ-ℕ n) a))
          ( λ a → apd (s∞ ∘ f∞) (coherence-cocone-sequential-diagram c n a))
          ( γ n _)
          ( λ a → apd s∞ (C (succ-ℕ n) a) ∙ C' (succ-ℕ n) (map-hom-sequential-diagram B f (succ-ℕ n) a))
          ( λ a → apd s∞ (C n a) ∙ C' n (map-hom-sequential-diagram B f n a))
          ( λ a →
            ap
              ( tr (Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n)) (naturality-map-hom-sequential-diagram B f n a))
              ( naturality-map-section-dependent-sequential-diagram _ _ s n (map-hom-sequential-diagram B f n a)) ∙
            apd (map-section-dependent-sequential-diagram _ _ s (succ-ℕ n)) (naturality-map-hom-sequential-diagram B f n a))
          ( λ a →
            ( left-whisker-concat
              ( γ n a (s∞ (f∞ (map-cocone-sequential-diagram c n a))))
              ( inv (assoc _ _ _))) ∙
            ( inv (assoc _ _ _)) ∙
            ( right-whisker-concat
              ( ( right-whisker-concat-coherence-triangle-identifications' _ _ _
                  ( apd s∞ (C (succ-ℕ n) (map-sequential-diagram A n a)))
                  ( assoc _ _ _ ∙
                    left-whisker-concat
                      ( γ-base' up-c c' f (Q ∘ f∞) Q id-fam-equiv n a (s∞ (f∞ (map-cocone-sequential-diagram c n a))))
                      ( [step-1] a) ∙
                    assoc _ _ _)) ∙
                ( assoc _ _ _) ∙
                ( left-whisker-concat
                  ( _)
                  ( [step-2] a)) ∙
                ( left-whisker-concat-coherence-triangle-identifications' _ _ _ _
                  ( [step-3] a)) ∙
                ( left-whisker-concat-coherence-triangle-identifications' _ _ _ _
                  ( [step-4] a)) ∙
                ( left-whisker-concat-coherence-triangle-identifications' _ _ _ _
                  ( ( right-whisker-concat-coherence-triangle-identifications' _ _ _
                      ( apd s∞ _)
                      ( [step-5] a)) ∙
                  ( ( left-whisker-concat-coherence-triangle-identifications' _ _ _ _
                      ( [step-6] a)))) ∙
                ( right-whisker-concat-coherence-square-identifications _ _ _ _
                  ( [step-7] a)
                  ( _)) ∙
                ( left-whisker-concat _
                  ( ( right-whisker-concat-coherence-square-identifications _ _ _ _
                      ( [step-8] a)
                      ( _)) ∙
                    ( left-whisker-concat _
                      ( [step-9] a))))))
              ( C'
                ( succ-ℕ n)
                ( map-hom-sequential-diagram B f (succ-ℕ n)
                  ( map-sequential-diagram A n a)))) ∙
            ( assoc _ _ _) ∙
            ( left-whisker-concat-coherence-triangle-identifications
              ( ap
                ( tr
                    ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
                    ( naturality-map-hom-sequential-diagram B f n a) ∘
                  tr Q
                    ( coherence-cocone-sequential-diagram c' n
                      ( map-hom-sequential-diagram B f n a)))
                ( apd s∞ (C n a)))
              _ _ _
              ( ( left-whisker-concat-coherence-square-identifications _ _ _ _ _
                  ( [step-10] a)) ∙
                ( right-whisker-concat
                  ( [step-11] a)
                  ( _)))) ∙
            ( right-whisker-concat
              ( [step-12] a)
              ( apd
                ( map-section-dependent-sequential-diagram _ _ s (succ-ℕ n))
                ( naturality-map-hom-sequential-diagram B f n a))) ∙
            ( assoc _ _ _))

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

    opaque
      unfolding γ-flip

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

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : sequential-diagram l1} {X : UU l2}
  {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {B : sequential-diagram l3} {Y : UU l4}
  {c' : cocone-sequential-diagram B Y}
  (up-c' : universal-property-sequential-colimit c')
  (f : hom-sequential-diagram A B)
  (let f∞ = map-sequential-colimit-hom-sequential-diagram up-c c' f)
  (Q : Y → UU l5)
  (let Q' = descent-data-family-cocone-sequential-diagram c (Q ∘ f∞))
  where

  comp-over-diagram' :
  -- For now restricted to l5
    (P : X → UU l5)
    (let P' = descent-data-family-cocone-sequential-diagram c P)
    (e' : fam-equiv P (Q ∘ f∞))
    (s : section-descent-data-sequential-colimit P')
    (let s∞ = sect-family-sect-dd-sequential-colimit up-c P s) →
    section-descent-data-sequential-colimit Q'
  pr1 (comp-over-diagram' P e' s) n a =
    map-fam-equiv e'
      ( map-cocone-sequential-diagram c n a)
      ( map-section-dependent-sequential-diagram _ _ s n a)
  pr2 (comp-over-diagram' P e' s) n a =
    inv
      ( preserves-tr
        ( map-fam-equiv e')
        ( coherence-cocone-sequential-diagram c n a)
        ( map-section-dependent-sequential-diagram _ _ s n a)) ∙
    ap
      ( map-fam-equiv e'
        ( map-cocone-sequential-diagram c (succ-ℕ n)
        ( map-sequential-diagram A n a)))
      ( naturality-map-section-dependent-sequential-diagram _ _ s n a)

  compute-comp-over-diagram' :
    (s : section-descent-data-sequential-colimit Q') →
    htpy-section-dependent-sequential-diagram
      ( comp-over-diagram' (Q ∘ f∞) id-fam-equiv s)
      ( s)
  pr1 (compute-comp-over-diagram' s) n = refl-htpy
  pr2 (compute-comp-over-diagram' s) n a =
    right-unit ∙
    ap-binary
      ( _∙_)
      ( ap
        ( inv)
        ( compute-preserves-tr-id
          ( coherence-cocone-sequential-diagram c n a)
          ( map-section-dependent-sequential-diagram _ _ s n a)))
      ( ap-id (naturality-map-section-dependent-sequential-diagram _ _ s n a))

  theorem' :
    (P : X → UU l5)
    (let P' = descent-data-family-cocone-sequential-diagram c P)
    (e' : fam-equiv P (Q ∘ f∞))
    (s : section-descent-data-sequential-colimit P')
    (let s∞ = sect-family-sect-dd-sequential-colimit up-c P s) →
    sect-family-sect-dd-sequential-colimit up-c (Q ∘ f∞)
      ( comp-over-diagram' P e' s) ~
    (map-fam-equiv e' _ ∘ s∞)
  theorem' P =
    ind-fam-equiv'
      ( λ P e' →
        let P' = descent-data-family-cocone-sequential-diagram c P in
        (s : section-descent-data-sequential-colimit P') →
        sect-family-sect-dd-sequential-colimit up-c (Q ∘ f∞)
          ( comp-over-diagram' P e' s) ~
        map-fam-equiv e' _ ∘ sect-family-sect-dd-sequential-colimit up-c P s)
      ( λ s →
        htpy-colimit-htpy-diagram-section up-c (Q ∘ f∞) _ _
          ( compute-comp-over-diagram' s))
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
  (f : hom-sequential-diagram A B)
  {P : X → UU l5} {Q : Y → UU l5}
  (let
    P' = descent-data-family-cocone-sequential-diagram c P
    Q' = descent-data-family-cocone-sequential-diagram c' Q
    f∞ = map-sequential-colimit-hom-sequential-diagram up-c c' f)
  (s : section-descent-data-sequential-colimit P')
  (t : section-descent-data-sequential-colimit Q')
  (let
    s∞ = sect-family-sect-dd-sequential-colimit up-c P s
    t∞ = sect-family-sect-dd-sequential-colimit up-c' Q t)
  (e : fam-equiv P (Q ∘ f∞))
  (let C = htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f)
  (let
    f∞n =
      λ n a →
      tr Q (C n a) ∘ map-fam-equiv e (map-cocone-sequential-diagram c n a))
  where


  -- TODO: cleanup
  -- - make γ into a proper definition
  -- - pasting of squares
  -- - find the right lemmas
  opaque
    unfolding square-over-diagram-square-over-colimit γ γ' γ-base'
    square-colimit-cube-diagram :
      (F :
        (n : ℕ) →
        f∞n n _ ∘ map-section-dependent-sequential-diagram _ _ s n ~
        map-section-dependent-sequential-diagram _ _ t n ∘
        map-hom-sequential-diagram B f n) →
      ((n : ℕ) →
        section-square-over
          ( map-sequential-diagram A n)
          ( map-hom-sequential-diagram B f n)
          ( map-hom-sequential-diagram B f (succ-ℕ n))
          ( map-sequential-diagram B n)
          ( λ {a} → map-family-descent-data-sequential-colimit P' n a)
          ( λ {a} → f∞n n a)
          ( λ {a} → f∞n (succ-ℕ n) a)
          ( λ {b} → map-family-descent-data-sequential-colimit Q' n b)
          ( map-section-dependent-sequential-diagram _ _ s n)
          ( map-section-dependent-sequential-diagram _ _ t n)
          ( map-section-dependent-sequential-diagram _ _ s (succ-ℕ n))
          ( map-section-dependent-sequential-diagram _ _ t (succ-ℕ n))
          ( naturality-map-section-dependent-sequential-diagram _ _ s n)
          ( F n)
          ( F (succ-ℕ n))
          ( naturality-map-section-dependent-sequential-diagram _ _ t n)
          ( naturality-map-hom-sequential-diagram B f n)
          ( square-over-diagram-square-over-colimit up-c c' f P Q e n _)) →
      map-fam-equiv e _ ∘ s∞ ~ t∞ ∘ f∞
    square-colimit-cube-diagram F cubes =
      inv-htpy (theorem' up-c up-c' f Q P e s) ∙h
      theorem up-c up-c' Q f t _ F
        ( λ n a →
          assoc _ _ _ ∙
          ap
            ( γ up-c up-c' Q f t n a (map-fam-equiv e (map-cocone-sequential-diagram c n a) (map-section-dependent-sequential-diagram _ _ s n a)) ∙_)
            ( ( ap
                ( _∙ F (succ-ℕ n) (map-sequential-diagram A n a))
                ( ap-concat (tr Q (C (succ-ℕ n) (map-sequential-diagram A n a)))
                  ( inv (preserves-tr (map-fam-equiv e) (coherence-cocone-sequential-diagram c n a) (map-section-dependent-sequential-diagram _ _ s n a)))
                  ( ap (map-fam-equiv e (map-cocone-sequential-diagram c (succ-ℕ n) (map-sequential-diagram A n a))) (naturality-map-section-dependent-sequential-diagram _ _ s n a)) ∙
                  ap
                    ( ap (tr Q (C (succ-ℕ n) (map-sequential-diagram A n a))) (inv (preserves-tr (map-fam-equiv e) (coherence-cocone-sequential-diagram c n a) (map-section-dependent-sequential-diagram _ _ s n a))) ∙_)
                    ( inv (ap-comp (tr Q (C (succ-ℕ n) _)) (map-fam-equiv e _) (naturality-map-section-dependent-sequential-diagram _ _ s n a))))) ∙
              ( assoc _ _ _)) ∙
          inv (assoc _ _ _) ∙
          inv (assoc _ _ _) ∙
          cubes n a)
```
