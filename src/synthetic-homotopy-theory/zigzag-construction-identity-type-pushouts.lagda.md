# The zigzag construction of identity types of pushouts

```agda
{-# OPTIONS --lossy-unification #-}

module synthetic-homotopy-theory.zigzag-construction-identity-type-pushouts where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.transposition-identifications-along-equivalences
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.functoriality-sequential-colimits
open import synthetic-homotopy-theory.identity-systems-descent-data-pushouts
open import synthetic-homotopy-theory.families-descent-data-pushouts
open import synthetic-homotopy-theory.flattening-lemma-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.shifts-sequential-diagrams
open import synthetic-homotopy-theory.sections-descent-data-pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
open import synthetic-homotopy-theory.zigzags-sequential-diagrams
```

</details>

## Idea

The identity types of pushouts may be characterized as certain sequential
colimits of pushouts.

## Definitions

```agda
open import foundation.commuting-triangles-of-maps
open import foundation.homotopy-induction
open import foundation.dependent-homotopies
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2}
  {A' : A → UU l3} (B' : B → UU l4)
  {f g : A → B}
  (H : f ~ g)
  (f' : {a : A} → A' a → B' (f a))
  (g' : {a : A} → A' a → B' (g a))
  where

  htpy-over : UU (l1 ⊔ l3 ⊔ l4)
  htpy-over = {a : A} (a' : A' a) → dependent-identification B' (H a) (f' a') (g' a')

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : A → UU l4} {B' : B → UU l5} {X' : X → UU l6}
  {f g : A → B}
  (H : f ~ g)
  {f' : {a : A} → A' a → B' (f a)}
  {g' : {a : A} → A' a → B' (g a)}
  (H' : htpy-over B' H f' g')
  {s : X → A} (s' : {x : X} → X' x → A' (s x))
  where

  right-whisk-htpy-over : htpy-over B' (H ·r s) (f' ∘ s') (g' ∘ s')
  right-whisk-htpy-over a' = H' (s' a')

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : A → UU l4} {B' : B → UU l5} {X' : X → UU l6}
  {f g : A → B}
  (H : f ~ g)
  {f' : {a : A} → A' a → B' (f a)}
  {g' : {a : A} → A' a → B' (g a)}
  (H' : htpy-over B' H f' g')
  {s : B → X} (s' : {b : B} → B' b → X' (s b))
  where

  left-whisk-htpy-over : htpy-over X' (s ·l H) (s' ∘ f') (s' ∘ g')
  left-whisk-htpy-over =
    ind-htpy f
      ( λ g H →
        {g' : {a : A} → A' a → B' (g a)} (H' : htpy-over B' H f' g') →
        htpy-over X' (s ·l H) (s' ∘ f') (s' ∘ g'))
      ( λ H' → s' ·l H')
      ( H)
      ( H')

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {A' : A → UU l3} {B' : B → UU l4}
  {f g h : A → B}
  (H : f ~ g) (K : g ~ h)
  {f' : {a : A} → A' a → B' (f a)}
  {g' : {a : A} → A' a → B' (g a)}
  {h' : {a : A} → A' a → B' (h a)}
  (H' : htpy-over B' H f' g') (K' : htpy-over B' K g' h')
  where

  concat-htpy-over : htpy-over B' (H ∙h K) f' h'
  concat-htpy-over {a} a' =
    concat-dependent-identification B' (H a) (K a) (H' a') (K' a')

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : A → UU l4} {B' : B → UU l5} {X' : X → UU l6}
  (f : A → B) (g : A → X) (m : B → X)
  (f' : {a : A} → A' a → B' (f a))
  (g' : {a : A} → A' a → X' (g a))
  (m' : {b : B} → B' b → X' (m b))
  (sA : (a : A) → A' a) (sB : (b : B) → B' b) (sX : (x : X) → X' x)
  (F : (a : A) → f' (sA a) ＝ sB (f a))
  (G : (a : A) → g' (sA a) ＝ sX (g a))
  (M : (b : B) → m' (sB b) ＝ sX (m b))
  where

  section-triangle-over :
    (H : coherence-triangle-maps g m f) →
    (H' : htpy-over X' H g' (m' ∘ f')) →
    UU (l1 ⊔ l6)
  section-triangle-over H H' =
    (a : A) →
    H' (sA a) ∙ ap m' (F a) ∙ (M (f a)) ＝
    ap (tr X' (H a)) (G a) ∙ apd sX (H a)

  section-triangle-over' :
    (H : coherence-triangle-maps' g m f) →
    (H' : htpy-over X' H (m' ∘ f') g') →
    UU (l1 ⊔ l6)
  section-triangle-over' H H' =
    (a : A) →
    ( H' (sA a) ∙ G a) ＝
    ( ap (tr X' (H a) ∘ m') (F a) ∙ ap (tr X' (H a)) (M (f a)) ∙ apd sX (H a))

  -- actually ≐ section-triangle-over 🤔
  -- section-triangle-over-inv :
  --   (H : coherence-triangle-maps g m f) →
  --   (H' : {a : A} (a' : A' a) → dependent-identification X' (H a) (g' a') (m' (f' a'))) →
  --   UU (l1 ⊔ l6)
  -- section-triangle-over-inv H H' =
  --   (a : A) →
  --   H' (sA a) ∙ ap m' (F a) ∙ (M (f a)) ＝
  --   ap (tr X' (H a)) (G a) ∙ apd sX (H a)

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {A' : A → UU l3} {B' : B → UU l4}
  (f : A → B)
  (f' : {a : A} → A' a → B' (f a))
  (sA : (a : A) → A' a)
  (sB : (b : B) → B' b)
  where

  section-map-over : UU (l1 ⊔ l4)
  section-map-over = (a : A) → f' (sA a) ＝ sB (f a)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  {A' : A → UU l4} {B' : B → UU l5} {C' : C → UU l6}
  (g : B → C) (f : A → B)
  (g' : {b : B} → B' b → C' (g b))
  (f' : {a : A} → A' a → B' (f a))
  (sA : (a : A) → A' a) (sB : (b : B) → B' b) (sC : (c : C) → C' c)
  where

  comp-section-map-over :
    section-map-over g g' sB sC → section-map-over f f' sA sB →
    section-map-over (g ∘ f) (g' ∘ f') sA sC
  comp-section-map-over G F =
    g' ·l F ∙h G ·r f

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {A' : A → UU l3} {B' : B → UU l4}
  {f g : A → B}
  (H : f ~ g)
  {f' : {a : A} → A' a → B' (f a)}
  {g' : {a : A} → A' a → B' (g a)}
  (H' : htpy-over B' H f' g')
  (sA : (a : A) → A' a)
  (sB : (b : B) → B' b)
  (F : section-map-over f f' sA sB)
  (G : section-map-over g g' sA sB)
  where

  section-htpy-over : UU (l1 ⊔ l4)
  section-htpy-over =
    (a : A) →
    H' (sA a) ∙ G a ＝
    ap (tr B' (H a)) (F a) ∙ apd sB (H a)

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {A' : A → UU l3} {B' : B → UU l4}
  {f g i : A → B}
  (H : f ~ g) (K : g ~ i)
  {f' : {a : A} → A' a → B' (f a)}
  {g' : {a : A} → A' a → B' (g a)}
  {i' : {a : A} → A' a → B' (i a)}
  (H' : htpy-over B' H f' g') (K' : htpy-over B' K g' i')
  (sA : (a : A) → A' a)
  (sB : (b : B) → B' b)
  (F : section-map-over f f' sA sB)
  (G : section-map-over g g' sA sB)
  (I : section-map-over i i' sA sB)
  (α : section-htpy-over H H' sA sB F G)
  (β : section-htpy-over K K' sA sB G I)
  where

  concat-section-htpy-over :
    section-htpy-over
      ( H ∙h K)
      ( concat-htpy-over H K H' K')
      ( sA)
      ( sB)
      ( F)
      ( I)
  concat-section-htpy-over =
    ind-htpy f
      ( λ g H →
        {i : A → B} (K : g ~ i)
        {g' : {a : A} → A' a → B' (g a)}
        {i' : {a : A} → A' a → B' (i a)}
        (H' : htpy-over B' H f' g') (K' : htpy-over B' K g' i')
        (G : section-map-over g g' sA sB)
        (I : section-map-over i i' sA sB)
        (α : section-htpy-over H H' sA sB F G)
        (β : section-htpy-over K K' sA sB G I) →
        section-htpy-over
          ( H ∙h K)
          ( concat-htpy-over H K H' K')
          sA sB F I)
      ( λ K H' K' G I α β a →
        ind-htpy (f' {a})
          ( λ g'a H' →
            {ia : B} (K : f a ＝ ia)
            {i'a : A' a → B' ia}
            (K' : (a' : A' a) → dependent-identification B' K (g'a a') (i'a a'))
            (G : g'a (sA a) ＝ sB (f a))
            (I : i'a (sA a) ＝ sB ia)
            (α : H' (sA a) ∙ G ＝ ap id (F a) ∙ refl)
            (β : K' (sA a) ∙ I ＝ ap (tr B' K) G ∙ apd sB K) →
              concat-dependent-identification B' refl K (H' (sA a)) (K' (sA a)) ∙ I ＝
              ap (tr B' K) (F a) ∙ apd sB K)
          ( λ K K' G I α β → β ∙ ap (λ p → ap (tr B' K) p ∙ apd sB K) (α ∙ (right-unit ∙ ap-id (F a))))
          ( H' {a})
          ( K a)
          ( K' {a})
          ( G a)
          ( I a)
          ( α a)
          ( β a))
      ( H)
      ( K)
      ( H')
      ( K')
      ( G)
      ( I)
      ( α)
      ( β)

module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {P1 : UU l1} {P2 : UU l2} {P3 : UU l3} {P4 : UU l4}
  {Q1 : P1 → UU l5} {Q2 : P2 → UU l6} {Q3 : P3 → UU l7} {Q4 : P4 → UU l8}
  (g1 : P1 → P3) (f1 : P1 → P2) (f2 : P3 → P4) (g2 : P2 → P4)
  (g1' : {p : P1} → Q1 p → Q3 (g1 p))
  (f1' : {p : P1} → Q1 p → Q2 (f1 p))
  (f2' : {p : P3} → Q3 p → Q4 (f2 p))
  (g2' : {p : P2} → Q2 p → Q4 (g2 p))
  where

  module _
    (s1 : (p : P1) → Q1 p) (s2 : (p : P2) → Q2 p) (s3 : (p : P3) → Q3 p)
    (s4 : (p : P4) → Q4 p)
    (G1 : (p : P1) → g1' (s1 p) ＝ s3 (g1 p))
    (F1 : (p : P1) → f1' (s1 p) ＝ s2 (f1 p))
    (F2 : (p : P3) → f2' (s3 p) ＝ s4 (f2 p))
    (G2 : (p : P2) → g2' (s2 p) ＝ s4 (g2 p))
    (H : coherence-square-maps g1 f1 f2 g2)
    (H' : htpy-over Q4 H (g2' ∘ f1') (f2' ∘ g1'))
    where

    section-square-over : UU (l1 ⊔ l8)
    section-square-over =
      (p : P1) →
      H' (s1 p) ∙ ap f2' (G1 p) ∙ (F2 (g1 p)) ＝
      ( ap (tr Q4 (H p) ∘ g2') (F1 p) ∙
        ap (tr Q4 (H p)) (G2 (f1 p)) ∙
        apd s4 (H p))

    get-section-square-over :
      section-htpy-over H H' s1 s4
        ( comp-section-map-over g2 f1 g2' f1' s1 s2 s4 G2 F1)
        ( comp-section-map-over f2 g1 f2' g1' s1 s3 s4 F2 G1) →
      section-square-over
    get-section-square-over = {!!}

  module _
    (m : P2 → P3)
    (m' : {p : P2} → Q2 p → Q3 (m p))
    (B1 : coherence-triangle-maps' g1 m f1)
    (B2 : coherence-triangle-maps g2 f2 m)
    (T1 : htpy-over Q3 B1 (m' ∘ f1') g1')
    (T2 : htpy-over Q4 B2 g2' (f2' ∘ m'))
    where

    pasting-triangles-over :
      htpy-over Q4
        ( horizontal-pasting-up-diagonal-coherence-triangle-maps g1 f1 f2 g2 B1 B2)
        ( g2' ∘ f1')
        ( f2' ∘ g1')
    pasting-triangles-over =
      concat-htpy-over
        ( B2 ·r f1)
        ( f2 ·l B1)
        ( right-whisk-htpy-over B2 T2 f1')
        ( left-whisk-htpy-over B1 T1 f2')

  module _
    (m : P2 → P3)
    (m' : {p : P2} → Q2 p → Q3 (m p))
    (s1 : (p : P1) → Q1 p) (s2 : (p : P2) → Q2 p) (s3 : (p : P3) → Q3 p)
    (s4 : (p : P4) → Q4 p)
    (G1 : (p : P1) → g1' (s1 p) ＝ s3 (g1 p))
    (F1 : (p : P1) → f1' (s1 p) ＝ s2 (f1 p))
    (F2 : (p : P3) → f2' (s3 p) ＝ s4 (f2 p))
    (G2 : (p : P2) → g2' (s2 p) ＝ s4 (g2 p))
    (M : (p : P2) → m' (s2 p) ＝ s3 (m p))
    (B1 : coherence-triangle-maps' g1 m f1)
    (B2 : coherence-triangle-maps g2 f2 m)
    (T1 : htpy-over Q3 B1 (m' ∘ f1') g1')
    (T2 : htpy-over Q4 B2 g2' (f2' ∘ m'))
    where

    pasting-sections-triangles-over :
      section-triangle-over' f1 g1 m f1' g1' m' s1 s2 s3 F1 G1 M B1 T1 →
      section-triangle-over m g2 f2 m' g2' f2' s2 s3 s4 M G2 F2 B2 T2 →
      section-square-over s1 s2 s3 s4 G1 F1 F2 G2
        ( horizontal-pasting-up-diagonal-coherence-triangle-maps g1 f1 f2 g2 B1 B2)
        ( pasting-triangles-over m m' B1 B2 T1 T2)
    pasting-sections-triangles-over S1 S2 =
      get-section-square-over s1 s2 s3 s4 G1 F1 F2 G2
        ( horizontal-pasting-up-diagonal-coherence-triangle-maps g1 f1 f2 g2 B1 B2)
        ( pasting-triangles-over m m' B1 B2 T1 T2)
        ( concat-section-htpy-over (B2 ·r f1) (f2 ·l B1)
           ( right-whisk-htpy-over B2 T2 f1')
           ( left-whisk-htpy-over B1 T1 f2')
           s1 s4
           ( comp-section-map-over g2 f1 g2' f1' s1 s2 s4 G2 F1)
           ( comp-section-map-over (f2 ∘ m) f1 (f2' ∘ m') f1' s1 s2 s4
             ( comp-section-map-over f2 m f2' m' s2 s3 s4 F2 M)
             ( F1))
           ( comp-section-map-over f2 g1 f2' g1' s1 s3 s4 F2 G1)
           {!!}
           {!!})
```
^ remove this code fence
-- module _
--   {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
--   where

--   type-stage-zigzag-construction-id-pushout : ℕ → UU (lsuc (l1 ⊔ l2 ⊔ l3))
--   type-stage-zigzag-construction-id-pushout n =
--     Σ ( codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3))
--       ( λ Path-to-b →
--         Σ ( domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3))
--           ( λ Path-to-a →
--             ( Σ ( (s : spanning-type-span-diagram 𝒮) →
--                   Path-to-b (right-map-span-diagram 𝒮 s) →
--                   Path-to-a (left-map-span-diagram 𝒮 s))
--                 ( λ _ →
--                   rec-ℕ
--                     ( raise-unit (lsuc (l1 ⊔ l2 ⊔ l3)))
--                     ( λ _ _ →
--                       ( codomain-span-diagram 𝒮 →
--                         span-diagram
--                           ( l1 ⊔ l2 ⊔ l3)
--                           ( l1 ⊔ l2 ⊔ l3)
--                           ( l1 ⊔ l2 ⊔ l3)) ×
--                       ( domain-span-diagram 𝒮 →
--                         span-diagram
--                           ( l1 ⊔ l2 ⊔ l3)
--                           ( l1 ⊔ l2 ⊔ l3)
--                           ( l1 ⊔ l2 ⊔ l3)))
--                     ( n)))))

-- module _
--   {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
--   (a₀ : domain-span-diagram 𝒮)
--   where

--   stage-zigzag-construction-id-pushout :
--     (n : ℕ) → type-stage-zigzag-construction-id-pushout 𝒮 n
--   stage-zigzag-construction-id-pushout zero-ℕ =
--     Path-to-b ,
--     Path-to-a ,
--     ( λ s → raise-ex-falso _) ,
--     raise-star
--     where
--     Path-to-b : codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
--     Path-to-b _ = raise-empty _
--     Path-to-a : domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
--     Path-to-a a = raise (l2 ⊔ l3) (a₀ ＝ a)
--   stage-zigzag-construction-id-pushout (succ-ℕ n) =
--     Path-to-b ,
--     Path-to-a ,
--     ( λ s p → inr-pushout _ _ (s , refl , p)) ,
--     span-diagram-B ,
--     span-diagram-A
--     where
--     span-diagram-B :
--       codomain-span-diagram 𝒮 →
--       span-diagram (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l3)
--     span-diagram-B b =
--       make-span-diagram
--         ( pr2 ∘ pr2)
--         ( tot
--           ( λ s →
--             tot
--               ( λ r (p : pr1 (stage-zigzag-construction-id-pushout n) b) →
--                 pr1
--                   ( pr2 (pr2 (stage-zigzag-construction-id-pushout n)))
--                   ( s)
--                   ( tr (pr1 (stage-zigzag-construction-id-pushout n)) r p))))
--     Path-to-b : codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
--     Path-to-b b = standard-pushout (span-diagram-B b)
--     span-diagram-A :
--       domain-span-diagram 𝒮 →
--       span-diagram (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l3)
--     span-diagram-A a =
--       make-span-diagram
--         ( pr2 ∘ pr2)
--         ( tot
--           ( λ s →
--             tot
--               ( λ r (p : pr1 (pr2 (stage-zigzag-construction-id-pushout n)) a) →
--                 inr-standard-pushout
--                   ( span-diagram-B (right-map-span-diagram 𝒮 s))
--                   ( ( s) ,
--                     ( refl) ,
--                     ( tr
--                       ( pr1 (pr2 (stage-zigzag-construction-id-pushout n)))
--                       ( r)
--                       ( p))))))
--     Path-to-a : domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
--     Path-to-a a = standard-pushout (span-diagram-A a)

--   span-diagram-path-to-b :
--     codomain-span-diagram 𝒮 → ℕ →
--     span-diagram
--       ( l1 ⊔ l2 ⊔ l3)
--       ( l1 ⊔ l2 ⊔ l3)
--       ( l1 ⊔ l2 ⊔ l3)
--   span-diagram-path-to-b b n =
--     pr1 (pr2 (pr2 (pr2 (stage-zigzag-construction-id-pushout (succ-ℕ n))))) b

--   span-diagram-path-to-a :
--     domain-span-diagram 𝒮 → ℕ →
--     span-diagram
--       ( l1 ⊔ l2 ⊔ l3)
--       ( l1 ⊔ l2 ⊔ l3)
--       ( l1 ⊔ l2 ⊔ l3)
--   span-diagram-path-to-a a n =
--     pr2 (pr2 (pr2 (pr2 (stage-zigzag-construction-id-pushout (succ-ℕ n))))) a

--   Path-to-b : codomain-span-diagram 𝒮 → ℕ → UU (l1 ⊔ l2 ⊔ l3)
--   Path-to-b b n = pr1 (stage-zigzag-construction-id-pushout n) b

--   Path-to-a : domain-span-diagram 𝒮 → ℕ → UU (l1 ⊔ l2 ⊔ l3)
--   Path-to-a a n = pr1 (pr2 (stage-zigzag-construction-id-pushout n)) a

--   inl-Path-to-b :
--     (b : codomain-span-diagram 𝒮) (n : ℕ) → Path-to-b b n → Path-to-b b (succ-ℕ n)
--   inl-Path-to-b b n =
--     inl-standard-pushout
--       ( span-diagram-path-to-b b n)

--   inl-Path-to-a :
--     (a : domain-span-diagram 𝒮) (n : ℕ) → Path-to-a a n → Path-to-a a (succ-ℕ n)
--   inl-Path-to-a a n =
--     inl-standard-pushout
--       ( span-diagram-path-to-a a n)

--   concat-inv-s :
--     (s : spanning-type-span-diagram 𝒮) →
--     (n : ℕ) →
--     Path-to-b (right-map-span-diagram 𝒮 s) n →
--     Path-to-a (left-map-span-diagram 𝒮 s) n
--   concat-inv-s s n = pr1 (pr2 (pr2 (stage-zigzag-construction-id-pushout n))) s

--   concat-s :
--     (s : spanning-type-span-diagram 𝒮) →
--     (n : ℕ) →
--     Path-to-a (left-map-span-diagram 𝒮 s) n →
--     Path-to-b (right-map-span-diagram 𝒮 s) (succ-ℕ n)
--   concat-s s n p =
--     inr-standard-pushout
--       ( span-diagram-path-to-b (right-map-span-diagram 𝒮 s) n)
--       ( s , refl , p)

--   right-sequential-diagram-zigzag-id-pushout :
--     codomain-span-diagram 𝒮 →
--     sequential-diagram (l1 ⊔ l2 ⊔ l3)
--   pr1 (right-sequential-diagram-zigzag-id-pushout b) = Path-to-b b
--   pr2 (right-sequential-diagram-zigzag-id-pushout b) = inl-Path-to-b b

--   left-sequential-diagram-zigzag-id-pushout :
--     domain-span-diagram 𝒮 →
--     sequential-diagram (l1 ⊔ l2 ⊔ l3)
--   pr1 (left-sequential-diagram-zigzag-id-pushout a) = Path-to-a a
--   pr2 (left-sequential-diagram-zigzag-id-pushout a) = inl-Path-to-a a

--   zigzag-sequential-diagram-zigzag-id-pushout :
--     (s : spanning-type-span-diagram 𝒮) →
--     zigzag-sequential-diagram
--       ( left-sequential-diagram-zigzag-id-pushout
--         ( left-map-span-diagram 𝒮 s))
--       ( shift-once-sequential-diagram
--         ( right-sequential-diagram-zigzag-id-pushout
--           ( right-map-span-diagram 𝒮 s)))
--   pr1 (zigzag-sequential-diagram-zigzag-id-pushout s) =
--     concat-s s
--   pr1 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout s)) n =
--     concat-inv-s s (succ-ℕ n)
--   pr1 (pr2 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout s))) n p =
--     glue-standard-pushout
--       ( span-diagram-path-to-a (left-map-span-diagram 𝒮 s) n)
--       ( s , refl , p)
--   pr2 (pr2 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout s))) n p =
--     glue-standard-pushout
--       ( span-diagram-path-to-b (right-map-span-diagram 𝒮 s) (succ-ℕ n))
--       ( s , refl , p)

--   left-id-pushout : domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
--   left-id-pushout a =
--     standard-sequential-colimit (left-sequential-diagram-zigzag-id-pushout a)

--   refl-id-pushout : left-id-pushout a₀
--   refl-id-pushout =
--     map-cocone-standard-sequential-colimit 0 (map-raise refl)

--   right-id-pushout : codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
--   right-id-pushout b =
--     standard-sequential-colimit (right-sequential-diagram-zigzag-id-pushout b)

--   equiv-id-pushout :
--     (s : spanning-type-span-diagram 𝒮) →
--     left-id-pushout (left-map-span-diagram 𝒮 s) ≃
--     right-id-pushout (right-map-span-diagram 𝒮 s)
--   equiv-id-pushout s =
--     equiv-colimit-zigzag-sequential-diagram _ _
--       ( up-standard-sequential-colimit)
--       ( up-shift-cocone-sequential-diagram 1 up-standard-sequential-colimit)
--       ( zigzag-sequential-diagram-zigzag-id-pushout s)

--   -- concat-inv-s-inf :
--   --   (s : spanning-type-span-diagram 𝒮) →
--   --   right-id-pushout (right-map-span-diagram 𝒮 s) →
--   --   left-id-pushout (left-map-span-diagram 𝒮 s)
--   -- concat-inv-s-inf s =
--   --   map-inv-equiv (equiv-id-pushout s)

--   concat-s-inf :
--     (s : spanning-type-span-diagram 𝒮) →
--     left-id-pushout (left-map-span-diagram 𝒮 s) →
--     right-id-pushout (right-map-span-diagram 𝒮 s)
--   concat-s-inf s =
--     map-equiv (equiv-id-pushout s)

--   descent-data-zigzag-id-pushout : descent-data-pushout 𝒮 (l1 ⊔ l2 ⊔ l3)
--   pr1 descent-data-zigzag-id-pushout = left-id-pushout
--   pr1 (pr2 descent-data-zigzag-id-pushout) = right-id-pushout
--   pr2 (pr2 descent-data-zigzag-id-pushout) = equiv-id-pushout
-- ```

-- ## Theorem

-- ### TODO

-- ```agda
-- nat-lemma :
--   {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
--   {P : A → UU l3} {Q : B → UU l4}
--   (f : A → B) (h : (a : A) → P a → Q (f a))
--   {x y : A} {p : x ＝ y}
--   {q : f x ＝ f y} (α : ap f p ＝ q) →
--   coherence-square-maps
--     ( tr P p)
--     ( h x)
--     ( h y)
--     ( tr Q q)
-- nat-lemma f h {p = p} refl x = substitution-law-tr _ f p ∙ inv (preserves-tr h p x)

-- apd-lemma :
--   {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
--   (f : (a : A) → B a) (g : (a : A) → B a → C a) {x y : A} (p : x ＝ y) →
--   apd (λ a → g a (f a)) p ＝ inv (preserves-tr g p (f x)) ∙ ap (g y) (apd f p)
-- apd-lemma f g refl = refl

-- lem :
--   {l : Level} {X : UU l} {x y z u v : X} →
--   (p : y ＝ x) (q : y ＝ z) (r : z ＝ u) (s : x ＝ v) (t : u ＝ v) →
--   (inv p ∙ (q ∙ r) ＝ s ∙ inv t) → q ∙ r ∙ t ＝ p ∙ s
-- lem refl q r refl refl x = right-unit ∙ x

-- module _
--   {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
--   {X : UU l4} {c : cocone-span-diagram 𝒮 X}
--   (up-c : universal-property-pushout _ _ c)
--   (a₀ : domain-span-diagram 𝒮)
--   where

--   module _
--     {l5 : Level}
--     (R : descent-data-pushout
--       ( span-diagram-flattening-descent-data-pushout
--         ( descent-data-zigzag-id-pushout 𝒮 a₀))
--       ( l5))
--     (r₀ : left-family-descent-data-pushout R (a₀ , refl-id-pushout 𝒮 a₀))
--     where

--     private
--       CB :
--         (s : spanning-type-span-diagram 𝒮) →
--         (n : ℕ) →
--         (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
--         concat-s-inf 𝒮 a₀ s
--           ( map-cocone-standard-sequential-colimit n p) ＝
--         map-cocone-standard-sequential-colimit (succ-ℕ n)
--           ( concat-s 𝒮 a₀ s n p)
--       CB s =
--         htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--           ( up-standard-sequential-colimit)
--           ( shift-once-cocone-sequential-diagram
--             ( cocone-standard-sequential-colimit
--               ( right-sequential-diagram-zigzag-id-pushout 𝒮 a₀ (right-map-span-diagram 𝒮 s))))
--           ( hom-diagram-zigzag-sequential-diagram
--             ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))

--       Ψ :
--         (s : spanning-type-span-diagram 𝒮) →
--         (n : ℕ) →
--         (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
--         left-family-descent-data-pushout R
--           ( left-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit n p) →
--         right-family-descent-data-pushout R
--           ( right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-s 𝒮 a₀ s n p))
--       Ψ s n p =
--         ( tr
--           ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
--           ( CB s n p)) ∘
--         ( map-family-descent-data-pushout R
--           ( s , map-cocone-standard-sequential-colimit n p))

--       Φ :
--         (s : spanning-type-span-diagram 𝒮) →
--         (n : ℕ) →
--         (p : Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) (succ-ℕ n)) →
--         right-family-descent-data-pushout R
--           ( right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) p) →
--         right-family-descent-data-pushout R
--           ( right-map-span-diagram 𝒮 s ,
--             concat-s-inf 𝒮 a₀ s (map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))
--       Φ s n p =
--         ( tr
--           ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
--           ( inv (CB s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))) ∘
--         ( tr
--           ( λ p →
--             right-family-descent-data-pushout R
--               ( right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
--           ( glue-pushout _ _ (s , refl , p))) ∘
--         ( tr
--           ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
--           ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) p))

--       Φ' :
--         (s : spanning-type-span-diagram 𝒮) →
--         (n : ℕ) →
--         (p : Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) (succ-ℕ n)) →
--         right-family-descent-data-pushout R
--           ( right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) p) →
--         left-family-descent-data-pushout R
--           ( left-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p))
--       Φ' s n p =
--         ( inv-map-family-descent-data-pushout R
--           ( s , map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p))) ∘
--         ( Φ s n p)

--     coh-dep-cocone-a :
--       (s : spanning-type-span-diagram 𝒮) (n : ℕ) →
--       (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
--       coherence-square-maps
--         ( ( tr
--             ( λ p →
--               left-family-descent-data-pushout R
--                 ( left-map-span-diagram 𝒮 s ,
--                   map-cocone-standard-sequential-colimit (succ-ℕ n) p))
--             ( glue-pushout _ _ (s , refl , p))) ∘
--           ( tr
--             ( ev-pair
--               ( left-family-descent-data-pushout R)
--               ( left-map-span-diagram 𝒮 s))
--             ( coherence-cocone-standard-sequential-colimit n p)))
--         ( map-family-descent-data-pushout R
--           ( s , map-cocone-standard-sequential-colimit n p))
--         ( map-family-descent-data-pushout R
--           ( s ,
--             map-cocone-standard-sequential-colimit (succ-ℕ n)
--               ( concat-inv-s 𝒮 a₀ s (succ-ℕ n) ( concat-s 𝒮 a₀ s n p))))
--         ( ( tr
--             ( ev-pair
--               ( right-family-descent-data-pushout R)
--               ( right-map-span-diagram 𝒮 s))
--             ( inv (CB s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) (concat-s 𝒮 a₀ s n p))))) ∘
--           ( tr
--             ( λ p →
--               right-family-descent-data-pushout R
--                 ( right-map-span-diagram 𝒮 s ,
--                   map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
--             ( glue-pushout _ _ (s , refl , concat-s 𝒮 a₀ s n p))) ∘
--           ( tr
--             ( ev-pair
--               ( right-family-descent-data-pushout R)
--               ( right-map-span-diagram 𝒮 s))
--             ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) (concat-s 𝒮 a₀ s n p))) ∘
--           ( tr
--             ( ev-pair
--               ( right-family-descent-data-pushout R)
--               ( right-map-span-diagram 𝒮 s))
--             ( CB s n p)))
--     coh-dep-cocone-a s n p =
--       ( ( inv-htpy
--           ( ( tr-concat _ _) ∙h
--             ( ( tr _ _) ·l
--               ( ( tr-concat _ _) ∙h
--                 ( horizontal-concat-htpy
--                   ( λ _ → substitution-law-tr _ _ _)
--                   ( tr-concat _ _)))))) ·r
--         ( map-family-descent-data-pushout R
--           ( s , map-cocone-standard-sequential-colimit n p))) ∙h
--       ( nat-lemma
--           ( concat-s-inf 𝒮 a₀ s)
--           ( ev-pair (map-family-descent-data-pushout R) s)
--           ( [i] p)) ∙h
--       ( ( map-family-descent-data-pushout R
--           ( s ,
--             map-cocone-standard-sequential-colimit
--               ( succ-ℕ n)
--               ( concat-inv-s 𝒮 a₀ s
--                 ( succ-ℕ n)
--                 ( concat-s 𝒮 a₀ s n p)))) ·l
--         ( ( tr-concat _ _) ∙h
--           ( λ q → substitution-law-tr _ _ _)))
--       where
--       [i] :
--         ( ( concat-s-inf 𝒮 a₀ s) ·l
--           ( ( coherence-cocone-standard-sequential-colimit n) ∙h
--             ( ( map-cocone-standard-sequential-colimit
--               { A =
--                 left-sequential-diagram-zigzag-id-pushout 𝒮 a₀
--                   ( left-map-span-diagram 𝒮 s)}
--               ( succ-ℕ n)) ·l
--             ( λ p → glue-pushout _ _ (s , refl , p))))) ~
--         ( ( CB s n) ∙h
--           ( ( coherence-cocone-standard-sequential-colimit (succ-ℕ n)) ·r
--               ( concat-s 𝒮 a₀ s n)) ∙h
--           ( ( map-cocone-standard-sequential-colimit
--               { A =
--                 right-sequential-diagram-zigzag-id-pushout 𝒮 a₀
--                   ( right-map-span-diagram 𝒮 s)}
--               ( succ-ℕ (succ-ℕ n))) ·l
--             ( λ p → glue-pushout _ _ ( s , refl , concat-s 𝒮 a₀ s n p))) ∙h
--           ( ( inv-htpy (CB s (succ-ℕ n))) ·r
--             ( concat-inv-s 𝒮 a₀ s (succ-ℕ n) ∘ concat-s 𝒮 a₀ s n)))
--       [i] =
--         ( distributive-left-whisker-comp-concat _ _ _) ∙h
--         ( right-transpose-htpy-concat _ _ _
--           ( ( left-whisker-concat-coherence-square-homotopies _ _ _ _ _
--               ( λ p →
--                 inv
--                   ( nat-coherence-square-maps _ _ _ _
--                     ( CB s (succ-ℕ n))
--                     ( glue-pushout _ _ (s , refl , p))))) ∙h
--             ( map-inv-equiv
--               ( equiv-right-transpose-htpy-concat _ _ _)
--               ( ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--                   ( up-standard-sequential-colimit)
--                   ( shift-once-cocone-sequential-diagram
--                     ( cocone-standard-sequential-colimit
--                       ( right-sequential-diagram-zigzag-id-pushout 𝒮 a₀
--                         ( right-map-span-diagram 𝒮 s))))
--                   ( hom-diagram-zigzag-sequential-diagram
--                     ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))
--                   ( n)) ∙h
--                 ( ap-concat-htpy
--                   ( CB s n)
--                   ( ( ap-concat-htpy _
--                       ( ( distributive-left-whisker-comp-concat
--                           ( map-cocone-standard-sequential-colimit
--                             { A =
--                               right-sequential-diagram-zigzag-id-pushout 𝒮 a₀
--                                 ( right-map-span-diagram 𝒮 s)}
--                             ( succ-ℕ (succ-ℕ n)))
--                           ( _)
--                           ( _)) ∙h
--                         ( ap-concat-htpy _
--                           ( ( left-whisker-comp² _
--                               ( left-whisker-inv-htpy _ _)) ∙h
--                             ( left-whisker-inv-htpy _ _))))) ∙h
--                     ( inv-htpy-assoc-htpy _ _ _))) ∙h
--                 ( inv-htpy-assoc-htpy _ _ _))))) ∙h
--         ( ap-concat-htpy' _
--           ( inv-htpy-assoc-htpy _ _ _))

--     α :
--       (s : spanning-type-span-diagram 𝒮) →
--       (n : ℕ) →
--       (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
--       coherence-square-maps
--         ( Ψ s n p)
--         ( tr
--           ( ev-pair
--             ( left-family-descent-data-pushout R)
--             ( left-map-span-diagram 𝒮 s))
--           ( coherence-cocone-standard-sequential-colimit n p))
--         ( Φ' s n (concat-s 𝒮 a₀ s n p))
--         ( tr
--           ( λ p →
--             left-family-descent-data-pushout R
--               ( left-map-span-diagram 𝒮 s ,
--                 map-cocone-standard-sequential-colimit (succ-ℕ n) p))
--           ( glue-pushout _ _ (s , refl , p)))
--     α s n p q =
--       map-eq-transpose-equiv
--         ( equiv-family-descent-data-pushout R
--           ( s ,
--             map-cocone-standard-sequential-colimit
--               ( succ-ℕ n)
--               ( concat-inv-s 𝒮 a₀ s
--                 ( succ-ℕ n)
--                 ( concat-s 𝒮 a₀ s n p))))
--         ( inv (coh-dep-cocone-a s n p q))

--     β :
--       (s : spanning-type-span-diagram 𝒮) →
--       (n : ℕ) →
--       (p : Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) (succ-ℕ n)) →
--       coherence-square-maps
--         ( Φ' s n p)
--         ( tr
--           ( ev-pair
--             ( right-family-descent-data-pushout R)
--             ( right-map-span-diagram 𝒮 s))
--           ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) p))
--         ( Ψ s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p))
--         ( tr
--           ( λ p →
--             right-family-descent-data-pushout R
--               ( right-map-span-diagram 𝒮 s ,
--                 map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
--           ( glue-pushout _ _ (s , refl , p)))
--     β s n p q =
--       inv
--         ( ( ap
--             ( tr _ _)
--             ( is-section-map-inv-equiv
--               ( equiv-family-descent-data-pushout R
--                 ( s , map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))
--               ( _)) ∙
--           ( is-section-map-inv-equiv
--             ( equiv-tr _ _)
--             ( _))))

--     -- Note for refactoring: after contracting away the last component and the
--     -- vertical map, the definition of prism2 will fail to typecheck, since
--     -- currently the coherence computes to <X> ∙ refl, which needs to be taken
--     -- into account; contracting away this data would simplify the later
--     -- homotopy algebra.
--     stages-cocones' :
--       (n : ℕ) →
--       Σ ( (b : codomain-span-diagram 𝒮) →
--           dependent-cocone-span-diagram
--             ( cocone-pushout-span-diagram
--               ( span-diagram-path-to-b 𝒮 a₀ b n))
--             ( λ p →
--               right-family-descent-data-pushout R
--                 ( b , map-cocone-standard-sequential-colimit (succ-ℕ n) p)))
--         ( λ dep-cocone-b →
--           Σ ( (a : domain-span-diagram 𝒮) →
--               dependent-cocone-span-diagram
--                 ( cocone-pushout-span-diagram
--                   ( span-diagram-path-to-a 𝒮 a₀ a n))
--                 ( λ p →
--                   left-family-descent-data-pushout R
--                     ( a , map-cocone-standard-sequential-colimit (succ-ℕ n) p)))
--             ( λ dep-cocone-a →
--               (s : spanning-type-span-diagram 𝒮) →
--               (p : Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) (succ-ℕ n)) →
--               vertical-map-dependent-cocone _ _ _ _
--                 ( dep-cocone-a (left-map-span-diagram 𝒮 s))
--                 ( s , refl , p) ＝
--               Φ' s n p (dependent-cogap _ _ (dep-cocone-b (right-map-span-diagram 𝒮 s)) p)))
--     stages-cocones' zero-ℕ =
--       dep-cocone-b ,
--       dep-cocone-a ,
--       λ s p → refl
--       where
--       dep-cocone-b :
--         (b : codomain-span-diagram 𝒮) →
--         dependent-cocone-span-diagram
--           ( cocone-pushout-span-diagram (span-diagram-path-to-b 𝒮 a₀ b 0))
--           ( λ p →
--             right-family-descent-data-pushout R
--               ( b , map-cocone-standard-sequential-colimit 1 p))
--       pr1 (dep-cocone-b b) (map-raise ())
--       pr1 (pr2 (dep-cocone-b ._)) (s , refl , map-raise refl) =
--         tr
--           ( ev-pair
--             ( right-family-descent-data-pushout R)
--             ( right-map-span-diagram 𝒮 s))
--           ( CB s 0 (map-raise refl))
--           ( map-family-descent-data-pushout R
--             ( s , map-cocone-standard-sequential-colimit 0 (map-raise refl))
--             ( r₀))
--       pr2 (pr2 (dep-cocone-b ._)) (s , refl , map-raise ())
--       dep-cocone-a :
--         (a : domain-span-diagram 𝒮) →
--         dependent-cocone-span-diagram
--           ( cocone-pushout-span-diagram (span-diagram-path-to-a 𝒮 a₀ a 0))
--           ( λ p →
--             left-family-descent-data-pushout R
--               ( a , map-cocone-standard-sequential-colimit 1 p))
--       pr1 (dep-cocone-a .a₀) (map-raise refl) =
--         tr
--           ( ev-pair (left-family-descent-data-pushout R) a₀)
--           ( coherence-cocone-standard-sequential-colimit 0 (map-raise refl))
--           ( r₀)
--       pr1 (pr2 (dep-cocone-a a)) (s , refl , p) =
--         Φ' s 0 p (dependent-cogap _ _ (dep-cocone-b (right-map-span-diagram 𝒮 s)) p)
--       pr2 (pr2 (dep-cocone-a .a₀)) (s , refl , map-raise refl) =
--         ( α s 0 (map-raise refl) r₀) ∙
--         ( ap
--           ( Φ' s 0 _)
--           ( inv
--             ( compute-inr-dependent-cogap _ _
--               ( dep-cocone-b (right-map-span-diagram 𝒮 s))
--               ( s , refl , map-raise refl))))
--     stages-cocones' (succ-ℕ n) =
--       dep-cocone-b ,
--       dep-cocone-a ,
--       λ s p → refl
--       where
--       dep-cocone-b :
--         (b : codomain-span-diagram 𝒮) →
--         dependent-cocone-span-diagram
--           ( cocone-pushout-span-diagram (span-diagram-path-to-b 𝒮 a₀ b (succ-ℕ n)))
--           ( λ p →
--             right-family-descent-data-pushout R
--               ( b , map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
--       pr1 (dep-cocone-b b) p =
--         tr
--           ( ev-pair (right-family-descent-data-pushout R) b)
--           ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) p)
--           ( dependent-cogap _ _ (pr1 (stages-cocones' n) b) p)
--       pr1 (pr2 (dep-cocone-b b)) (s , refl , p) =
--         tr
--           ( ev-pair
--             ( right-family-descent-data-pushout R)
--             ( right-map-span-diagram 𝒮 s))
--           ( CB s (succ-ℕ n) p)
--           ( map-family-descent-data-pushout R
--             ( s , map-cocone-standard-sequential-colimit (succ-ℕ n) p)
--             ( dependent-cogap _ _ (pr1 (pr2 (stages-cocones' n)) (left-map-span-diagram 𝒮 s)) p))
--       pr2 (pr2 (dep-cocone-b b)) (s , refl , p) =
--         ( β s n p _) ∙
--         ( ap
--           ( Ψ s (succ-ℕ n) _)
--           ( inv
--             ( ( compute-inr-dependent-cogap _ _
--                 ( pr1 (pr2 (stages-cocones' n)) (left-map-span-diagram 𝒮 s))
--                 ( s , refl , p)) ∙
--               ( pr2 (pr2 (stages-cocones' n)) s p))))
--       dep-cocone-a :
--         (a : domain-span-diagram 𝒮) →
--         dependent-cocone-span-diagram
--           ( cocone-pushout-span-diagram (span-diagram-path-to-a 𝒮 a₀ a (succ-ℕ n)))
--           ( λ p →
--             left-family-descent-data-pushout R
--               ( a , map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
--       pr1 (dep-cocone-a a) p =
--         tr
--           ( ev-pair (left-family-descent-data-pushout R) a)
--           ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) p)
--           ( dependent-cogap _ _ (pr1 (pr2 (stages-cocones' n)) a) p)
--       pr1 (pr2 (dep-cocone-a a)) (s , refl , p) =
--         Φ' s (succ-ℕ n) p (dependent-cogap _ _ (dep-cocone-b (right-map-span-diagram 𝒮 s)) p)
--       pr2 (pr2 (dep-cocone-a a)) (s , refl , p) =
--         ( α s (succ-ℕ n) p _) ∙
--         ( ap
--           ( Φ' s (succ-ℕ n) _)
--           ( inv
--             ( compute-inr-dependent-cogap _ _
--               ( dep-cocone-b (right-map-span-diagram 𝒮 s))
--               ( s , refl , p))))


--     tB :
--       (b : codomain-span-diagram 𝒮) (n : ℕ) (p : Path-to-b 𝒮 a₀ b n) →
--       right-family-descent-data-pushout R
--         ( b , map-cocone-standard-sequential-colimit n p)
--     tB b zero-ℕ (map-raise ())
--     tB b (succ-ℕ n) = dependent-cogap _ _ (pr1 (stages-cocones' n) b)

--     tA :
--       (a : domain-span-diagram 𝒮) (n : ℕ) (p : Path-to-a 𝒮 a₀ a n) →
--       left-family-descent-data-pushout R
--         ( a , map-cocone-standard-sequential-colimit n p)
--     tA .a₀ zero-ℕ (map-raise refl) = r₀
--     tA a (succ-ℕ n) = dependent-cogap _ _ (pr1 (pr2 (stages-cocones' n)) a)

--     ind-singleton-zigzag-id-pushout' : section-descent-data-pushout R
--     pr1 ind-singleton-zigzag-id-pushout' (a , p) =
--       dependent-cogap-standard-sequential-colimit
--         ( tA a , KA)
--         ( p)
--       where
--       KA :
--         (n : ℕ) (p : Path-to-a 𝒮 a₀ a n) →
--         dependent-identification
--           ( ev-pair (left-family-descent-data-pushout R) a)
--           ( coherence-cocone-standard-sequential-colimit n p)
--           ( tA a n p)
--           ( tA a (succ-ℕ n) (inl-Path-to-a 𝒮 a₀ a n p))
--       KA zero-ℕ (map-raise refl) =
--         inv
--           ( compute-inl-dependent-cogap _ _
--             ( pr1 (pr2 (stages-cocones' 0)) a)
--             ( map-raise refl))
--       KA (succ-ℕ n) p =
--         inv
--           ( compute-inl-dependent-cogap _ _
--             ( pr1 (pr2 (stages-cocones' (succ-ℕ n))) a)
--             ( p))
--     pr1 (pr2 ind-singleton-zigzag-id-pushout') (b , p) =
--       dependent-cogap-standard-sequential-colimit
--         ( tB b , KB)
--         ( p)
--       where
--       KB :
--         (n : ℕ) (p : Path-to-b 𝒮 a₀ b n) →
--         dependent-identification
--           ( ev-pair (right-family-descent-data-pushout R) b)
--           ( coherence-cocone-standard-sequential-colimit n p)
--           ( tB b n p)
--           ( tB b (succ-ℕ n) (inl-Path-to-b 𝒮 a₀ b n p))
--       KB zero-ℕ (map-raise ())
--       KB (succ-ℕ n) p =
--         inv
--           ( compute-inl-dependent-cogap _ _
--             ( pr1 (stages-cocones' (succ-ℕ n)) b)
--             ( p))
--     pr2 (pr2 ind-singleton-zigzag-id-pushout') (s , p) =
--       dependent-cogap-standard-sequential-colimit
--         ( tS , KS)
--         ( p)
--       where
--       [i] :
--         (n : ℕ) (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
--         tr
--           ( ev-pair
--             ( right-family-descent-data-pushout R)
--             ( right-map-span-diagram 𝒮 s))
--           ( CB s n p)
--           ( map-family-descent-data-pushout R
--             ( s , map-cocone-standard-sequential-colimit n p)
--             ( tA (left-map-span-diagram 𝒮 s) n p)) ＝
--         tB (right-map-span-diagram 𝒮 s) (succ-ℕ n) (concat-s 𝒮 a₀ s n p)
--       [i] zero-ℕ (map-raise refl) = inv (compute-inr-dependent-cogap _ _ _ _)
--       [i] (succ-ℕ n) p = inv (compute-inr-dependent-cogap _ _ _ _)
--       tS :
--         (n : ℕ) (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
--         map-family-descent-data-pushout R
--           ( s , map-cocone-standard-sequential-colimit n p)
--           ( pr1
--             ( ind-singleton-zigzag-id-pushout')
--             ( left-map-span-diagram 𝒮 s ,
--               map-cocone-standard-sequential-colimit n p)) ＝
--         pr1
--           ( pr2 ind-singleton-zigzag-id-pushout')
--           ( right-map-span-diagram 𝒮 s ,
--             concat-s-inf 𝒮 a₀ s (map-cocone-standard-sequential-colimit n p))
--       tS n p =
--         ( ap
--           ( map-family-descent-data-pushout R
--             ( s , map-cocone-standard-sequential-colimit n p))
--           ( compute-incl-dependent-cogap-standard-sequential-colimit _ n p)) ∙
--         ( map-equiv
--           ( inv-equiv-ap-emb
--             ( emb-equiv
--               ( equiv-tr
--                 ( ev-pair
--                   ( right-family-descent-data-pushout R)
--                   ( right-map-span-diagram 𝒮 s))
--                 ( CB s n p))))
--           ( [i] n p ∙
--             inv
--               ( ( apd
--                   ( dependent-cogap-standard-sequential-colimit (tB (right-map-span-diagram 𝒮 s) , _))
--                   ( CB s n p)) ∙
--                 ( compute-incl-dependent-cogap-standard-sequential-colimit _ (succ-ℕ n) _))))
--       KS :
--         (n : ℕ) (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
--         tr
--           ( λ p →
--             map-family-descent-data-pushout R
--               ( s , p)
--               ( pr1
--                 ( ind-singleton-zigzag-id-pushout')
--                 ( left-map-span-diagram 𝒮 s , p)) ＝
--             pr1 (pr2 ind-singleton-zigzag-id-pushout') (right-map-span-diagram 𝒮 s , concat-s-inf 𝒮 a₀ s p))
--           ( coherence-cocone-standard-sequential-colimit n p)
--           ( tS n p) ＝
--         tS (succ-ℕ n) (inl-Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n p)
--       KS n p =
--         map-compute-dependent-identification-eq-value _ _
--           ( coherence-cocone-standard-sequential-colimit n p)
--           ( _)
--           ( _)
--           ( {!!})

--     tS-in-diagram :
--       (s : spanning-type-span-diagram 𝒮) (n : ℕ) →
--       (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
--       ( tr (ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
--         ( CB s n p)
--         ( map-family-descent-data-pushout R _ (tA (left-map-span-diagram 𝒮 s) n p))) ＝
--       ( tB (right-map-span-diagram 𝒮 s) (succ-ℕ n) (concat-s 𝒮 a₀ s n p))
--     tS-in-diagram s zero-ℕ (map-raise refl) = inv (compute-inr-dependent-cogap _ _ _ _)
--     tS-in-diagram s (succ-ℕ n) p = inv (compute-inr-dependent-cogap _ _ _ _)

--     module vertices
--       (s : spanning-type-span-diagram 𝒮)
--       where
--       PAn : (n : ℕ) → UU (l1 ⊔ l2 ⊔ l3)
--       PAn = Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s)
--       QAn : {n : ℕ} → PAn n → UU l5
--       QAn {n} p = left-family-descent-data-pushout R (left-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit n p)
--       PBn : (n : ℕ) → UU (l1 ⊔ l2 ⊔ l3)
--       PBn = Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) ∘ succ-ℕ
--       QBn : {n : ℕ} → PBn n → UU l5
--       QBn {n} p = right-family-descent-data-pushout R (right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) p)
--       fn : {n : ℕ} → PAn n → PBn n
--       fn = concat-s 𝒮 a₀ s _
--       gn : {n : ℕ} → PAn n → PAn (succ-ℕ n)
--       gn = inl-Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) _
--       hn : {n : ℕ} → PBn n → PBn (succ-ℕ n)
--       hn = inl-Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) _
--       mn : {n : ℕ} → PBn n → PAn (succ-ℕ n)
--       mn {n} = concat-inv-s 𝒮 a₀ s (succ-ℕ n)
--       sAn : {n : ℕ} (p : PAn n) → QAn p
--       sAn = tA (left-map-span-diagram 𝒮 s) _
--       sBn : {n : ℕ} (p : PBn n) → QBn p
--       sBn = tB (right-map-span-diagram 𝒮 s) _
--       f'n : {n : ℕ} {p : PAn n} → QAn p → QBn (fn p)
--       f'n {n} {p} = Ψ s n p
--       g'n : {n : ℕ} {p : PAn n} → QAn p → QAn (gn p)
--       g'n {n} {p} =
--         tr
--           ( ev-pair
--             ( left-family-descent-data-pushout R)
--             ( left-map-span-diagram 𝒮 s))
--           ( coherence-cocone-standard-sequential-colimit n p)
--       h'n : {n : ℕ} {p : PBn n} → QBn p → QBn (hn p)
--       h'n {n} {p} =
--         tr
--           ( ev-pair
--             ( right-family-descent-data-pushout R)
--             ( right-map-span-diagram 𝒮 s))
--           ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) p)
--       m'n : {n : ℕ} {p : PBn n} → QBn p → QAn (mn p)
--       m'n = Φ' s _ _

--     module sides
--       (s : spanning-type-span-diagram 𝒮) (n : ℕ)
--       where
--       open vertices s
--       left :
--         {p : PAn n} → f'n (sAn p) ＝ sBn (fn p)
--       left = tS-in-diagram s n _
--       right :
--         {p : PAn (succ-ℕ n)} →
--         f'n (sAn p) ＝ sBn (fn p)
--       right = tS-in-diagram s (succ-ℕ n) _
--       bottom :
--         {p : PAn n} → hn (fn p) ＝ fn (gn p)
--       bottom =
--         naturality-map-hom-diagram-zigzag-sequential-diagram
--           ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s)
--           ( n)
--           ( _)
--       bottom1 :
--         {p : PAn n} → gn p ＝ mn (fn p)
--       bottom1 = glue-pushout _ _ _
--       bottom2 :
--         {p : PBn n} → hn p ＝ fn (mn p)
--       bottom2 = glue-pushout _ _ _
--       far :
--         {p : PAn n} → g'n (sAn p) ＝ sAn (gn p)
--       far = far' n _
--         where
--         far' : (n : ℕ) (p : PAn n) → g'n (sAn p) ＝ sAn (gn p)
--         far' zero-ℕ (map-raise refl) = inv (compute-inl-dependent-cogap _ _ _ _)
--         far' (succ-ℕ n) p = inv (compute-inl-dependent-cogap _ _ _ _)
--       near :
--         {p : PBn n} → h'n (sBn p) ＝ sBn (hn p)
--       near = inv (compute-inl-dependent-cogap _ _ _ _)
--       mid :
--         {p : PBn n} → m'n (sBn p) ＝ sAn (mn p)
--       mid = mid' _ _
--         where
--         mid' : (n : ℕ) (p : PBn n) → m'n (sBn p) ＝ sAn (mn p)
--         mid' zero-ℕ p = inv (compute-inr-dependent-cogap _ _ _ _)
--         mid' (succ-ℕ n) p = inv (compute-inr-dependent-cogap _ _ _ _)
--       top1 :
--         {p : PAn n} (q : QAn p) →
--         tr QAn bottom1 (g'n q) ＝ m'n (f'n q)
--       top1 = α s n _
--       top2 :
--         {p : PBn n} (q : QBn p) →
--         tr QBn bottom2 (h'n q) ＝ f'n (m'n q)
--       top2 = β s n _
--       top :
--         {p : PAn n} (q : QAn p) →
--         tr QBn bottom (h'n (f'n q)) ＝ f'n (g'n q)
--       top = {!!}

--     module CUBE
--       (s : spanning-type-span-diagram 𝒮) (n : ℕ)
--       where
--       open vertices s
--       open sides s n

--       CUBE : (p : PAn n) → UU _
--       CUBE p =
--         ( top (sAn p) ∙ ap f'n far ∙ right) ＝
--         ( ap (tr QBn bottom ∘ h'n) left ∙
--           ap (tr QBn bottom) near ∙
--           apd sBn bottom)

--       PRISM1 : (p : PAn n) → UU _
--       PRISM1 p =
--         ( top1 (sAn p) ∙ ap m'n left ∙ mid) ＝
--         ( ap (tr QAn bottom1) far ∙ apd sAn bottom1)

--       PRISM2 : (p : PBn n) → UU _
--       PRISM2 p =
--         top2 (sBn p) ∙ ap f'n mid ∙ right ＝
--         ap (tr QBn bottom2) near ∙ apd sBn bottom2

--     module cube
--       (s : spanning-type-span-diagram 𝒮)
--       where abstract
--       open vertices s
--       open sides s
--       open CUBE s

--       -- THE COMMENTED CODE WORKS, DON'T DELETE IT!
--       -- It just takes too long to typecheck it in its current state
--       prism1 : (n : ℕ) → (p : PAn n) → PRISM1 n p
--       prism1 = {!!}
--       -- prism1 zero-ℕ (map-raise refl) =
--       --   lem _ _ _ _ _
--       --     ( ( ap
--       --         ( _∙ (top1 0 (sAn _) ∙ ap m'n (left 0)))
--       --         ( ( inv (ap-inv (tr QAn (bottom1 0)) (far 0))) ∙
--       --           ( ap² (tr QAn (bottom1 0)) (inv-inv _)))) ∙
--       --       ( [i]) ∙
--       --       ( ap
--       --         ( apd sAn (bottom1 0) ∙_)
--       --         ( inv (inv-inv _))))
--       --   where
--       --     open import foundation.action-on-higher-identifications-functions
--       --     [i] =
--       --       inv
--       --         ( compute-glue-dependent-cogap _ _
--       --           ( pr1 (pr2 (stages-cocones' 0)) (left-map-span-diagram 𝒮 s))
--       --           ( s , refl , (map-raise refl)))
--       -- prism1 (succ-ℕ n) p =
--       --   lem _ _ _ _ _
--       --     ( ( ap
--       --         ( _∙ (top1 (succ-ℕ n) (sAn _) ∙ ap m'n (left (succ-ℕ n))))
--       --         ( ( inv (ap-inv (tr QAn (bottom1 (succ-ℕ n))) (far (succ-ℕ n)))) ∙
--       --           ( ap² (tr QAn (bottom1 (succ-ℕ n))) (inv-inv _)))) ∙
--       --       ( [i]) ∙
--       --       ( ap
--       --         ( apd sAn (bottom1 (succ-ℕ n)) ∙_)
--       --         ( inv (inv-inv _))))
--       --   where
--       --     open import foundation.action-on-higher-identifications-functions
--       --     [i] =
--       --       inv
--       --         ( compute-glue-dependent-cogap _ _
--       --           ( pr1 (pr2 (stages-cocones' (succ-ℕ n))) (left-map-span-diagram 𝒮 s))
--       --           ( s , refl , p))

--       prism2 : (n : ℕ) → (p : PBn n) → PRISM2 n p
--       prism2 = {!!}
--       -- prism2 0 p =
--       --   lem _ _ _ _ _
--       --     ( ( ap
--       --         ( _∙ (top2 0 (sBn p) ∙ ap f'n (mid 0)))
--       --         ( ( inv (ap-inv (tr QBn (bottom2 0)) (near 0))) ∙
--       --           ( ap² (tr (QBn {1}) (bottom2 0)) (inv-inv _)))) ∙
--       --       ( inv [ii]) ∙
--       --       ( ap
--       --         ( apd sBn (bottom2 0) ∙_)
--       --         ( inv (inv-inv _))))
--       --   where
--       --     open import foundation.action-on-higher-identifications-functions
--       --     [i] =
--       --       -- inv
--       --         ( compute-glue-dependent-cogap _ _
--       --           ( pr1 (stages-cocones' 1) (right-map-span-diagram 𝒮 s))
--       --           ( s , refl , p))
--       --     [ii] = [i] ∙ ap (λ q → ap (tr QBn _) (compute-inl-dependent-cogap _ _ _ _) ∙ (top2 0 (sBn p) ∙ ap f'n (inv q))) right-unit
--       -- prism2 (succ-ℕ n) p =
--       --   lem _ _ _ _ _
--       --     ( ( ap
--       --         ( _∙ (top2 (succ-ℕ n) (sBn p) ∙ ap f'n (mid (succ-ℕ n))))
--       --         ( ( inv (ap-inv (tr QBn (bottom2 (succ-ℕ n))) (near (succ-ℕ n)))) ∙
--       --           ( ap² (tr QBn (bottom2 (succ-ℕ n))) (inv-inv _)))) ∙
--       --       ( inv [ii]) ∙
--       --       ( ap
--       --         ( apd sBn (bottom2 (succ-ℕ n)) ∙_)
--       --         ( inv (inv-inv _))))
--       --   where
--       --     open import foundation.action-on-higher-identifications-functions
--       --     [i] =
--       --       -- inv
--       --         ( compute-glue-dependent-cogap _ _
--       --           ( pr1 (stages-cocones' (succ-ℕ (succ-ℕ n))) (right-map-span-diagram 𝒮 s))
--       --           ( s , refl , p))
--       --     [ii] = [i] ∙ ap (λ q → ap (tr QBn _) (compute-inl-dependent-cogap _ _ _ _) ∙ (top2 (succ-ℕ n) (sBn p) ∙ ap f'n (inv q))) right-unit

--       cube :
--         (n : ℕ) → (p : PAn n) → CUBE n p
--       cube = {!!}

--     KS-in-diagram :
--       (s : spanning-type-span-diagram 𝒮) (n : ℕ) →
--       (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
--       sides.top s n (vertices.sAn s p) ∙
--        ap (vertices.f'n s) (sides.far s n)
--        ∙ sides.right s n
--        ＝
--        ap (tr (vertices.QBn s) (sides.bottom s n) ∘ vertices.h'n s)
--        (sides.left s n)
--        ∙ ap (tr (vertices.QBn s) (sides.bottom s n)) (sides.near s n)
--        ∙ apd (vertices.sBn s) (sides.bottom s n)
--     KS-in-diagram = cube.cube

--   is-identity-system-zigzag-id-pushout :
--     is-identity-system-descent-data-pushout
--       ( descent-data-zigzag-id-pushout 𝒮 a₀)
--       ( refl-id-pushout 𝒮 a₀)
--   is-identity-system-zigzag-id-pushout =
--     is-identity-system-descent-data-pushout-ind-singleton up-c
--       ( descent-data-zigzag-id-pushout 𝒮 a₀)
--       ( refl-id-pushout 𝒮 a₀)
--       ( ind-singleton-zigzag-id-pushout')
-- ```
