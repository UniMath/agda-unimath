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
open import synthetic-homotopy-theory.families-descent-data-pushouts
open import synthetic-homotopy-theory.flattening-lemma-pushouts
open import synthetic-homotopy-theory.functoriality-sequential-colimits
open import synthetic-homotopy-theory.functoriality-stuff
open import synthetic-homotopy-theory.identity-systems-descent-data-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.sections-descent-data-pushouts
open import synthetic-homotopy-theory.sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.shifts-sequential-diagrams
open import synthetic-homotopy-theory.stuff-over
open import synthetic-homotopy-theory.universal-property-pushouts
open import synthetic-homotopy-theory.zigzags-sequential-diagrams
```

</details>

## Idea

The identity types of pushouts may be characterized as certain sequential
colimits of pushouts.

## Definitions

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  type-stage-zigzag-construction-id-pushout : ℕ → UU (lsuc (l1 ⊔ l2 ⊔ l3))
  type-stage-zigzag-construction-id-pushout n =
    Σ ( codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3))
      ( λ Path-to-b →
        Σ ( domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3))
          ( λ Path-to-a →
            ( Σ ( (s : spanning-type-span-diagram 𝒮) →
                  Path-to-b (right-map-span-diagram 𝒮 s) →
                  Path-to-a (left-map-span-diagram 𝒮 s))
                ( λ _ →
                  rec-ℕ
                    ( raise-unit (lsuc (l1 ⊔ l2 ⊔ l3)))
                    ( λ _ _ →
                      ( codomain-span-diagram 𝒮 →
                        span-diagram
                          ( l1 ⊔ l2 ⊔ l3)
                          ( l1 ⊔ l2 ⊔ l3)
                          ( l1 ⊔ l2 ⊔ l3)) ×
                      ( domain-span-diagram 𝒮 →
                        span-diagram
                          ( l1 ⊔ l2 ⊔ l3)
                          ( l1 ⊔ l2 ⊔ l3)
                          ( l1 ⊔ l2 ⊔ l3)))
                    ( n)))))

module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  (a₀ : domain-span-diagram 𝒮)
  where

  stage-zigzag-construction-id-pushout :
    (n : ℕ) → type-stage-zigzag-construction-id-pushout 𝒮 n
  stage-zigzag-construction-id-pushout zero-ℕ =
    Path-to-b ,
    Path-to-a ,
    ( λ s → raise-ex-falso _) ,
    raise-star
    where
    Path-to-b : codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
    Path-to-b _ = raise-empty _
    Path-to-a : domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
    Path-to-a a = raise (l2 ⊔ l3) (a₀ ＝ a)
  stage-zigzag-construction-id-pushout (succ-ℕ n) =
    Path-to-b ,
    Path-to-a ,
    ( λ s p → inr-pushout _ _ (s , refl , p)) ,
    span-diagram-B ,
    span-diagram-A
    where
    span-diagram-B :
      codomain-span-diagram 𝒮 →
      span-diagram (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l3)
    span-diagram-B b =
      make-span-diagram
        ( pr2 ∘ pr2)
        ( tot
          ( λ s →
            tot
              ( λ r (p : pr1 (stage-zigzag-construction-id-pushout n) b) →
                pr1
                  ( pr2 (pr2 (stage-zigzag-construction-id-pushout n)))
                  ( s)
                  ( tr (pr1 (stage-zigzag-construction-id-pushout n)) r p))))
    Path-to-b : codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
    Path-to-b b = standard-pushout (span-diagram-B b)
    span-diagram-A :
      domain-span-diagram 𝒮 →
      span-diagram (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l3) (l1 ⊔ l2 ⊔ l3)
    span-diagram-A a =
      make-span-diagram
        ( pr2 ∘ pr2)
        ( tot
          ( λ s →
            tot
              ( λ r (p : pr1 (pr2 (stage-zigzag-construction-id-pushout n)) a) →
                inr-standard-pushout
                  ( span-diagram-B (right-map-span-diagram 𝒮 s))
                  ( ( s) ,
                    ( refl) ,
                    ( tr
                      ( pr1 (pr2 (stage-zigzag-construction-id-pushout n)))
                      ( r)
                      ( p))))))
    Path-to-a : domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
    Path-to-a a = standard-pushout (span-diagram-A a)

  span-diagram-path-to-b :
    codomain-span-diagram 𝒮 → ℕ →
    span-diagram
      ( l1 ⊔ l2 ⊔ l3)
      ( l1 ⊔ l2 ⊔ l3)
      ( l1 ⊔ l2 ⊔ l3)
  span-diagram-path-to-b b n =
    pr1 (pr2 (pr2 (pr2 (stage-zigzag-construction-id-pushout (succ-ℕ n))))) b

  span-diagram-path-to-a :
    domain-span-diagram 𝒮 → ℕ →
    span-diagram
      ( l1 ⊔ l2 ⊔ l3)
      ( l1 ⊔ l2 ⊔ l3)
      ( l1 ⊔ l2 ⊔ l3)
  span-diagram-path-to-a a n =
    pr2 (pr2 (pr2 (pr2 (stage-zigzag-construction-id-pushout (succ-ℕ n))))) a

  Path-to-b : codomain-span-diagram 𝒮 → ℕ → UU (l1 ⊔ l2 ⊔ l3)
  Path-to-b b n = pr1 (stage-zigzag-construction-id-pushout n) b

  Path-to-a : domain-span-diagram 𝒮 → ℕ → UU (l1 ⊔ l2 ⊔ l3)
  Path-to-a a n = pr1 (pr2 (stage-zigzag-construction-id-pushout n)) a

  inl-Path-to-b :
    (b : codomain-span-diagram 𝒮) (n : ℕ) → Path-to-b b n → Path-to-b b (succ-ℕ n)
  inl-Path-to-b b n =
    inl-standard-pushout
      ( span-diagram-path-to-b b n)

  inl-Path-to-a :
    (a : domain-span-diagram 𝒮) (n : ℕ) → Path-to-a a n → Path-to-a a (succ-ℕ n)
  inl-Path-to-a a n =
    inl-standard-pushout
      ( span-diagram-path-to-a a n)

  concat-inv-s :
    (s : spanning-type-span-diagram 𝒮) →
    (n : ℕ) →
    Path-to-b (right-map-span-diagram 𝒮 s) n →
    Path-to-a (left-map-span-diagram 𝒮 s) n
  concat-inv-s s n = pr1 (pr2 (pr2 (stage-zigzag-construction-id-pushout n))) s

  concat-s :
    (s : spanning-type-span-diagram 𝒮) →
    (n : ℕ) →
    Path-to-a (left-map-span-diagram 𝒮 s) n →
    Path-to-b (right-map-span-diagram 𝒮 s) (succ-ℕ n)
  concat-s s n p =
    inr-standard-pushout
      ( span-diagram-path-to-b (right-map-span-diagram 𝒮 s) n)
      ( s , refl , p)

  right-sequential-diagram-zigzag-id-pushout :
    codomain-span-diagram 𝒮 →
    sequential-diagram (l1 ⊔ l2 ⊔ l3)
  pr1 (right-sequential-diagram-zigzag-id-pushout b) = Path-to-b b
  pr2 (right-sequential-diagram-zigzag-id-pushout b) = inl-Path-to-b b

  left-sequential-diagram-zigzag-id-pushout :
    domain-span-diagram 𝒮 →
    sequential-diagram (l1 ⊔ l2 ⊔ l3)
  pr1 (left-sequential-diagram-zigzag-id-pushout a) = Path-to-a a
  pr2 (left-sequential-diagram-zigzag-id-pushout a) = inl-Path-to-a a

  zigzag-sequential-diagram-zigzag-id-pushout :
    (s : spanning-type-span-diagram 𝒮) →
    zigzag-sequential-diagram
      ( left-sequential-diagram-zigzag-id-pushout
        ( left-map-span-diagram 𝒮 s))
      ( shift-once-sequential-diagram
        ( right-sequential-diagram-zigzag-id-pushout
          ( right-map-span-diagram 𝒮 s)))
  pr1 (zigzag-sequential-diagram-zigzag-id-pushout s) =
    concat-s s
  pr1 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout s)) n =
    concat-inv-s s (succ-ℕ n)
  pr1 (pr2 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout s))) n p =
    glue-standard-pushout
      ( span-diagram-path-to-a (left-map-span-diagram 𝒮 s) n)
      ( s , refl , p)
  pr2 (pr2 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout s))) n p =
    glue-standard-pushout
      ( span-diagram-path-to-b (right-map-span-diagram 𝒮 s) (succ-ℕ n))
      ( s , refl , p)

  left-id-pushout : domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
  left-id-pushout a =
    standard-sequential-colimit (left-sequential-diagram-zigzag-id-pushout a)

  refl-id-pushout : left-id-pushout a₀
  refl-id-pushout =
    map-cocone-standard-sequential-colimit 0 (map-raise refl)

  right-id-pushout : codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
  right-id-pushout b =
    standard-sequential-colimit (right-sequential-diagram-zigzag-id-pushout b)

  equiv-id-pushout :
    (s : spanning-type-span-diagram 𝒮) →
    left-id-pushout (left-map-span-diagram 𝒮 s) ≃
    right-id-pushout (right-map-span-diagram 𝒮 s)
  equiv-id-pushout s =
    equiv-colimit-zigzag-sequential-diagram _ _
      ( up-standard-sequential-colimit)
      ( up-shift-cocone-sequential-diagram 1 up-standard-sequential-colimit)
      ( zigzag-sequential-diagram-zigzag-id-pushout s)

  -- concat-inv-s-inf :
  --   (s : spanning-type-span-diagram 𝒮) →
  --   right-id-pushout (right-map-span-diagram 𝒮 s) →
  --   left-id-pushout (left-map-span-diagram 𝒮 s)
  -- concat-inv-s-inf s =
  --   map-inv-equiv (equiv-id-pushout s)

  concat-s-inf :
    (s : spanning-type-span-diagram 𝒮) →
    left-id-pushout (left-map-span-diagram 𝒮 s) →
    right-id-pushout (right-map-span-diagram 𝒮 s)
  concat-s-inf s =
    map-equiv (equiv-id-pushout s)

  descent-data-zigzag-id-pushout : descent-data-pushout 𝒮 (l1 ⊔ l2 ⊔ l3)
  pr1 descent-data-zigzag-id-pushout = left-id-pushout
  pr1 (pr2 descent-data-zigzag-id-pushout) = right-id-pushout
  pr2 (pr2 descent-data-zigzag-id-pushout) = equiv-id-pushout
```

## Theorem

### TODO

```agda
apd-lemma :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (f : (a : A) → B a) (g : (a : A) → B a → C a) {x y : A} (p : x ＝ y) →
  apd (λ a → g a (f a)) p ＝ inv (preserves-tr g p (f x)) ∙ ap (g y) (apd f p)
apd-lemma f g refl = refl

lem :
  {l : Level} {X : UU l} {x y z u v : X} →
  (p : y ＝ x) (q : y ＝ z) (r : z ＝ u) (s : x ＝ v) (t : u ＝ v) →
  (inv p ∙ (q ∙ r) ＝ s ∙ inv t) → q ∙ r ∙ t ＝ p ∙ s
lem refl q r refl refl x = right-unit ∙ x

module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  (a₀ : domain-span-diagram 𝒮)
  where

  module _
    {l5 : Level}
    (R : descent-data-pushout
      ( span-diagram-flattening-descent-data-pushout
        ( descent-data-zigzag-id-pushout 𝒮 a₀))
      ( l5))
    (r₀ : left-family-descent-data-pushout R (a₀ , refl-id-pushout 𝒮 a₀))
    where

    private
      CB :
        (s : spanning-type-span-diagram 𝒮) →
        (n : ℕ) →
        (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
        concat-s-inf 𝒮 a₀ s
          ( map-cocone-standard-sequential-colimit n p) ＝
        map-cocone-standard-sequential-colimit (succ-ℕ n)
          ( concat-s 𝒮 a₀ s n p)
      CB s =
        htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
          ( up-standard-sequential-colimit)
          ( shift-once-cocone-sequential-diagram
            ( cocone-standard-sequential-colimit
              ( right-sequential-diagram-zigzag-id-pushout 𝒮 a₀ (right-map-span-diagram 𝒮 s))))
          ( hom-diagram-zigzag-sequential-diagram
            ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))

      Ψ :
        (s : spanning-type-span-diagram 𝒮) →
        (n : ℕ) →
        (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
        left-family-descent-data-pushout R
          ( left-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit n p) →
        right-family-descent-data-pushout R
          ( right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-s 𝒮 a₀ s n p))
      Ψ s =
        map-over-diagram-equiv-over-colimit
          ( up-standard-sequential-colimit)
          ( shift-once-cocone-sequential-diagram
            ( cocone-standard-sequential-colimit _))
          ( hom-diagram-zigzag-sequential-diagram
            ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))
          ( ev-pair
            ( left-family-descent-data-pushout R)
            ( left-map-span-diagram 𝒮 s))
          ( ev-pair
            ( right-family-descent-data-pushout R)
            ( right-map-span-diagram 𝒮 s))
          ( ev-pair
            ( equiv-family-descent-data-pushout R)
            ( s))
        -- ( tr
        --   ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
        --   ( CB s n p)) ∘
        -- ( map-family-descent-data-pushout R
        --   ( s , map-cocone-standard-sequential-colimit n p))

      opaque
        -- The definitions currently matter for α and β
        -- Φ :
        --   (s : spanning-type-span-diagram 𝒮) →
        --   (n : ℕ) →
        --   (p : Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) (succ-ℕ n)) →
        --   right-family-descent-data-pushout R
        --     ( right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) p) →
        --   right-family-descent-data-pushout R
        --     ( right-map-span-diagram 𝒮 s ,
        --       concat-s-inf 𝒮 a₀ s (map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))
        -- Φ s n p =
        --   ( tr
        --     ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
        --     ( inv (CB s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))) ∘
        --   ( tr
        --     ( λ p →
        --       right-family-descent-data-pushout R
        --         ( right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
        --     ( glue-pushout _ _ (s , refl , p))) ∘
        --   ( tr
        --     ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
        --     ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) p))

        Φ' :
          (s : spanning-type-span-diagram 𝒮) →
          (n : ℕ) →
          (p : Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) (succ-ℕ n)) →
          right-family-descent-data-pushout R
            ( right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) p) →
          left-family-descent-data-pushout R
            ( left-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p))
        Φ' s =
          inv-map-over-diagram-equiv-zigzag
            ( up-standard-sequential-colimit)
            ( shift-once-cocone-sequential-diagram
              ( cocone-standard-sequential-colimit _))
            ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s)
            ( ev-pair
              ( left-family-descent-data-pushout R)
              ( left-map-span-diagram 𝒮 s))
            ( ev-pair
              ( right-family-descent-data-pushout R)
              ( right-map-span-diagram 𝒮 s))
            ( ev-pair
              ( equiv-family-descent-data-pushout R)
              ( s))

    -- coh-dep-cocone-a :
    --   (s : spanning-type-span-diagram 𝒮) (n : ℕ) →
    --   (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
    --   coherence-square-maps
    --     ( ( tr
    --         ( λ p →
    --           left-family-descent-data-pushout R
    --             ( left-map-span-diagram 𝒮 s ,
    --               map-cocone-standard-sequential-colimit (succ-ℕ n) p))
    --         ( glue-pushout _ _ (s , refl , p))) ∘
    --       ( tr
    --         ( ev-pair
    --           ( left-family-descent-data-pushout R)
    --           ( left-map-span-diagram 𝒮 s))
    --         ( coherence-cocone-standard-sequential-colimit n p)))
    --     ( map-family-descent-data-pushout R
    --       ( s , map-cocone-standard-sequential-colimit n p))
    --     ( map-family-descent-data-pushout R
    --       ( s ,
    --         map-cocone-standard-sequential-colimit (succ-ℕ n)
    --           ( concat-inv-s 𝒮 a₀ s (succ-ℕ n) ( concat-s 𝒮 a₀ s n p))))
    --     ( ( tr
    --         ( ev-pair
    --           ( right-family-descent-data-pushout R)
    --           ( right-map-span-diagram 𝒮 s))
    --         ( inv (CB s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) (concat-s 𝒮 a₀ s n p))))) ∘
    --       ( tr
    --         ( λ p →
    --           right-family-descent-data-pushout R
    --             ( right-map-span-diagram 𝒮 s ,
    --               map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
    --         ( glue-pushout _ _ (s , refl , concat-s 𝒮 a₀ s n p))) ∘
    --       ( tr
    --         ( ev-pair
    --           ( right-family-descent-data-pushout R)
    --           ( right-map-span-diagram 𝒮 s))
    --         ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) (concat-s 𝒮 a₀ s n p))) ∘
    --       ( tr
    --         ( ev-pair
    --           ( right-family-descent-data-pushout R)
    --           ( right-map-span-diagram 𝒮 s))
    --         ( CB s n p)))
    -- coh-dep-cocone-a s n p =
    --   ( ( inv-htpy
    --       ( ( tr-concat _ _) ∙h
    --         ( ( tr _ _) ·l
    --           ( ( tr-concat _ _) ∙h
    --             ( horizontal-concat-htpy
    --               ( λ _ → substitution-law-tr _ _ _)
    --               ( tr-concat _ _)))))) ·r
    --     ( map-family-descent-data-pushout R
    --       ( s , map-cocone-standard-sequential-colimit n p))) ∙h
    --   ( ( λ q →
    --       ap
    --         ( λ r →
    --           tr
    --             ( ev-pair
    --                ( right-family-descent-data-pushout R)
    --                ( right-map-span-diagram 𝒮 s))
    --             ( r)
    --             ( map-family-descent-data-pushout R
    --               ( s , map-cocone-standard-sequential-colimit n p)
    --               ( q)))
    --         ( inv ([i] p))) ∙h
    --     ( λ q →
    --       substitution-law-tr
    --         ( ev-pair
    --           ( right-family-descent-data-pushout R)
    --           ( right-map-span-diagram 𝒮 s))
    --         ( concat-s-inf 𝒮 a₀ s)
    --         ( coherence-cocone-standard-sequential-colimit n p ∙
    --           ap
    --             ( map-cocone-standard-sequential-colimit (succ-ℕ n))
    --             ( glue-standard-pushout _ _))) ∙h
    --     ( inv-htpy
    --       ( preserves-tr
    --         ( ev-pair
    --           ( map-family-descent-data-pushout R)
    --           ( s))
    --         ( coherence-cocone-standard-sequential-colimit n p ∙
    --           ap (map-cocone-standard-sequential-colimit (succ-ℕ n)) (glue-standard-pushout _ _))))) ∙h
    --   ( ( map-family-descent-data-pushout R
    --       ( s ,
    --         map-cocone-standard-sequential-colimit
    --           ( succ-ℕ n)
    --           ( concat-inv-s 𝒮 a₀ s
    --             ( succ-ℕ n)
    --             ( concat-s 𝒮 a₀ s n p)))) ·l
    --     ( ( tr-concat _ _) ∙h
    --       ( λ q → substitution-law-tr _ _ _)))
    --   where
    --   [i] :
    --     ( ( concat-s-inf 𝒮 a₀ s) ·l
    --       ( ( coherence-cocone-standard-sequential-colimit n) ∙h
    --         ( ( map-cocone-standard-sequential-colimit
    --           { A =
    --             left-sequential-diagram-zigzag-id-pushout 𝒮 a₀
    --               ( left-map-span-diagram 𝒮 s)}
    --           ( succ-ℕ n)) ·l
    --         ( λ p → glue-pushout _ _ (s , refl , p))))) ~
    --     ( ( CB s n) ∙h
    --       ( ( coherence-cocone-standard-sequential-colimit (succ-ℕ n)) ·r
    --           ( concat-s 𝒮 a₀ s n)) ∙h
    --       ( ( map-cocone-standard-sequential-colimit
    --           { A =
    --             right-sequential-diagram-zigzag-id-pushout 𝒮 a₀
    --               ( right-map-span-diagram 𝒮 s)}
    --           ( succ-ℕ (succ-ℕ n))) ·l
    --         ( λ p → glue-pushout _ _ ( s , refl , concat-s 𝒮 a₀ s n p))) ∙h
    --       ( ( inv-htpy (CB s (succ-ℕ n))) ·r
    --         ( concat-inv-s 𝒮 a₀ s (succ-ℕ n) ∘ concat-s 𝒮 a₀ s n)))
    --   [i] =
    --     ( distributive-left-whisker-comp-concat _ _ _) ∙h
    --     ( right-transpose-htpy-concat _ _ _
    --       ( ( left-whisker-concat-coherence-square-homotopies _ _ _ _ _
    --           ( λ p →
    --             inv
    --               ( nat-coherence-square-maps _ _ _ _
    --                 ( CB s (succ-ℕ n))
    --                 ( glue-pushout _ _ (s , refl , p))))) ∙h
    --         ( map-inv-equiv
    --           ( equiv-right-transpose-htpy-concat _ _ _)
    --           ( ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
    --               ( up-standard-sequential-colimit)
    --               ( shift-once-cocone-sequential-diagram
    --                 ( cocone-standard-sequential-colimit
    --                   ( right-sequential-diagram-zigzag-id-pushout 𝒮 a₀
    --                     ( right-map-span-diagram 𝒮 s))))
    --               ( hom-diagram-zigzag-sequential-diagram
    --                 ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))
    --               ( n)) ∙h
    --             ( ap-concat-htpy
    --               ( CB s n)
    --               ( ( ap-concat-htpy _
    --                   ( ( distributive-left-whisker-comp-concat
    --                       ( map-cocone-standard-sequential-colimit
    --                         { A =
    --                           right-sequential-diagram-zigzag-id-pushout 𝒮 a₀
    --                             ( right-map-span-diagram 𝒮 s)}
    --                         ( succ-ℕ (succ-ℕ n)))
    --                       ( _)
    --                       ( _)) ∙h
    --                     ( ap-concat-htpy _
    --                       ( ( left-whisker-comp² _
    --                           ( left-whisker-inv-htpy _ _)) ∙h
    --                         ( left-whisker-inv-htpy _ _))))) ∙h
    --                 ( inv-htpy-assoc-htpy _ _ _))) ∙h
    --             ( inv-htpy-assoc-htpy _ _ _))))) ∙h
    --     ( ap-concat-htpy' _
    --       ( inv-htpy-assoc-htpy _ _ _))

        α :
          (s : spanning-type-span-diagram 𝒮) →
          (n : ℕ) →
          (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
          coherence-square-maps
            ( Ψ s n p)
            ( tr
              ( ev-pair
                ( left-family-descent-data-pushout R)
                ( left-map-span-diagram 𝒮 s))
              ( coherence-cocone-standard-sequential-colimit n p))
            ( Φ' s n (concat-s 𝒮 a₀ s n p))
            ( tr
              ( λ p →
                left-family-descent-data-pushout R
                  ( left-map-span-diagram 𝒮 s ,
                    map-cocone-standard-sequential-colimit (succ-ℕ n) p))
              ( glue-pushout _ _ (s , refl , p)))
        α s n p =
          upper-triangle-over
            ( up-standard-sequential-colimit)
            ( shift-once-cocone-sequential-diagram
              ( cocone-standard-sequential-colimit _))
            ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s)
            ( ev-pair
              ( left-family-descent-data-pushout R)
              ( left-map-span-diagram 𝒮 s))
            ( ev-pair
              ( right-family-descent-data-pushout R)
              ( right-map-span-diagram 𝒮 s))
            ( ev-pair
              ( equiv-family-descent-data-pushout R)
              ( s))
            ( n)
            { p}
          -- map-eq-transpose-equiv
          --   ( equiv-family-descent-data-pushout R
          --     ( s ,
          --       map-cocone-standard-sequential-colimit
          --         ( succ-ℕ n)
          --         ( concat-inv-s 𝒮 a₀ s
          --           ( succ-ℕ n)
          --           ( concat-s 𝒮 a₀ s n p))))
          --   ( inv (coh-dep-cocone-a s n p q))

        β :
          (s : spanning-type-span-diagram 𝒮) →
          (n : ℕ) →
          (p : Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) (succ-ℕ n)) →
          coherence-square-maps
            ( Φ' s n p)
            ( tr
              ( ev-pair
                ( right-family-descent-data-pushout R)
                ( right-map-span-diagram 𝒮 s))
              ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) p))
            ( Ψ s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p))
            ( tr
              ( λ p →
                right-family-descent-data-pushout R
                  ( right-map-span-diagram 𝒮 s ,
                    map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
              ( glue-pushout _ _ (s , refl , p)))
        β s n p =
          lower-triangle-over
            ( up-standard-sequential-colimit)
            ( shift-once-cocone-sequential-diagram
              ( cocone-standard-sequential-colimit _))
            ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s)
            ( ev-pair
              ( left-family-descent-data-pushout R)
              ( left-map-span-diagram 𝒮 s))
            ( ev-pair
              ( right-family-descent-data-pushout R)
              ( right-map-span-diagram 𝒮 s))
            ( ev-pair
              ( equiv-family-descent-data-pushout R)
              ( s))
            ( n)
            { p}

    -- Note for refactoring: after contracting away the last component and the
    -- vertical map, the definition of prism2 will fail to typecheck, since
    -- currently the coherence computes to <X> ∙ refl, which needs to be taken
    -- into account; contracting away this data would simplify the later
    -- homotopy algebra.
    stages-cocones' :
      (n : ℕ) →
      Σ ( (b : codomain-span-diagram 𝒮) →
          dependent-cocone-span-diagram
            ( cocone-pushout-span-diagram
              ( span-diagram-path-to-b 𝒮 a₀ b n))
            ( λ p →
              right-family-descent-data-pushout R
                ( b , map-cocone-standard-sequential-colimit (succ-ℕ n) p)))
        ( λ dep-cocone-b →
          Σ ( (a : domain-span-diagram 𝒮) →
              dependent-cocone-span-diagram
                ( cocone-pushout-span-diagram
                  ( span-diagram-path-to-a 𝒮 a₀ a n))
                ( λ p →
                  left-family-descent-data-pushout R
                    ( a , map-cocone-standard-sequential-colimit (succ-ℕ n) p)))
            ( λ dep-cocone-a →
              (s : spanning-type-span-diagram 𝒮) →
              (p : Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) (succ-ℕ n)) →
              vertical-map-dependent-cocone _ _ _ _
                ( dep-cocone-a (left-map-span-diagram 𝒮 s))
                ( s , refl , p) ＝
              Φ' s n p (dependent-cogap _ _ (dep-cocone-b (right-map-span-diagram 𝒮 s)) p)))
    stages-cocones' zero-ℕ =
      dep-cocone-b ,
      dep-cocone-a ,
      λ s p → refl
      where
      dep-cocone-b :
        (b : codomain-span-diagram 𝒮) →
        dependent-cocone-span-diagram
          ( cocone-pushout-span-diagram (span-diagram-path-to-b 𝒮 a₀ b 0))
          ( λ p →
            right-family-descent-data-pushout R
              ( b , map-cocone-standard-sequential-colimit 1 p))
      pr1 (dep-cocone-b b) (map-raise ())
      pr1 (pr2 (dep-cocone-b ._)) (s , refl , map-raise refl) =
        tr
          ( ev-pair
            ( right-family-descent-data-pushout R)
            ( right-map-span-diagram 𝒮 s))
          ( CB s 0 (map-raise refl))
          ( map-family-descent-data-pushout R
            ( s , map-cocone-standard-sequential-colimit 0 (map-raise refl))
            ( r₀))
      pr2 (pr2 (dep-cocone-b ._)) (s , refl , map-raise ())
      dep-cocone-a :
        (a : domain-span-diagram 𝒮) →
        dependent-cocone-span-diagram
          ( cocone-pushout-span-diagram (span-diagram-path-to-a 𝒮 a₀ a 0))
          ( λ p →
            left-family-descent-data-pushout R
              ( a , map-cocone-standard-sequential-colimit 1 p))
      pr1 (dep-cocone-a .a₀) (map-raise refl) =
        tr
          ( ev-pair (left-family-descent-data-pushout R) a₀)
          ( coherence-cocone-standard-sequential-colimit 0 (map-raise refl))
          ( r₀)
      pr1 (pr2 (dep-cocone-a a)) (s , refl , p) =
        Φ' s 0 p (dependent-cogap _ _ (dep-cocone-b (right-map-span-diagram 𝒮 s)) p)
      pr2 (pr2 (dep-cocone-a .a₀)) (s , refl , map-raise refl) =
        ( α s 0 (map-raise refl) r₀) ∙
        ( ap
          ( Φ' s 0 _)
          ( inv
            ( compute-inr-dependent-cogap _ _
              ( dep-cocone-b (right-map-span-diagram 𝒮 s))
              ( s , refl , map-raise refl))))
    stages-cocones' (succ-ℕ n) =
      dep-cocone-b ,
      dep-cocone-a ,
      λ s p → refl
      where
      dep-cocone-b :
        (b : codomain-span-diagram 𝒮) →
        dependent-cocone-span-diagram
          ( cocone-pushout-span-diagram (span-diagram-path-to-b 𝒮 a₀ b (succ-ℕ n)))
          ( λ p →
            right-family-descent-data-pushout R
              ( b , map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
      pr1 (dep-cocone-b b) p =
        tr
          ( ev-pair (right-family-descent-data-pushout R) b)
          ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) p)
          ( dependent-cogap _ _ (pr1 (stages-cocones' n) b) p)
      pr1 (pr2 (dep-cocone-b b)) (s , refl , p) =
        tr
          ( ev-pair
            ( right-family-descent-data-pushout R)
            ( right-map-span-diagram 𝒮 s))
          ( CB s (succ-ℕ n) p)
          ( map-family-descent-data-pushout R
            ( s , map-cocone-standard-sequential-colimit (succ-ℕ n) p)
            ( dependent-cogap _ _ (pr1 (pr2 (stages-cocones' n)) (left-map-span-diagram 𝒮 s)) p))
      pr2 (pr2 (dep-cocone-b b)) (s , refl , p) =
        ( β s n p _) ∙
        ( ap
          ( Ψ s (succ-ℕ n) _)
          ( inv
            ( ( compute-inr-dependent-cogap _ _
                ( pr1 (pr2 (stages-cocones' n)) (left-map-span-diagram 𝒮 s))
                ( s , refl , p)) ∙
              ( pr2 (pr2 (stages-cocones' n)) s p))))
      dep-cocone-a :
        (a : domain-span-diagram 𝒮) →
        dependent-cocone-span-diagram
          ( cocone-pushout-span-diagram (span-diagram-path-to-a 𝒮 a₀ a (succ-ℕ n)))
          ( λ p →
            left-family-descent-data-pushout R
              ( a , map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
      pr1 (dep-cocone-a a) p =
        tr
          ( ev-pair (left-family-descent-data-pushout R) a)
          ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) p)
          ( dependent-cogap _ _ (pr1 (pr2 (stages-cocones' n)) a) p)
      pr1 (pr2 (dep-cocone-a a)) (s , refl , p) =
        Φ' s (succ-ℕ n) p (dependent-cogap _ _ (dep-cocone-b (right-map-span-diagram 𝒮 s)) p)
      pr2 (pr2 (dep-cocone-a a)) (s , refl , p) =
        ( α s (succ-ℕ n) p _) ∙
        ( ap
          ( Φ' s (succ-ℕ n) _)
          ( inv
            ( compute-inr-dependent-cogap _ _
              ( dep-cocone-b (right-map-span-diagram 𝒮 s))
              ( s , refl , p))))

    tB :
      (b : codomain-span-diagram 𝒮) (n : ℕ) (p : Path-to-b 𝒮 a₀ b n) →
      right-family-descent-data-pushout R
        ( b , map-cocone-standard-sequential-colimit n p)
    tB b zero-ℕ (map-raise ())
    tB b (succ-ℕ n) = dependent-cogap _ _ (pr1 (stages-cocones' n) b)

    KB :
      (b : codomain-span-diagram 𝒮) (n : ℕ) (p : Path-to-b 𝒮 a₀ b n) →
      dependent-identification
        ( ev-pair (right-family-descent-data-pushout R) b)
        ( coherence-cocone-standard-sequential-colimit n p)
        ( tB b n p)
        ( tB b (succ-ℕ n) (inl-Path-to-b 𝒮 a₀ b n p))
    KB b zero-ℕ (map-raise ())
    KB b (succ-ℕ n) p =
      inv
        ( compute-inl-dependent-cogap _ _
          ( pr1 (stages-cocones' (succ-ℕ n)) b)
          ( p))

    tA :
      (a : domain-span-diagram 𝒮) (n : ℕ) (p : Path-to-a 𝒮 a₀ a n) →
      left-family-descent-data-pushout R
        ( a , map-cocone-standard-sequential-colimit n p)
    tA .a₀ zero-ℕ (map-raise refl) = r₀
    tA a (succ-ℕ n) = dependent-cogap _ _ (pr1 (pr2 (stages-cocones' n)) a)

    KA :
      (a : domain-span-diagram 𝒮) (n : ℕ) (p : Path-to-a 𝒮 a₀ a n) →
        dependent-identification
          ( ev-pair (left-family-descent-data-pushout R) a)
          ( coherence-cocone-standard-sequential-colimit n p)
          ( tA a n p)
          ( tA a (succ-ℕ n) (inl-Path-to-a 𝒮 a₀ a n p))
    KA a zero-ℕ (map-raise refl) =
      inv
        ( compute-inl-dependent-cogap _ _
          ( pr1 (pr2 (stages-cocones' 0)) a)
          ( map-raise refl))
    KA a (succ-ℕ n) p =
      inv
        ( compute-inl-dependent-cogap _ _
          ( pr1 (pr2 (stages-cocones' (succ-ℕ n))) a)
          ( p))

    tS-in-diagram :
      (s : spanning-type-span-diagram 𝒮) (n : ℕ) →
      (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
      ( tr (ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
        ( CB s n p)
        ( map-family-descent-data-pushout R _ (tA (left-map-span-diagram 𝒮 s) n p))) ＝
      ( tB (right-map-span-diagram 𝒮 s) (succ-ℕ n) (concat-s 𝒮 a₀ s n p))
    tS-in-diagram s zero-ℕ (map-raise refl) =
      inv (compute-inr-dependent-cogap _ _ _ _)
    tS-in-diagram s (succ-ℕ n) p = inv (compute-inr-dependent-cogap _ _ _ _)

    module vertices
      (s : spanning-type-span-diagram 𝒮)
      where
      PAn : (n : ℕ) → UU (l1 ⊔ l2 ⊔ l3)
      PAn = Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s)
      QAn : {n : ℕ} → PAn n → UU l5
      QAn {n} p =
        left-family-descent-data-pushout R (left-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit n p)
      PBn : (n : ℕ) → UU (l1 ⊔ l2 ⊔ l3)
      PBn = Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) ∘ succ-ℕ
      QBn : {n : ℕ} → PBn n → UU l5
      QBn {n} p =
        right-family-descent-data-pushout R (right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) p)
      fn : {n : ℕ} → PAn n → PBn n
      fn = concat-s 𝒮 a₀ s _
      gn : {n : ℕ} → PAn n → PAn (succ-ℕ n)
      gn = inl-Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) _
      hn : {n : ℕ} → PBn n → PBn (succ-ℕ n)
      hn = inl-Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) _
      mn : {n : ℕ} → PBn n → PAn (succ-ℕ n)
      mn {n} = concat-inv-s 𝒮 a₀ s (succ-ℕ n)
      sAn : {n : ℕ} (p : PAn n) → QAn p
      sAn = tA (left-map-span-diagram 𝒮 s) _
      sBn : {n : ℕ} (p : PBn n) → QBn p
      sBn = tB (right-map-span-diagram 𝒮 s) _
      f'n : {n : ℕ} {p : PAn n} → QAn p → QBn (fn p)
      f'n {n} {p} = Ψ s n p
      g'n : {n : ℕ} {p : PAn n} → QAn p → QAn (gn p)
      g'n {n} {p} =
        tr
          ( ev-pair
            ( left-family-descent-data-pushout R)
            ( left-map-span-diagram 𝒮 s))
          ( coherence-cocone-standard-sequential-colimit n p)
      h'n : {n : ℕ} {p : PBn n} → QBn p → QBn (hn p)
      h'n {n} {p} =
        tr
          ( ev-pair
            ( right-family-descent-data-pushout R)
            ( right-map-span-diagram 𝒮 s))
          ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) p)
      m'n : {n : ℕ} {p : PBn n} → QBn p → QAn (mn p)
      m'n = Φ' s _ _

    module sides
      (s : spanning-type-span-diagram 𝒮) (n : ℕ)
      where
      open vertices s
      left :
        {p : PAn n} → f'n (sAn p) ＝ sBn (fn p)
      left = tS-in-diagram s n _
      right :
        {p : PAn (succ-ℕ n)} →
        f'n (sAn p) ＝ sBn (fn p)
      right = tS-in-diagram s (succ-ℕ n) _
      bottom :
        {p : PAn n} → hn (fn p) ＝ fn (gn p)
      bottom =
        naturality-map-hom-diagram-zigzag-sequential-diagram
          ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s)
          ( n)
          ( _)
      bottom1 :
        {p : PAn n} → gn p ＝ mn (fn p)
      bottom1 = glue-pushout _ _ _
      bottom2 :
        {p : PBn n} → hn p ＝ fn (mn p)
      bottom2 = glue-pushout _ _ _
      far :
        {p : PAn n} → g'n (sAn p) ＝ sAn (gn p)
      far = KA (left-map-span-diagram 𝒮 s) n _
      near :
        {p : PBn n} → h'n (sBn p) ＝ sBn (hn p)
      near = KB (right-map-span-diagram 𝒮 s) (succ-ℕ n) _
      mid :
        {p : PBn n} → m'n (sBn p) ＝ sAn (mn p)
      mid = mid' _ _
        where
        mid' : (n : ℕ) (p : PBn n) → m'n (sBn p) ＝ sAn (mn p)
        mid' zero-ℕ p = inv (compute-inr-dependent-cogap _ _ _ _)
        mid' (succ-ℕ n) p = inv (compute-inr-dependent-cogap _ _ _ _)
      top1 :
        {p : PAn n} (q : QAn p) →
        tr QAn bottom1 (g'n q) ＝ m'n (f'n q)
      top1 = α s n _
      top2 :
        {p : PBn n} (q : QBn p) →
        tr QBn bottom2 (h'n {n = n} q) ＝ f'n {n = succ-ℕ n} (m'n q)
      top2 = β s n _
      top :
        {p : PAn n} (q : QAn p) →
        tr QBn bottom (h'n (f'n q)) ＝ f'n (g'n q)
      top =
        pasting-triangles-over gn fn fn hn g'n f'n f'n h'n mn m'n
          ( inv-htpy (λ p → bottom1 {p}))
          ( λ p → bottom2 {p})
          ( inv-htpy-over QAn (λ _ → bottom1) g'n (m'n ∘ f'n) top1)
          ( top2)

    module CUBE
      (s : spanning-type-span-diagram 𝒮) (n : ℕ)
      where
      open vertices s
      open sides s n

      CUBE : UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
      CUBE =
        section-square-over gn fn fn hn g'n f'n f'n h'n sAn sBn sAn sBn
          ( λ p → far {p})
          ( λ p → left {p})
          ( λ p → right {p})
          ( λ p → near {p})
          ( λ p → bottom {p})
          ( top)

      PRISM1 : UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
      PRISM1 =
        section-triangle-over fn gn mn f'n g'n m'n sAn sBn sAn
          ( λ p → left {p})
          ( λ p → far {p})
          ( λ p → mid {p})
          ( λ p → bottom1 {p})
          ( top1)

      PRISM2 : UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
      PRISM2 =
        section-triangle-over mn hn fn m'n h'n f'n sBn sAn sBn
          ( λ p → mid {p})
          ( λ p → near {p})
          ( λ p → right {p})
          ( λ p → bottom2 {p})
          ( top2)

    module cube
      (s : spanning-type-span-diagram 𝒮)
      where abstract
      open vertices s
      open sides s
      open CUBE s

      -- THE COMMENTED CODE WORKS, DON'T DELETE IT!
      -- It just takes too long to typecheck it in its current state
      prism1 : (n : ℕ) → PRISM1 n
      -- prism1 = {!!}
      prism1 zero-ℕ (map-raise refl) =
        lem _ _ _ _ _
          ( ( ap
              ( _∙ (top1 0 (sAn _) ∙ ap m'n (left 0)))
              ( ( inv (ap-inv (tr QAn (bottom1 0)) (far 0))) ∙
                ( ap² (tr QAn (bottom1 0)) (inv-inv _)))) ∙
            -- ( [i]) ∙
            ( inv
              ( compute-glue-dependent-cogap _ _
                ( pr1 (pr2 (stages-cocones' 0)) (left-map-span-diagram 𝒮 s))
                ( s , refl , (map-raise refl)))) ∙
            ( ap
              ( apd sAn (bottom1 0) ∙_)
              ( inv (inv-inv _))))
        where
          open import foundation.action-on-higher-identifications-functions
      prism1 (succ-ℕ n) p =
        lem _ _ _ _ _
          ( ( ap
              ( _∙ (top1 (succ-ℕ n) (sAn _) ∙ ap m'n (left (succ-ℕ n))))
              ( ( inv (ap-inv (tr QAn (bottom1 (succ-ℕ n))) (far (succ-ℕ n)))) ∙
                ( ap² (tr QAn (bottom1 (succ-ℕ n))) (inv-inv _)))) ∙
            ( inv
              ( compute-glue-dependent-cogap _ _
                ( pr1 (pr2 (stages-cocones' (succ-ℕ n))) (left-map-span-diagram 𝒮 s))
                ( s , refl , p))) ∙
            -- ( [i]) ∙
            ( ap
              ( apd sAn (bottom1 (succ-ℕ n)) ∙_)
              ( inv (inv-inv _))))
        where
          open import foundation.action-on-higher-identifications-functions

      prism2 : (n : ℕ) → PRISM2 n
      -- prism2 = {!!}
      prism2 0 p =
        lem _ _ _ _ _
          ( ( ap
              ( _∙ (top2 0 (sBn p) ∙ ap f'n (mid 0)))
              ( ( inv (ap-inv (tr QBn (bottom2 0)) (near 0))) ∙
                ( ap² (tr (QBn {1}) (bottom2 0)) (inv-inv _)))) ∙
            -- ( inv [ii]) ∙
            ( inv
              ( ( compute-glue-dependent-cogap _ _
                  ( pr1 (stages-cocones' 1) (right-map-span-diagram 𝒮 s))
                  ( s , refl , p)) ∙
                ( ap
                  ( λ q →
                    ap (tr QBn _) (compute-inl-dependent-cogap _ _ _ _) ∙
                    (top2 0 (sBn p) ∙ ap f'n (inv q)))
                  ( right-unit)))) ∙
            ( ap
              ( apd sBn (bottom2 0) ∙_)
              ( inv (inv-inv _))))
        where
          open import foundation.action-on-higher-identifications-functions
          -- [i] =
          --   -- inv
          --     ( compute-glue-dependent-cogap _ _
          --       ( pr1 (stages-cocones' 1) (right-map-span-diagram 𝒮 s))
          --       ( s , refl , p))
          -- [ii] = [i] ∙ ap (λ q → ap (tr QBn _) (compute-inl-dependent-cogap _ _ _ _) ∙ (top2 0 (sBn p) ∙ ap f'n (inv q))) right-unit
      prism2 (succ-ℕ n) p =
        lem _ _ _ _ _
          ( ( ap
              ( _∙ (top2 (succ-ℕ n) (sBn p) ∙ ap f'n (mid (succ-ℕ n))))
              ( ( inv (ap-inv (tr QBn (bottom2 (succ-ℕ n))) (near (succ-ℕ n)))) ∙
                ( ap² (tr QBn (bottom2 (succ-ℕ n))) (inv-inv _)))) ∙
            -- ( inv [ii]) ∙
            ( inv
              ( ( compute-glue-dependent-cogap _ _
                  ( pr1 (stages-cocones' (succ-ℕ (succ-ℕ n))) (right-map-span-diagram 𝒮 s))
                  ( s , refl , p)) ∙
                ( ap
                  ( λ q →
                    ap (tr QBn _) (compute-inl-dependent-cogap _ _ _ _) ∙
                    (top2 (succ-ℕ n) (sBn p) ∙ ap f'n (inv q)))
                  ( right-unit)))) ∙
            ( ap
              ( apd sBn (bottom2 (succ-ℕ n)) ∙_)
              ( inv (inv-inv _))))
        where
          open import foundation.action-on-higher-identifications-functions
          -- [i] =
          --   -- inv
          --     ( compute-glue-dependent-cogap _ _
          --       ( pr1 (stages-cocones' (succ-ℕ (succ-ℕ n))) (right-map-span-diagram 𝒮 s))
          --       ( s , refl , p))
          -- [ii] = [i] ∙ ap (λ q → ap (tr QBn _) (compute-inl-dependent-cogap _ _ _ _) ∙ (top2 (succ-ℕ n) (sBn p) ∙ ap f'n (inv q))) right-unit

      cube : (n : ℕ) → CUBE n
      cube n =
        pasting-sections-triangles-over gn fn fn hn g'n f'n f'n h'n mn m'n sAn sBn sAn sBn
          ( λ p → far n {p})
          ( λ p → left n {p})
          ( λ p → right n {p})
          ( λ p → near n {p})
          ( λ p → mid n {p})
          ( inv-htpy (λ p → bottom1 n {p}))
          ( λ p → bottom2 n {p})
          ( inv-htpy-over QAn (λ p → bottom1 n {p}) g'n (m'n ∘ f'n) (top1 n))
          ( top2 n)
          ( get-section-triangle-over' fn gn mn f'n g'n m'n sAn sBn sAn
            ( λ p → left n {p})
            ( λ p → far n {p})
            ( λ p → mid n {p})
            ( inv-htpy (λ p → bottom1 n {p}))
            ( inv-htpy-over QAn (λ p → bottom1 n {p}) g'n (m'n ∘ f'n) (top1 n))
            ( inv-section-htpy-over
              ( λ p → bottom1 n {p})
              ( top1 n)
              sAn sAn _ _
              ( unget-section-triangle-over fn gn mn f'n g'n m'n sAn sBn sAn
                ( λ p → left n {p})
                ( λ p → far n {p})
                ( λ p → mid n {p})
                ( λ p → bottom1 n {p})
                ( top1 n)
                ( prism1 n))))
          ( prism2 n)


    opaque
      unfolding Φ' -- square-over-diagram-square-over-colimit γ

      realign-top :
        (s : spanning-type-span-diagram 𝒮) (n : ℕ) →
        (p : vertices.PAn s n) →
        sides.top s n {p} ~
        square-over-diagram-square-over-colimit
          ( up-standard-sequential-colimit)
          ( shift-once-cocone-sequential-diagram
            ( cocone-standard-sequential-colimit _))
          ( hom-diagram-zigzag-sequential-diagram
            ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))
          ( ev-pair
            ( left-family-descent-data-pushout R)
            ( left-map-span-diagram 𝒮 s))
          ( ev-pair
            ( right-family-descent-data-pushout R)
            ( right-map-span-diagram 𝒮 s))
          ( ev-pair
            ( equiv-family-descent-data-pushout R)
            ( s))
          ( n)
          ( p)
      realign-top s =
        compute-square-over-zigzag-square-over-colimit
          ( up-standard-sequential-colimit)
          ( shift-once-cocone-sequential-diagram
            ( cocone-standard-sequential-colimit _))
          ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s)
          ( ev-pair
            ( left-family-descent-data-pushout R)
            ( left-map-span-diagram 𝒮 s))
          ( ev-pair
            ( right-family-descent-data-pushout R)
            ( right-map-span-diagram 𝒮 s))
          ( ev-pair
            ( equiv-family-descent-data-pushout R)
            ( s))

    KS-in-diagram :
      (s : spanning-type-span-diagram 𝒮) (n : ℕ) →
      section-square-over
        ( vertices.gn s)
        ( vertices.fn s)
        ( vertices.fn s)
        ( vertices.hn s)
        ( vertices.g'n s)
        ( vertices.f'n s)
        ( vertices.f'n s)
        ( vertices.h'n s)
        ( vertices.sAn s)
        ( vertices.sBn s)
        ( vertices.sAn s)
        ( vertices.sBn s)
        ( λ p → sides.far s n)
        ( λ p → sides.left s n)
        ( λ p → sides.right s n)
        ( λ p → sides.near s n)
        ( λ p → sides.bottom s n)
        ( sides.top s n)
    KS-in-diagram = cube.cube

    alt-section-RA :
      (a : domain-span-diagram 𝒮)
      (p : left-id-pushout 𝒮 a₀ a) →
      left-family-descent-data-pushout R (a , p)
    alt-section-RA a =
      sect-family-sect-dd-sequential-colimit
        ( up-standard-sequential-colimit)
        ( _)
        ( tA a , KA a)

    alt-section-RB :
      (b : codomain-span-diagram 𝒮)
      (p : right-id-pushout 𝒮 a₀ b) →
      right-family-descent-data-pushout R (b , p)
    alt-section-RB b =
      sect-family-sect-dd-sequential-colimit
        ( up-shift-cocone-sequential-diagram 1 up-standard-sequential-colimit)
        ( _)
        ( tB b ∘ succ-ℕ , KB b ∘ succ-ℕ)

    alt-ind-coherence :
      (s : spanning-type-span-diagram 𝒮)
      (p : left-id-pushout 𝒮 a₀ (left-map-span-diagram 𝒮 s)) →
      map-family-descent-data-pushout R
        ( s , p)
        ( alt-section-RA (left-map-span-diagram 𝒮 s) p) ＝
      alt-section-RB
        ( right-map-span-diagram 𝒮 s)
        ( map-sequential-colimit-hom-sequential-diagram
          ( up-standard-sequential-colimit)
          ( shift-once-cocone-sequential-diagram
            ( cocone-standard-sequential-colimit _))
          ( hom-diagram-zigzag-sequential-diagram
            ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))
          ( p))
    alt-ind-coherence s p =
      square-colimit-cube-diagram
        ( up-standard-sequential-colimit)
        ( up-shift-cocone-sequential-diagram 1 up-standard-sequential-colimit)
        ( hom-diagram-zigzag-sequential-diagram
          ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))
        ( tA (left-map-span-diagram 𝒮 s) , KA (left-map-span-diagram 𝒮 s))
        ( tB (right-map-span-diagram 𝒮 s) ∘ succ-ℕ ,
          KB (right-map-span-diagram 𝒮 s) ∘ succ-ℕ)
        ( λ p → equiv-family-descent-data-pushout R (s , p))
        ( tS-in-diagram s)
        ( λ n p →
          ap
            ( λ H → H ∙ ap (vertices.f'n s) (sides.far s n) ∙ sides.right s n)
            ( inv (realign-top s n p (vertices.sAn s p))) ∙ KS-in-diagram s n p)
        ( p)

    alt-ind-singleton-zigzag-id-pushout' : section-descent-data-pushout R
    pr1 alt-ind-singleton-zigzag-id-pushout' =
      ind-Σ alt-section-RA
    pr1 (pr2 alt-ind-singleton-zigzag-id-pushout') =
      ind-Σ alt-section-RB
    pr2 (pr2 alt-ind-singleton-zigzag-id-pushout') =
      ind-Σ alt-ind-coherence

  is-identity-system-zigzag-id-pushout :
    is-identity-system-descent-data-pushout
      ( descent-data-zigzag-id-pushout 𝒮 a₀)
      ( refl-id-pushout 𝒮 a₀)
  is-identity-system-zigzag-id-pushout =
    is-identity-system-descent-data-pushout-ind-singleton up-c
      ( descent-data-zigzag-id-pushout 𝒮 a₀)
      ( refl-id-pushout 𝒮 a₀)
      -- ( ind-singleton-zigzag-id-pushout')
      ( alt-ind-singleton-zigzag-id-pushout')
```
