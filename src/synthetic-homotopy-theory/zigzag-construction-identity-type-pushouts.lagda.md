# The zigzag construction of identity types of pushouts

```agda
{-# OPTIONS --lossy-unification #-}

module synthetic-homotopy-theory.zigzag-construction-identity-type-pushouts where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

-- open import foundation.commuting-squares-of-maps
-- open import foundation.contractible-types
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
-- open import foundation.fundamental-theorem-of-identity-types
-- open import foundation.homotopies
-- open import foundation.identity-systems
open import foundation.identity-types
-- open import foundation.sections
-- open import foundation.singleton-induction
open import foundation.raising-universe-levels
open import foundation.span-diagrams
open import foundation.transport-along-identifications
-- open import foundation.torsorial-type-families
-- open import foundation.transposition-identifications-along-equivalences
-- open import foundation.universal-property-dependent-pair-types
-- open import foundation.universal-property-identity-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
-- open import synthetic-homotopy-theory.dependent-universal-property-pushouts
-- open import synthetic-homotopy-theory.descent-data-equivalence-types-over-pushouts
-- open import synthetic-homotopy-theory.descent-data-identity-types-over-pushouts
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.functoriality-sequential-colimits
open import synthetic-homotopy-theory.identity-systems-descent-data-pushouts
-- open import synthetic-homotopy-theory.descent-property-pushouts
-- open import synthetic-homotopy-theory.equivalences-descent-data-pushouts
-- open import synthetic-homotopy-theory.families-descent-data-pushouts
open import synthetic-homotopy-theory.flattening-lemma-pushouts
-- open import synthetic-homotopy-theory.morphisms-descent-data-pushouts
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

TODO

## Definitions

### TODO

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  type-stage-zigzag-construction-id-pushout : UU (lsuc (l1 ⊔ l2 ⊔ l3))
  type-stage-zigzag-construction-id-pushout =
    Σ ( codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3))
      ( λ Path-to-b →
        Σ ( domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3))
          ( λ Path-to-a →
            ( (s : spanning-type-span-diagram 𝒮) →
              Path-to-b (right-map-span-diagram 𝒮 s) →
              Path-to-a (left-map-span-diagram 𝒮 s))))

module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  (a₀ : domain-span-diagram 𝒮)
  where

  stage-zigzag-construction-id-pushout :
    ℕ → type-stage-zigzag-construction-id-pushout 𝒮
  stage-zigzag-construction-id-pushout zero-ℕ =
    Path-to-b ,
    Path-to-a ,
    ( λ s → raise-ex-falso _) -- ,
    -- ( λ s p → inr-pushout _ _ (s , refl , p))
    where
    Path-to-b : codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
    Path-to-b _ = raise-empty _
    Path-to-a : domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
    Path-to-a a = raise (l2 ⊔ l3) (a₀ ＝ a)
  stage-zigzag-construction-id-pushout (succ-ℕ n) =
    Path-to-b ,
    Path-to-a ,
    ( λ s p → inr-pushout _ _ (s , refl , p)) -- ,
    -- ( λ s p → inr-pushout _ _ (s , refl , p))
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
                pr2
                  ( pr2 (stage-zigzag-construction-id-pushout n))
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
                      (pr1 (pr2 (stage-zigzag-construction-id-pushout n)))
                      ( r)
                      ( p))))))
    Path-to-a : domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
    Path-to-a a = standard-pushout (span-diagram-A a)

  Path-to-b : codomain-span-diagram 𝒮 → ℕ → UU (l1 ⊔ l2 ⊔ l3)
  Path-to-b b n = pr1 (stage-zigzag-construction-id-pushout n) b

  Path-to-a : domain-span-diagram 𝒮 → ℕ → UU (l1 ⊔ l2 ⊔ l3)
  Path-to-a a n = pr1 (pr2 (stage-zigzag-construction-id-pushout n)) a

  inl-Path-to-b :
    (b : codomain-span-diagram 𝒮) (n : ℕ) → Path-to-b b n → Path-to-b b (succ-ℕ n)
  inl-Path-to-b b n = inl-pushout _ _

  inl-Path-to-a :
    (a : domain-span-diagram 𝒮) (n : ℕ) → Path-to-a a n → Path-to-a a (succ-ℕ n)
  inl-Path-to-a a n = inl-pushout _ _

  concat-inv-s :
    (s : spanning-type-span-diagram 𝒮) →
    (n : ℕ) →
    Path-to-b (right-map-span-diagram 𝒮 s) n →
    Path-to-a (left-map-span-diagram 𝒮 s) n
  concat-inv-s s n = pr2 (pr2 (stage-zigzag-construction-id-pushout n)) s

  concat-s :
    (s : spanning-type-span-diagram 𝒮) →
    (n : ℕ) →
    Path-to-a (left-map-span-diagram 𝒮 s) n →
    Path-to-b (right-map-span-diagram 𝒮 s) (succ-ℕ n)
  concat-s s n p = inr-pushout _ _ (s , refl , p)

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
    glue-pushout _ _ (s , refl , p)
  pr2 (pr2 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout s))) n p =
    glue-pushout _ _ (s , refl , p)

--   -- zigzag-sequential-diagram-zigzag-id-pushout' :
--   --   (s : spanning-type-span-diagram 𝒮) →
--   --   zigzag-sequential-diagram
--   --     ( right-sequential-diagram-zigzag-id-pushout
--   --       ( right-map-span-diagram 𝒮 s))
--   --     ( left-sequential-diagram-zigzag-id-pushout
--   --       ( left-map-span-diagram 𝒮 s))
--   -- pr1 (zigzag-sequential-diagram-zigzag-id-pushout' s) n =
--   --   pr1 (pr2 (pr2 (stage-zigzag-construction-id-pushout n))) s
--   -- pr1 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout' s)) n =
--   --   pr2 (pr2 (pr2 (stage-zigzag-construction-id-pushout n))) s
--   -- pr1 (pr2 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout' s)))
--   --   zero-ℕ (map-raise ())
--   -- pr1 (pr2 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout' s))) (succ-ℕ n) p =
--   --   glue-pushout _ _ (s , refl , p)
--   -- pr2 (pr2 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout' s))) n p =
--   --   glue-pushout _ _ (s , refl , p)

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

  concat-inv-s-inf :
    (s : spanning-type-span-diagram 𝒮) →
    right-id-pushout (right-map-span-diagram 𝒮 s) →
    left-id-pushout (left-map-span-diagram 𝒮 s)
  concat-inv-s-inf s =
    map-inv-equiv (equiv-id-pushout s)

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
module _
  {l1 l2 l3 l4 : Level} {𝒮 : span-diagram l1 l2 l3}
  {X : UU l4} {c : cocone-span-diagram 𝒮 X}
  (up-c : universal-property-pushout _ _ c)
  (a₀ : domain-span-diagram 𝒮)
  where

  type-stage-ind-singleton-zigzag-id-pushout :
    {l5 : Level}
    (R : descent-data-pushout
      ( span-diagram-flattening-descent-data-pushout
        ( descent-data-zigzag-id-pushout 𝒮 a₀))
      ( l5))
    (r₀ : left-family-descent-data-pushout R (a₀ , refl-id-pushout 𝒮 a₀)) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
  type-stage-ind-singleton-zigzag-id-pushout R r₀ =
    Σ ( (a : domain-span-diagram 𝒮) →
        dependent-cocone-sequential-diagram
          ( cocone-standard-sequential-colimit
            ( left-sequential-diagram-zigzag-id-pushout 𝒮 a₀ a))
          ( λ p → left-family-descent-data-pushout R (a , p)))
      ( λ dep-cocone-left →
        (b : codomain-span-diagram 𝒮) →
        dependent-cocone-sequential-diagram
          ( shift-once-cocone-sequential-diagram
            ( cocone-standard-sequential-colimit
              ( right-sequential-diagram-zigzag-id-pushout 𝒮 a₀ b)))
          ( λ p → right-family-descent-data-pushout R (b , p)))

  module _
    {l5 : Level}
    (R : descent-data-pushout
      ( span-diagram-flattening-descent-data-pushout
        ( descent-data-zigzag-id-pushout 𝒮 a₀))
      ( l5))
    (r₀ : left-family-descent-data-pushout R (a₀ , refl-id-pushout 𝒮 a₀))
    where

    interleaved mutual
      cocone-tA :
        (a : domain-span-diagram 𝒮) →
        (n : ℕ) →
        dependent-cocone-span-diagram
          ( cocone-pushout _ _)
          ( λ p →
            left-family-descent-data-pushout R
              ( a , map-cocone-standard-sequential-colimit (succ-ℕ n) p))
      cocone-tB :
        (b : codomain-span-diagram 𝒮) →
        (n : ℕ) →
        dependent-cocone-span-diagram
          ( cocone-pushout _ _)
          ( λ p →
            right-family-descent-data-pushout R
              ( b , map-cocone-standard-sequential-colimit (succ-ℕ n) p))
      cocone-tAA :
        (a : domain-span-diagram 𝒮) →
        dependent-cocone-sequential-diagram
          ( cocone-standard-sequential-colimit
            ( left-sequential-diagram-zigzag-id-pushout 𝒮 a₀ a))
          ( λ p → left-family-descent-data-pushout R (a , p))
      cocone-tBB :
        (b : codomain-span-diagram 𝒮) →
        dependent-cocone-sequential-diagram
          ( cocone-standard-sequential-colimit
            ( right-sequential-diagram-zigzag-id-pushout 𝒮 a₀ b))
          ( λ p → right-family-descent-data-pushout R (b , p))
      tA :
        (a : domain-span-diagram 𝒮) →
        (n : ℕ) →
        (p : Path-to-a 𝒮 a₀ a n) →
        left-family-descent-data-pushout R
          ( a , map-cocone-standard-sequential-colimit n p)
      tAA :
        (a : domain-span-diagram 𝒮) →
        (p : left-id-pushout 𝒮 a₀ a) →
        left-family-descent-data-pushout R (a , p)
      kA :
        (a : domain-span-diagram 𝒮) →
        (n : ℕ) →
        (p : Path-to-a 𝒮 a₀ a n) →
        tr
          ( ev-pair (left-family-descent-data-pushout R) a)
          ( coherence-cocone-standard-sequential-colimit n p)
          ( tA a n p) ＝
        tA a (succ-ℕ n) (inl-Path-to-a 𝒮 a₀ a n p)
      tB :
        (b : codomain-span-diagram 𝒮) →
        (n : ℕ) →
        (p : Path-to-b 𝒮 a₀ b n) →
        right-family-descent-data-pushout R
          ( b , map-cocone-standard-sequential-colimit n p)
      tBB :
        (b : codomain-span-diagram 𝒮) →
        (p : right-id-pushout 𝒮 a₀ b) →
        right-family-descent-data-pushout R (b , p)
      kB :
        (b : codomain-span-diagram 𝒮) →
        (n : ℕ) →
        (p : Path-to-b 𝒮 a₀ b n) →
        tr
          ( ev-pair (right-family-descent-data-pushout R) b)
          ( coherence-cocone-standard-sequential-colimit n p)
          ( tB b n p) ＝
        tB b (succ-ℕ n) (inl-Path-to-b 𝒮 a₀ b n p)
      tR :
        (s : spanning-type-span-diagram 𝒮) →
        (n : ℕ) →
        (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
        map-family-descent-data-pushout R
          ( s , map-cocone-standard-sequential-colimit n p)
          ( tAA
            ( left-map-span-diagram 𝒮 s)
            ( map-cocone-standard-sequential-colimit n p)) ＝
        tBB
          ( right-map-span-diagram 𝒮 s)
          ( concat-s-inf 𝒮 a₀ s (map-cocone-standard-sequential-colimit n p))
      tRR :
        (s : spanning-type-span-diagram 𝒮) →
        (p : left-id-pushout 𝒮 a₀ (left-map-span-diagram 𝒮 s)) →
        map-family-descent-data-pushout R
          ( s , p)
          ( tAA (left-map-span-diagram 𝒮 s) p) ＝
        tBB
          ( right-map-span-diagram 𝒮 s)
          ( concat-s-inf 𝒮 a₀ s p)

      tA a zero-ℕ (map-raise refl) = r₀
      tA a (succ-ℕ n) = dependent-cogap _ _ (cocone-tA a n)
      tB b zero-ℕ (map-raise ())
      tB b (succ-ℕ n) = dependent-cogap _ _ (cocone-tB b n)
      tAA a = dependent-cogap-standard-sequential-colimit (cocone-tAA a)
      tBB b = dependent-cogap-standard-sequential-colimit (cocone-tBB b)

      pr1 (cocone-tA a n) p =
        tr
          ( ev-pair (left-family-descent-data-pushout R) a)
          ( coherence-cocone-standard-sequential-colimit n p)
          ( tA a n p)
      pr1 (pr2 (cocone-tA a n)) (s , refl , p) = {!!}
      pr2 (pr2 (cocone-tA a n)) (s , refl , p) = {!!}

      pr1 (cocone-tB b n) p =
        tr
          ( ev-pair (right-family-descent-data-pushout R) b)
          ( coherence-cocone-standard-sequential-colimit n p)
          ( tB b n p)
      pr1 (pr2 (cocone-tB b n)) (s , refl , p) =
        tr
          ( ev-pair (right-family-descent-data-pushout R) b)
          ( {!!})
          ( map-family-descent-data-pushout R
            ( s , map-cocone-standard-sequential-colimit n p)
            ( tA (left-map-span-diagram 𝒮 s) n p))
      pr2 (pr2 (cocone-tB b n)) (s , refl , p) = {!!}

      kA a n p = inv (compute-inl-dependent-cogap _ _ (cocone-tA a n) p)
      kB b n p = inv (compute-inl-dependent-cogap _ _ (cocone-tB b n) p)

      pr1 (cocone-tAA a) = tA a
      pr2 (cocone-tAA a) = kA a

      pr1 (cocone-tBB b) = tB b
      pr2 (cocone-tBB b) = kB b

    type-stage-map-ind-singleton-zigzag-id-pushout :
      (n : ℕ) →
      UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
    type-stage-map-ind-singleton-zigzag-id-pushout n =
      Σ ( (b : codomain-span-diagram 𝒮) (p : Path-to-b 𝒮 a₀ b n) →
          right-family-descent-data-pushout R
            (b , map-cocone-standard-sequential-colimit n p))
        ( λ tB →
          Σ ( (a : domain-span-diagram 𝒮) (p : Path-to-a 𝒮 a₀ a n) →
              left-family-descent-data-pushout R
                (a , map-cocone-standard-sequential-colimit n p))
            ( λ tA →
              (s : spanning-type-span-diagram 𝒮)
              (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
              {!tB (right-map-span-diagram 𝒮 s)
                ?!} ＝
                {!tr
                  ( )!}))
              -- map-family-descent-data-pushout R
              --   ( s , map-cocone-standard-sequential-colimit n p)
              --   ( tA (left-map-span-diagram 𝒮 s) p)))

    stage-map-ind-singleton-zigzag-id-pushout :
      (n : ℕ) → type-stage-map-ind-singleton-zigzag-id-pushout n
    stage-map-ind-singleton-zigzag-id-pushout zero-ℕ =
      map-b ,
      map-a ,
      {!!}
      where
      map-b :
        (b : codomain-span-diagram 𝒮) (p : Path-to-b 𝒮 a₀ b 0) →
        right-family-descent-data-pushout R
          ( b , map-cocone-standard-sequential-colimit 0 p)
      map-b b (map-raise ())
      map-a :
        (a : domain-span-diagram 𝒮) (p : Path-to-a 𝒮 a₀ a 0) →
        left-family-descent-data-pushout R
          ( a , map-cocone-standard-sequential-colimit 0 p)
      map-a a (map-raise refl) = r₀
    stage-map-ind-singleton-zigzag-id-pushout (succ-ℕ n) =
      map-b ,
      map-a ,
      {!!}
      where
      dep-cocone-b :
        (b : codomain-span-diagram 𝒮) →
        dependent-cocone _ _
          ( cocone-pushout _ _)
          ( λ p →
            right-family-descent-data-pushout R
              ( b , map-cocone-standard-sequential-colimit (succ-ℕ n) p))
      pr1 (dep-cocone-b b) p =
        tr
          ( ev-pair (right-family-descent-data-pushout R) b)
          ( coherence-cocone-standard-sequential-colimit n p)
          ( pr1 (stage-map-ind-singleton-zigzag-id-pushout n) b p)
      pr1 (pr2 (dep-cocone-b b)) (s , refl , p) =
        tr
          ( ev-pair (right-family-descent-data-pushout R) b)
          ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
            ( up-standard-sequential-colimit)
            ( shift-once-cocone-sequential-diagram
              ( cocone-standard-sequential-colimit
                ( right-sequential-diagram-zigzag-id-pushout 𝒮 a₀ b)))
            ( hom-diagram-zigzag-sequential-diagram
              ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))
            ( n)
            ( p))
          ( map-family-descent-data-pushout R
            ( s , map-cocone-standard-sequential-colimit n p)
            ( pr1
              ( pr2 ( stage-map-ind-singleton-zigzag-id-pushout n))
              ( left-map-span-diagram 𝒮 s)
              ( p)))
      pr2 (pr2 (dep-cocone-b b)) (s , refl , p) = {!!}
      map-b :
        (b : codomain-span-diagram 𝒮) (p : Path-to-b 𝒮 a₀ b (succ-ℕ n)) →
        right-family-descent-data-pushout R
          ( b , map-cocone-standard-sequential-colimit (succ-ℕ n) p)
      map-b b = dependent-cogap _ _ (dep-cocone-b b)
      dep-cocone-a :
        (a : domain-span-diagram 𝒮) →
        dependent-cocone _ _
          ( cocone-pushout _ _)
          ( λ p →
            left-family-descent-data-pushout R
              ( a , map-cocone-standard-sequential-colimit (succ-ℕ n) p))
      pr1 (dep-cocone-a a) p =
        tr
          ( ev-pair (left-family-descent-data-pushout R) a)
          ( coherence-cocone-standard-sequential-colimit n p)
        ( pr1 (pr2 (stage-map-ind-singleton-zigzag-id-pushout n)) a p)
      pr1 (pr2 (dep-cocone-a a)) (s , refl , p) =
        tr
          ( ev-pair (left-family-descent-data-pushout R) a)
          ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
            ( up-shift-cocone-sequential-diagram 1 up-standard-sequential-colimit)
            ( shift-once-cocone-sequential-diagram
              ( cocone-standard-sequential-colimit
                ( left-sequential-diagram-zigzag-id-pushout 𝒮 a₀ a)))
            ( inv-hom-diagram-zigzag-sequential-diagram
              ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))
            ( n)
            ( p))
          ( inv-map-family-descent-data-pushout R
            ( s ,
              map-inv-equiv
                ( equiv-id-pushout 𝒮 a₀ s)
                ( map-cocone-standard-sequential-colimit (succ-ℕ n) p))
            ( tr
              ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
              ( inv
                ( is-section-map-inv-equiv
                  ( equiv-id-pushout 𝒮 a₀ s)
                  ( map-cocone-standard-sequential-colimit (succ-ℕ n) p)))
              ( map-b (right-map-span-diagram 𝒮 s) p)))
      pr2 (pr2 (dep-cocone-a a)) (s , refl , p) = {!!}
      map-a :
        (a : domain-span-diagram 𝒮) (p : Path-to-a 𝒮 a₀ a (succ-ℕ n)) →
        left-family-descent-data-pushout R
          ( a , map-cocone-standard-sequential-colimit (succ-ℕ n) p)
      map-a a = dependent-cogap _ _ (dep-cocone-a a)

  ind-singleton-zigzag-id-pushout :
    {l5 : Level}
    (R :
      descent-data-pushout
        ( span-diagram-flattening-descent-data-pushout
          ( descent-data-zigzag-id-pushout 𝒮 a₀))
        ( l5))
    (r₀ : left-family-descent-data-pushout R (a₀ , refl-id-pushout 𝒮 a₀)) →
    section-descent-data-pushout R
  ind-singleton-zigzag-id-pushout R r₀ =
    ind-Σ (λ a → dependent-cogap-standard-sequential-colimit (dep-cocone-a a)) ,
    ind-Σ (λ b → dependent-cogap-standard-sequential-colimit (dep-cocone-b b)) ,
    ind-Σ {!!}
    where
      dep-cocone-a :
        ( a : domain-span-diagram 𝒮) →
        dependent-cocone-sequential-diagram
          ( cocone-standard-sequential-colimit
            ( left-sequential-diagram-zigzag-id-pushout 𝒮 a₀ a))
          ( λ p → left-family-descent-data-pushout R (a , p))
      pr1 (dep-cocone-a a) n =
        pr1 (pr2 (stage-map-ind-singleton-zigzag-id-pushout R r₀ n)) a
      pr2 (dep-cocone-a a) n =
        {!!}
      dep-cocone-b :
        (b : codomain-span-diagram 𝒮) →
        dependent-cocone-sequential-diagram
          ( cocone-standard-sequential-colimit
            ( right-sequential-diagram-zigzag-id-pushout 𝒮 a₀ b))
          ( λ p → right-family-descent-data-pushout R (b , p))
      pr1 (dep-cocone-b b) n =
        pr1 (stage-map-ind-singleton-zigzag-id-pushout R r₀ n) b
      pr2 (dep-cocone-b b) n =
        {!!}

  is-identity-system-zigzag-id-pushout :
    is-identity-system-descent-data-pushout
      ( descent-data-zigzag-id-pushout 𝒮 a₀)
      ( refl-id-pushout 𝒮 a₀)
  is-identity-system-zigzag-id-pushout =
    is-identity-system-descent-data-pushout-ind-singleton up-c
      ( descent-data-zigzag-id-pushout 𝒮 a₀)
      ( refl-id-pushout 𝒮 a₀)
      ( ind-singleton-zigzag-id-pushout)
```
