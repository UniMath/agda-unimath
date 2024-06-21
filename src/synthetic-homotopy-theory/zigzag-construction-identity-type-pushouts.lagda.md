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
open import foundation.action-on-identifications-dependent-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
-- open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
-- open import foundation.identity-systems
open import foundation.identity-types
-- open import foundation.sections
-- open import foundation.singleton-induction
open import foundation.raising-universe-levels
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.transposition-identifications-along-equivalences
-- open import foundation.torsorial-type-families
-- open import foundation.transposition-identifications-along-equivalences
-- open import foundation.universal-property-dependent-pair-types
-- open import foundation.universal-property-identity-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
-- open import synthetic-homotopy-theory.dependent-universal-property-pushouts
-- open import synthetic-homotopy-theory.descent-data-equivalence-types-over-pushouts
-- open import synthetic-homotopy-theory.descent-data-identity-types-over-pushouts
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.descent-data-pushouts
open import synthetic-homotopy-theory.functoriality-sequential-colimits
open import synthetic-homotopy-theory.identity-systems-descent-data-pushouts
-- open import synthetic-homotopy-theory.descent-property-pushouts
-- open import synthetic-homotopy-theory.equivalences-descent-data-pushouts
open import synthetic-homotopy-theory.families-descent-data-pushouts
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
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
-- open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.universal-property-sequential-colimits
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : sequential-diagram l1} {B : sequential-diagram l2}
  {X : UU l3} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {Y : UU l4} {c' : cocone-sequential-diagram B Y}
  (up-c' : universal-property-sequential-colimit c')
  (z : zigzag-sequential-diagram A B)
  (P : X → UU l5) (Q : Y → UU l6)
  (e : (x : X) → P x ≃ Q (map-colimit-zigzag-sequential-diagram up-c up-c' z x))
  where

  private
    CB :
      (n : ℕ) →
      coherence-square-maps
        ( map-zigzag-sequential-diagram z n)
        ( map-cocone-sequential-diagram c n)
        ( map-cocone-sequential-diagram c' n)
        ( map-colimit-zigzag-sequential-diagram up-c up-c' z)
    CB =
       htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
        ( up-c)
        ( c')
        ( hom-diagram-zigzag-sequential-diagram z)
    dup-c : dependent-universal-property-sequential-colimit c
    dup-c = dependent-universal-property-universal-property-sequential-colimit _ up-c
    dup-c' : dependent-universal-property-sequential-colimit c'
    dup-c' = dependent-universal-property-universal-property-sequential-colimit _ up-c'

  tS-equiv-tS :
    (tA : (n : ℕ) (a : family-sequential-diagram A n) → P (map-cocone-sequential-diagram c n a))
    (HA :
      (n : ℕ) (a : family-sequential-diagram A n) →
      tr P (coherence-cocone-sequential-diagram c n a) (tA n a) ＝
      tA (succ-ℕ n) (map-sequential-diagram A n a))
    (tB : (n : ℕ) (b : family-sequential-diagram B n) → Q (map-cocone-sequential-diagram c' n b))
    (HB :
      (n : ℕ) (b : family-sequential-diagram B n) →
      tr Q (coherence-cocone-sequential-diagram c' n b) (tB n b) ＝
      tB (succ-ℕ n) (map-sequential-diagram B n b))
    (n : ℕ) (a : family-sequential-diagram A n) →
    ( ( map-equiv
        ( e (map-cocone-sequential-diagram c n a))
        ( map-dependent-universal-property-sequential-colimit dup-c
          ( tA , HA)
          ( map-cocone-sequential-diagram c n a))) ＝
      map-dependent-universal-property-sequential-colimit dup-c'
        ( tB , HB)
        ( map-colimit-zigzag-sequential-diagram up-c up-c' z
          ( map-cocone-sequential-diagram c n a))) ≃
    ( ( tr Q
        ( CB n a)
        ( map-equiv (e (map-cocone-sequential-diagram c n a)) (tA n a))) ＝
      ( tB n (map-zigzag-sequential-diagram z n a)))
  tS-equiv-tS tA HA tB HB n a =
    ( equiv-concat' _
      ( pr1
        ( htpy-dependent-cocone-dependent-universal-property-sequential-colimit
          ( dup-c')
          ( tB , HB))
        ( n)
        ( map-zigzag-sequential-diagram z n a))) ∘e
    ( equiv-concat' _
      ( apd
        ( map-dependent-universal-property-sequential-colimit dup-c' (tB , HB))
        ( CB n a))) ∘e
    ( equiv-ap
      ( equiv-tr Q (CB n a))
      ( _)
      ( _)) ∘e
    equiv-concat
      ( ap
        ( map-equiv (e (map-cocone-sequential-diagram c n a)))
        ( inv
          ( pr1
            ( htpy-dependent-cocone-dependent-universal-property-sequential-colimit
              ( dup-c)
              ( tA , HA))
            ( n)
            ( a))))
      ( _)
```

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
    ( λ s → raise-ex-falso _)
    where
    Path-to-b : codomain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
    Path-to-b _ = raise-empty _
    Path-to-a : domain-span-diagram 𝒮 → UU (l1 ⊔ l2 ⊔ l3)
    Path-to-a a = raise (l2 ⊔ l3) (a₀ ＝ a)
  stage-zigzag-construction-id-pushout (succ-ℕ n) =
    Path-to-b ,
    Path-to-a ,
    ( λ s p → inr-pushout _ _ (s , refl , p))
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

  zigzag-sequential-diagram-zigzag-id-pushout' :
    (s : spanning-type-span-diagram 𝒮) →
    zigzag-sequential-diagram
      ( right-sequential-diagram-zigzag-id-pushout
        ( right-map-span-diagram 𝒮 s))
      ( left-sequential-diagram-zigzag-id-pushout
        ( left-map-span-diagram 𝒮 s))
  pr1 (zigzag-sequential-diagram-zigzag-id-pushout' s) =
    concat-inv-s s
  pr1 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout' s)) =
    concat-s s
  pr1 (pr2 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout' s))) n p =
    glue-pushout _ _ (s , refl , p)
  pr2 (pr2 (pr2 (zigzag-sequential-diagram-zigzag-id-pushout' s))) n p =
    glue-pushout _ _ (s , refl , p)

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

  equiv-id-pushout' :
    (s : spanning-type-span-diagram 𝒮) →
    right-id-pushout (right-map-span-diagram 𝒮 s) ≃
    left-id-pushout (left-map-span-diagram 𝒮 s)
  equiv-id-pushout' s =
    equiv-colimit-zigzag-sequential-diagram _ _
      ( up-standard-sequential-colimit)
      ( up-standard-sequential-colimit)
      ( zigzag-sequential-diagram-zigzag-id-pushout' s)

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
nat-lemma :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {P : A → UU l3} {Q : B → UU l4}
  (f : A → B) (h : (a : A) → P a → Q (f a))
  {x y : A} (p : x ＝ y)
  (q : f x ＝ f y) (α : ap f p ＝ q) →
  coherence-square-maps
    ( tr P p)
    ( h x)
    ( h y)
    ( tr Q q)
nat-lemma f h p .(ap f p) refl x = substitution-law-tr _ f p ∙ inv (preserves-tr h p x)

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

    private
      CA :
        (s : spanning-type-span-diagram 𝒮) →
        (n : ℕ) →
        (p : Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) (succ-ℕ n)) →
        concat-inv-s-inf 𝒮 a₀ s
          ( map-cocone-standard-sequential-colimit (succ-ℕ n) p) ＝
        map-cocone-standard-sequential-colimit (succ-ℕ n)
          ( concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)
      CA s =
        htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
          ( up-shift-cocone-sequential-diagram 1 up-standard-sequential-colimit)
          ( shift-once-cocone-sequential-diagram
            ( cocone-standard-sequential-colimit
              ( left-sequential-diagram-zigzag-id-pushout 𝒮 a₀ (left-map-span-diagram 𝒮 s))))
          ( inv-hom-diagram-zigzag-sequential-diagram
            ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))

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

      foo :
        (s : spanning-type-span-diagram 𝒮) →
        (n : ℕ) →
        (p : Path-to-b 𝒮 a₀ (right-map-span-diagram 𝒮 s) (succ-ℕ n)) →
        right-family-descent-data-pushout R
          ( right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) p) →
        right-family-descent-data-pushout R
          ( right-map-span-diagram 𝒮 s ,
            concat-s-inf 𝒮 a₀ s (map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))
      foo s n p =
        ( tr
          ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
          ( inv (CB s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))) ∘
        ( tr
          ( λ p →
            right-family-descent-data-pushout R
              ( right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
          ( glue-pushout _ _ (s , refl , p))) ∘
        ( tr
          ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
          ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) p))

    interleaved mutual
      -- left section part tⁿ_A a
      tA :
        (a : domain-span-diagram 𝒮) →
        (n : ℕ) →
        (p : Path-to-a 𝒮 a₀ a n) →
        left-family-descent-data-pushout R
          ( a , map-cocone-standard-sequential-colimit n p)
      -- definition of tⁿ⁺¹_A a (pattern matching on Pⁿ⁺¹_A a)
      cocone-tA :
        (a : domain-span-diagram 𝒮) →
        (n : ℕ) →
        dependent-cocone-span-diagram
          ( cocone-pushout _ _)
          ( λ p →
            left-family-descent-data-pushout R
              ( a , map-cocone-standard-sequential-colimit (succ-ℕ n) p))
      -- right section part tⁿ_B b
      tB :
        (b : codomain-span-diagram 𝒮) →
        (n : ℕ) →
        (p : Path-to-b 𝒮 a₀ b n) →
        right-family-descent-data-pushout R
          ( b , map-cocone-standard-sequential-colimit n p)
      -- definition of tⁿ⁺¹_B b (pattern matching on Pⁿ⁺¹_B b)
      cocone-tB :
        (b : codomain-span-diagram 𝒮) →
        (n : ℕ) →
        dependent-cocone-span-diagram
          ( cocone-pushout _ _)
          ( λ p →
            right-family-descent-data-pushout R
              ( b , map-cocone-standard-sequential-colimit (succ-ℕ n) p))
      -- section coherence part tⁿ_S
      tS :
        (s : spanning-type-span-diagram 𝒮) →
        (n : ℕ) →
        (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
        tr
          ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
          ( CB s n p)
          ( map-family-descent-data-pushout R
            ( s , map-cocone-standard-sequential-colimit n p)
            ( tA (left-map-span-diagram 𝒮 s) n p)) ＝
        tB (right-map-span-diagram 𝒮 s) (succ-ℕ n) (concat-s 𝒮 a₀ s n p)
      -- left section t_A a
      tAA :
        (a : domain-span-diagram 𝒮) →
        (p : left-id-pushout 𝒮 a₀ a) →
        left-family-descent-data-pushout R (a , p)
      -- definition of t_A a (pattern matching on Pᵒᵒ_A a)
      cocone-tAA :
        (a : domain-span-diagram 𝒮) →
        dependent-cocone-sequential-diagram
          ( cocone-standard-sequential-colimit
            ( left-sequential-diagram-zigzag-id-pushout 𝒮 a₀ a))
          ( λ p → left-family-descent-data-pushout R (a , p))
      -- right section t_B b
      tBB :
        (b : codomain-span-diagram 𝒮) →
        (p : right-id-pushout 𝒮 a₀ b) →
        right-family-descent-data-pushout R (b , p)
      -- definition of t_B b (pattern matching on Pᵒᵒ_B b)
      cocone-tBB :
        (b : codomain-span-diagram 𝒮) →
        dependent-cocone-sequential-diagram
          ( cocone-standard-sequential-colimit
            ( right-sequential-diagram-zigzag-id-pushout 𝒮 a₀ b))
          ( λ p → right-family-descent-data-pushout R (b , p))
      -- section coherence t_S s
      tSS :
        (s : spanning-type-span-diagram 𝒮) →
        (p : left-id-pushout 𝒮 a₀ (left-map-span-diagram 𝒮 s)) →
        map-family-descent-data-pushout R
          ( s , p)
          ( tAA (left-map-span-diagram 𝒮 s) p) ＝
        tBB
          ( right-map-span-diagram 𝒮 s)
          ( concat-s-inf 𝒮 a₀ s p)
      -- definition of t_S s (pattern matching on Pᵒᵒ_A a)
      cocone-tSS :
        (s : spanning-type-span-diagram 𝒮) →
        dependent-cocone-sequential-diagram
          ( cocone-standard-sequential-colimit
            ( left-sequential-diagram-zigzag-id-pushout 𝒮 a₀
              ( left-map-span-diagram 𝒮 s)))
          ( λ p →
            map-family-descent-data-pushout R
              ( s , p)
              ( tAA (left-map-span-diagram 𝒮 s) p) ＝
            tBB (right-map-span-diagram 𝒮 s) (concat-s-inf 𝒮 a₀ s p))

      tA a zero-ℕ (map-raise refl) = r₀
      -- tA (n+1) needs coconeA n, which needs tA n and tB (n+1),
      -- which needs coconeB n, which only needs tB n and tA n,
      -- so it terminates
      tA a (succ-ℕ n) = dependent-cogap _ _ (cocone-tA a n)
      tB b zero-ℕ (map-raise ())
      tB b (succ-ℕ n) = dependent-cogap _ _ (cocone-tB b n)
      tAA a = dependent-cogap-standard-sequential-colimit (cocone-tAA a)
      tBB b = dependent-cogap-standard-sequential-colimit (cocone-tBB b)

      pr1 (cocone-tB b n) p =
        tr
          ( ev-pair (right-family-descent-data-pushout R) b)
          ( coherence-cocone-standard-sequential-colimit n p)
          ( tB b n p)
      pr1 (pr2 (cocone-tB b n)) (s , refl , p) =
        tr
          ( ev-pair (right-family-descent-data-pushout R) b)
          ( CB s n p)
          ( map-family-descent-data-pushout R
            ( s , map-cocone-standard-sequential-colimit n p)
            ( tA (left-map-span-diagram 𝒮 s) n p))
      pr2 (pr2 (cocone-tB ._ zero-ℕ)) (s , refl , map-raise ())
      pr2 (pr2 (cocone-tB ._ (succ-ℕ n))) (s , refl , p) =
        inv
          ( ( ap
              ( λ q →
                tr
                  ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
                  ( CB s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p))
                  ( map-family-descent-data-pushout R
                    ( s , map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p))
                    ( q)))
              ( compute-inr-dependent-cogap _ _
                ( cocone-tA (left-map-span-diagram 𝒮 s) n)
                ( s , refl , p))) ∙
            ( ap
              ( tr
                ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
                ( CB s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))
              -- Would typecheck if Agda were to expand vertical-map-dependent-cocone (cocone-tA)
              ( {![i]!})) ∙
            ( is-section-map-inv-equiv
              ( equiv-tr
                ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
                ( CB s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))
              ( _)))
        where
          [i] :
            map-family-descent-data-pushout R
              ( s , map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p))
              ( inv-map-family-descent-data-pushout R
                ( s , map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p))
                ( foo s n p (tB (right-map-span-diagram 𝒮 s) (succ-ℕ n) p))) ＝
            foo s n p (tB (right-map-span-diagram 𝒮 s) (succ-ℕ n) p)
          [i] =
            is-section-map-inv-equiv
              ( equiv-family-descent-data-pushout R
                ( s , map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p)))
              ( foo s n p (tB (right-map-span-diagram 𝒮 s) (succ-ℕ n) p))

      pr1 (cocone-tA a n) p =
        tr
          ( ev-pair (left-family-descent-data-pushout R) a)
          ( coherence-cocone-standard-sequential-colimit n p)
          ( tA a n p)
      pr1 (pr2 (cocone-tA a n)) (s , refl , p) =
        inv-map-family-descent-data-pushout R
          ( s , map-cocone-standard-sequential-colimit (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) p))
          ( foo s n p (tB (right-map-span-diagram 𝒮 s) (succ-ℕ n) p))
      pr2 (pr2 (cocone-tA a n)) (s , refl , p) =
        [key]
        where
        [i] :
          ( ( concat-s-inf 𝒮 a₀ s) ·l
            ( coherence-cocone-standard-sequential-colimit n ∙h
              map-cocone-standard-sequential-colimit (succ-ℕ n) ·l (λ p → glue-pushout _ _ (s , refl , p)))) ~
          ( ( CB s n) ∙h
            ( ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) ·r
              ( concat-s 𝒮 a₀ s n))) ∙h
            ( ( map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n))) ·l
              (λ p → glue-pushout _ _ (s , refl , concat-s 𝒮 a₀ s n p))) ∙h
            ( {!CB s (succ-ℕ n) ·r ?!}))
        [i] =
          {!coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
            ( up-standard-sequential-colimit)
            ( shift-once-cocone-sequential-diagram
              ( cocone-standard-sequential-colimit
                ( right-sequential-diagram-zigzag-id-pushout 𝒮 a₀ (right-map-span-diagram 𝒮 s))))
            ( hom-diagram-zigzag-sequential-diagram
              ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))
            ( n)!}
        [key]'' :
          tr
            ( λ p →
              left-family-descent-data-pushout R
                ( left-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) p))
            ( glue-pushout _ _ (s , refl , p))
            ( tr
              ( ev-pair (left-family-descent-data-pushout R) (left-map-span-diagram 𝒮 s))
              ( coherence-cocone-standard-sequential-colimit n p)
              ( tA (left-map-span-diagram 𝒮 s) n p)) ＝
          inv-map-family-descent-data-pushout R
            ( s ,
              map-cocone-standard-sequential-colimit
                ( succ-ℕ n)
                ( concat-inv-s 𝒮 a₀ s (succ-ℕ n) (concat-s 𝒮 a₀ s n p)))
            ( ( ( tr
                  ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
                  ( inv (CB s (succ-ℕ n) (concat-inv-s 𝒮 a₀ s (succ-ℕ n) (concat-s 𝒮 a₀ s n p))))) ∘
                ( tr
                  ( λ p →
                    right-family-descent-data-pushout R
                      ( right-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ (succ-ℕ n)) p))
                  ( glue-pushout _ _ (s , refl , (concat-s 𝒮 a₀ s n p)))) ∘
                ( tr
                  ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
                  ( coherence-cocone-standard-sequential-colimit (succ-ℕ n) (concat-s 𝒮 a₀ s n p))))
              ( tr
                ( ev-pair (right-family-descent-data-pushout R) (right-map-span-diagram 𝒮 s))
                ( CB s n p)
                ( map-family-descent-data-pushout R
                  ( s , map-cocone-standard-sequential-colimit n p)
                  ( tA (left-map-span-diagram 𝒮 s) n p))))
        [key]'' = {!!}
        [key]' :
          tr
            ( λ p →
              left-family-descent-data-pushout R
                ( left-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) p))
            ( glue-pushout _ _ (s , refl , p))
            ( tr
              ( ev-pair (left-family-descent-data-pushout R) (left-map-span-diagram 𝒮 s))
              ( coherence-cocone-standard-sequential-colimit n p)
              ( tA (left-map-span-diagram 𝒮 s) n p)) ＝
          inv-map-family-descent-data-pushout R
            ( s ,
              map-cocone-standard-sequential-colimit
                ( succ-ℕ n)
                ( concat-inv-s 𝒮 a₀ s (succ-ℕ n) (concat-s 𝒮 a₀ s n p)))
            ( foo s n (concat-s 𝒮 a₀ s n p) (tB (right-map-span-diagram 𝒮 s) (succ-ℕ n) (concat-s 𝒮 a₀ s n p)))
        [key]' = {!!}
        [key] :
          tr
            ( λ p →
              left-family-descent-data-pushout R
                ( left-map-span-diagram 𝒮 s , map-cocone-standard-sequential-colimit (succ-ℕ n) p))
            ( glue-pushout _ _ (s , refl , p))
            ( pr1 (cocone-tA (left-map-span-diagram 𝒮 s) n) p) ＝
          (pr1 (pr2 (cocone-tA (left-map-span-diagram 𝒮 s) n)) (s , refl , concat-s 𝒮 a₀ s n p))
        [key] = {!!}
          --         htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
          -- ( up-standard-sequential-colimit)
          -- ( shift-once-cocone-sequential-diagram
          --   ( cocone-standard-sequential-colimit
          --     ( right-sequential-diagram-zigzag-id-pushout 𝒮 a₀ (right-map-span-diagram 𝒮 s))))
          -- ( hom-diagram-zigzag-sequential-diagram
          --   ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s))


      tS s n p =
        inv
          ( compute-inr-dependent-cogap _ _
            ( cocone-tB (right-map-span-diagram 𝒮 s) n)
            ( s , refl , p))

      alt-tS :
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
      alt-tS s n p =
        {!tS s n p!}
        where
        [ii] =
          pr1
            ( htpy-dependent-cocone-dependent-universal-property-sequential-colimit
              ( dup-standard-sequential-colimit)
              ( cocone-tAA (left-map-span-diagram 𝒮 s)))
            ( n)
            ( p)
        [i] =
          apd
            ( map-family-descent-data-pushout R (s , map-cocone-standard-sequential-colimit n p))
            ( [ii])

      tSS s = dependent-cogap-standard-sequential-colimit (cocone-tSS s)

      pr1 (cocone-tAA a) = tA a
      pr2 (cocone-tAA a) n p = inv (compute-inl-dependent-cogap _ _ (cocone-tA a n) p)

      pr1 (cocone-tBB b) = tB b
      pr2 (cocone-tBB b) n p = inv (compute-inl-dependent-cogap _ _ (cocone-tB b n) p)

      pr1 (cocone-tSS s) = alt-tS s
      pr2 (cocone-tSS s) = {!!}

    alt-tS-tS-equiv :
      (s : spanning-type-span-diagram 𝒮) →
      {!!}
      -- (n : ℕ) →
      -- (p : Path-to-a 𝒮 a₀ (left-map-span-diagram 𝒮 s) n) →
      -- {!!} ≃ {!!}
    alt-tS-tS-equiv s =
      tS-equiv-tS
        ( up-standard-sequential-colimit)
        ( up-shift-cocone-sequential-diagram 1 up-standard-sequential-colimit)
        ( zigzag-sequential-diagram-zigzag-id-pushout 𝒮 a₀ s)
        ( λ p → left-family-descent-data-pushout R (left-map-span-diagram 𝒮 s , p))
        ( λ p → right-family-descent-data-pushout R (right-map-span-diagram 𝒮 s , p))
        ( λ p → equiv-family-descent-data-pushout R (s , p))
        ( tA (left-map-span-diagram 𝒮 s))
        -- ( λ where
        --   zero-ℕ (map-raise refl) → inv (compute-inl-dependent-cogap _ _ (cocone-tA (left-map-span-diagram 𝒮 s) 0) _ ∙ {!!})
        --   (succ-ℕ n) a → {!!} )
        ( λ n p →
          inv
            ( ( compute-inl-dependent-cogap _ _ (cocone-tA (left-map-span-diagram 𝒮 s) n) p) ∙
              {!refl!}))
        ( λ n → tB (right-map-span-diagram 𝒮 s) (succ-ℕ n))
        ( {!!})

  ind-singleton-zigzag-id-pushout' :
    {l5 : Level}
    (R :
      descent-data-pushout
        ( span-diagram-flattening-descent-data-pushout
          ( descent-data-zigzag-id-pushout 𝒮 a₀))
        ( l5))
    (r₀ : left-family-descent-data-pushout R (a₀ , refl-id-pushout 𝒮 a₀)) →
    section-descent-data-pushout R
  pr1 (ind-singleton-zigzag-id-pushout' R r₀) (a , p) =
    tAA R r₀ a p
  pr1 (pr2 (ind-singleton-zigzag-id-pushout' R r₀)) (b , p) =
    tBB R r₀ b p
  pr2 (pr2 (ind-singleton-zigzag-id-pushout' R r₀)) (s , p) =
    tSS R r₀ s p

  is-identity-system-zigzag-id-pushout :
    is-identity-system-descent-data-pushout
      ( descent-data-zigzag-id-pushout 𝒮 a₀)
      ( refl-id-pushout 𝒮 a₀)
  is-identity-system-zigzag-id-pushout =
    is-identity-system-descent-data-pushout-ind-singleton up-c
      ( descent-data-zigzag-id-pushout 𝒮 a₀)
      ( refl-id-pushout 𝒮 a₀)
      ( ind-singleton-zigzag-id-pushout')
```
