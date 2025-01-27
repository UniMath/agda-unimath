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
open import synthetic-homotopy-theory.dependent-sequential-diagrams
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.descent-data-sequential-colimits
open import synthetic-homotopy-theory.functoriality-sequential-colimits
open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.stuff-over
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Theorem

New idea: instead of bruteforcing this direction, show that a square induces
coherent cubes, and show that it's an equivalence because it fits in a diagram.

```agda
nat-lemma :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {P : A → UU l3} {Q : B → UU l4}
  (f : A → B) (h : (a : A) → P a → Q (f a))
  {x y : A} {p : x ＝ y}
  {q : f x ＝ f y} (α : ap f p ＝ q) →
  coherence-square-maps
    ( tr P p)
    ( h x)
    ( h y)
    ( tr Q q)
nat-lemma f h {p = p} refl x =
  substitution-law-tr _ f p ∙ inv (preserves-tr h p x)
```

```agda
open import synthetic-homotopy-theory.families-descent-data-sequential-colimits
open import synthetic-homotopy-theory.total-cocones-families-sequential-diagrams
open import synthetic-homotopy-theory.total-sequential-diagrams

open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.functoriality-dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import synthetic-homotopy-theory.sequential-colimits
open import synthetic-homotopy-theory.functoriality-sequential-colimits
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  (P : family-with-descent-data-sequential-colimit c l3)
  {Y : UU l4}
  {c' :
    cocone-sequential-diagram
      ( total-sequential-diagram-family-with-descent-data-sequential-colimit P)
      ( Y)}
  (up-c' : universal-property-sequential-colimit c')
  where

  mediating-cocone :
    cocone-sequential-diagram
      ( total-sequential-diagram-family-with-descent-data-sequential-colimit P)
      ( Σ X (family-cocone-family-with-descent-data-sequential-colimit P))
  pr1 mediating-cocone n =
    map-Σ
      ( family-cocone-family-with-descent-data-sequential-colimit P)
      ( map-cocone-sequential-diagram c n)
      ( λ a → map-equiv-descent-data-family-with-descent-data-sequential-colimit P n a)
  pr2 mediating-cocone n (a , p) =
    eq-pair-Σ
      ( coherence-cocone-sequential-diagram c n a)
      ( inv
        ( coherence-square-equiv-descent-data-family-with-descent-data-sequential-colimit P n a p))

  totι' : Y → Σ X (family-cocone-family-with-descent-data-sequential-colimit P)
  totι' =
    map-universal-property-sequential-colimit up-c' mediating-cocone
  triangle-pr1∞-pr1 :
    pr1-sequential-colimit-total-sequential-diagram
      ( dependent-sequential-diagram-family-with-descent-data-sequential-colimit P)
      ( up-c')
      ( c) ~
    pr1 ∘ totι'
  triangle-pr1∞-pr1 =
    htpy-htpy-out-of-sequential-colimit up-c'
      ( concat-htpy-cocone-sequential-diagram
        ( htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c' c
          ( pr1-total-sequential-diagram
            ( dependent-sequential-diagram-family-with-descent-data-sequential-colimit P)))
        ( ( λ n →
            inv-htpy (pr1 ·l (pr1 (htpy-cocone-universal-property-sequential-colimit up-c' mediating-cocone) n))) ,
          ( λ n x →
            ap (_∙ inv (ap pr1 (pr1 (htpy-cocone-universal-property-sequential-colimit up-c' mediating-cocone) (succ-ℕ n) _))) right-unit ∙
            horizontal-inv-coherence-square-identifications _
              ( ap (pr1 ∘ totι') (coherence-cocone-sequential-diagram c' n x))
              ( coherence-cocone-sequential-diagram c n (pr1 x))
              _
              ( ( ap
                  ( _∙ ap pr1
                    ( pr1 (htpy-cocone-universal-property-sequential-colimit up-c' mediating-cocone) (succ-ℕ n) _))
                  ( ap-comp pr1
                    ( totι')
                    ( coherence-cocone-sequential-diagram c' n x))) ∙
                ( inv
                  ( ap-concat pr1
                    ( ap
                      ( totι')
                      ( coherence-cocone-sequential-diagram c' n x)) _)) ∙
                ( ap (ap pr1) (pr2 (htpy-cocone-universal-property-sequential-colimit up-c' mediating-cocone) n x)) ∙
                ( ap-concat pr1
                  ( pr1
                    ( htpy-cocone-universal-property-sequential-colimit up-c' mediating-cocone)
                    n x)
                  ( coherence-cocone-sequential-diagram mediating-cocone n x)) ∙
                ( ap
                  ( ap pr1
                    ( pr1
                      ( htpy-cocone-universal-property-sequential-colimit up-c' mediating-cocone)
                      n x) ∙_)
                  ( ap-pr1-eq-pair-Σ
                    ( coherence-cocone-sequential-diagram c n (pr1 x))
                    ( _)))))))
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : sequential-diagram l1} {X : UU l2}
  {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {B : sequential-diagram l3} {Y : UU l4}
  {c' : cocone-sequential-diagram B Y}
  (up-c' : universal-property-sequential-colimit c')
  (P : X → UU l5) (Q : Y → UU l6)
  (f : hom-sequential-diagram A B)
  (f' :
    (x : X) → P x →
    Q (map-sequential-colimit-hom-sequential-diagram up-c c' f x))
  where

  open import synthetic-homotopy-theory.flattening-lemma-sequential-colimits

  ΣAP : sequential-diagram (l1 ⊔ l5)
  ΣAP =
    total-sequential-diagram (dependent-sequential-diagram-family-cocone c P)

  ΣBQ : sequential-diagram (l3 ⊔ l6)
  ΣBQ =
    total-sequential-diagram (dependent-sequential-diagram-family-cocone c' Q)

  totff' : hom-sequential-diagram ΣAP ΣBQ
  pr1 totff' n =
    map-Σ _
      ( map-hom-sequential-diagram B f n)
      ( λ a →
        tr Q
          ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
            up-c c' f n a) ∘
        f' (map-cocone-sequential-diagram c n a))
  pr2 totff' = {!!}

  totff'∞ : Σ X P → Σ Y Q
  totff'∞ =
    map-sequential-colimit-hom-sequential-diagram
      ( flattening-lemma-sequential-colimit _ P up-c)
      ( total-cocone-family-cocone-sequential-diagram c' Q)
      ( totff')

  _ :
    totι' up-c
      ( family-with-descent-data-family-cocone-sequential-diagram c P)
      ( flattening-lemma-sequential-colimit c P up-c) ~
    id
  _ =
    compute-map-universal-property-sequential-colimit-id
      ( flattening-lemma-sequential-colimit _ P up-c)

  _ :
    coherence-square-maps
      ( totι' up-c
        ( family-with-descent-data-family-cocone-sequential-diagram c P)
        ( flattening-lemma-sequential-colimit c P up-c))
      ( totff'∞)
      ( map-Σ Q
        ( map-sequential-colimit-hom-sequential-diagram up-c c' f)
        f')
      ( totι' up-c'
        ( family-with-descent-data-family-cocone-sequential-diagram c' Q)
        ( flattening-lemma-sequential-colimit c' Q up-c'))
  _ =
    ( compute-map-universal-property-sequential-colimit-id
      ( flattening-lemma-sequential-colimit c' Q up-c') ·r _) ∙h
    ( htpy-htpy-out-of-sequential-colimit
      ( flattening-lemma-sequential-colimit c P up-c)
      ( concat-htpy-cocone-sequential-diagram
        ( htpy-cocone-map-sequential-colimit-hom-sequential-diagram
          ( flattening-lemma-sequential-colimit c P up-c)
          ( total-cocone-family-cocone-sequential-diagram c' Q)
          ( totff'))
        ( ( λ n (a , p) →
            inv
              ( eq-pair-Σ
                ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c'
                  ( f)
                  ( n)
                  ( a))
                refl)) ,
          {!!}))) ∙h
    ( _ ·l
      ( inv-htpy
        (compute-map-universal-property-sequential-colimit-id
          ( flattening-lemma-sequential-colimit c P up-c))))

    -- htpy-htpy-out-of-sequential-colimit
    --   ( flattening-lemma-sequential-colimit c P up-c)
    --   ( {!!})
```

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1} {X : UU l2}
  {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {B : sequential-diagram l3} {Y : UU l4}
  {c' : cocone-sequential-diagram B Y}
  (up-c' : universal-property-sequential-colimit c')
  (f : hom-sequential-diagram A B)
  where
  open import foundation.homotopies-morphisms-arrows

  interm :
    coherence-square-maps
      ( id)
      ( map-sequential-colimit-hom-sequential-diagram up-c c' f)
      ( map-sequential-colimit-hom-sequential-diagram up-c c' f)
      ( id)
  interm =
    htpy-map-sequential-colimit-htpy-hom-sequential-diagram up-c c'
      ( refl-htpy-hom-sequential-diagram A B f)

  preserves-refl-htpy-sequential-colimit :
    htpy-hom-arrow
      ( map-sequential-colimit-hom-sequential-diagram up-c c' f)
      ( map-sequential-colimit-hom-sequential-diagram up-c c' f)
      ( id , id , interm)
      ( id , id , refl-htpy)
  pr1 preserves-refl-htpy-sequential-colimit = refl-htpy
  pr1 (pr2 preserves-refl-htpy-sequential-colimit) = refl-htpy
  pr2 (pr2 preserves-refl-htpy-sequential-colimit) =
    right-unit-htpy ∙h
    htpy-eq
      ( ap
        ( htpy-eq ∘ ap (map-sequential-colimit-hom-sequential-diagram up-c c'))
        ( is-retraction-map-inv-equiv
          ( extensionality-hom-sequential-diagram A B f f)
          ( refl)))
```

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
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1}
  (B : sequential-diagram l2)
  (f : hom-sequential-diagram A B)
  (P : descent-data-sequential-colimit A l3)
  (Q : descent-data-sequential-colimit B l4)
  where

  hom-over-hom : UU (l1 ⊔ l3 ⊔ l4)
  hom-over-hom =
    Σ ( (n : ℕ) (a : family-sequential-diagram A n) →
        family-descent-data-sequential-colimit P n a →
        family-descent-data-sequential-colimit Q n
          ( map-hom-sequential-diagram B f n a))
      ( λ f'n →
        (n : ℕ) →
        square-over
          { Q4 = family-descent-data-sequential-colimit Q (succ-ℕ n)}
          ( map-sequential-diagram A n)
          ( map-hom-sequential-diagram B f n)
          ( map-hom-sequential-diagram B f (succ-ℕ n))
          ( map-sequential-diagram B n)
          ( λ {a} → map-family-descent-data-sequential-colimit P n a)
          ( λ {a} → f'n n a)
          ( λ {a} → f'n (succ-ℕ n) a)
          ( λ {a} → map-family-descent-data-sequential-colimit Q n a)
          ( naturality-map-hom-sequential-diagram B f n))
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : sequential-diagram l1} {X : UU l2}
  {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {B : sequential-diagram l3} {Y : UU l4}
  {c' : cocone-sequential-diagram B Y}
  (up-c' : universal-property-sequential-colimit c')
  (f : hom-sequential-diagram A B)
  (P : X → UU l5) (Q : Y → UU l6)
  where

  private
    f∞ : X → Y
    f∞ = map-sequential-colimit-hom-sequential-diagram up-c c' f
    DDMO : descent-data-sequential-colimit A (l5 ⊔ l6)
    pr1 DDMO n a =
      P (map-cocone-sequential-diagram c n a) →
      Q (map-cocone-sequential-diagram c' n (map-hom-sequential-diagram B f n a))
    pr2 DDMO n a =
      ( equiv-postcomp _
        ( ( equiv-tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( naturality-map-hom-sequential-diagram B f n a)) ∘e
          ( equiv-tr Q (coherence-cocone-sequential-diagram c' n _)))) ∘e
      ( equiv-precomp
        ( inv-equiv (equiv-tr P (coherence-cocone-sequential-diagram c n a)))
        ( _))

  sect-over-DDMO-map-over :
    ((a : X) → P a → Q (f∞ a)) →
    section-descent-data-sequential-colimit DDMO
  pr1 (sect-over-DDMO-map-over f∞') n a =
    ( tr Q
      ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f n a)) ∘
    ( f∞' (map-cocone-sequential-diagram c n a))
  pr2 (sect-over-DDMO-map-over f∞') n a =
    eq-htpy
      ( λ p →
        {!coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f n a!})

  sect-over-DDMO-map-over' :
    ((a : X) → P a → Q (f∞ a)) →
    section-descent-data-sequential-colimit DDMO
  sect-over-DDMO-map-over' =
    {!sect-family-sect-dd-sequential-colimit!}

  map-over-sect-DDMO :
    section-descent-data-sequential-colimit DDMO →
    hom-over-hom B f
      ( descent-data-family-cocone-sequential-diagram c P)
      ( descent-data-family-cocone-sequential-diagram c' Q)
  map-over-sect-DDMO =
    tot
      ( λ s →
        map-Π
          ( λ n →
            ( map-implicit-Π
              ( λ a →
                ( concat-htpy
                  ( inv-htpy
                    ( ( ( tr
                          ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
                          ( naturality-map-hom-sequential-diagram B f n a)) ∘
                        ( tr Q
                          ( coherence-cocone-sequential-diagram c' n
                            (map-hom-sequential-diagram B f n a))) ∘
                        ( s n a)) ·l
                      ( is-retraction-inv-tr P
                        ( coherence-cocone-sequential-diagram c n a))))
                  ( _)) ∘
                ( map-equiv
                  ( equiv-htpy-precomp-htpy-Π _ _
                    ( equiv-tr P
                      ( coherence-cocone-sequential-diagram c n a)))) ∘
                ( htpy-eq
                  {f =
                    ( tr
                      ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
                      ( naturality-map-hom-sequential-diagram B f n a)) ∘
                    ( tr Q
                      ( coherence-cocone-sequential-diagram c' n
                        ( map-hom-sequential-diagram B f n a))) ∘
                    ( s n a) ∘
                    ( tr P (inv (coherence-cocone-sequential-diagram c n a)))}
                  { s (succ-ℕ n) (map-sequential-diagram A n a)}))) ∘
            ( implicit-explicit-Π)))

  map-over-diagram-map-over-colimit :
    ((a : X) → P a → Q (f∞ a)) →
    hom-over-hom B f
      ( descent-data-family-cocone-sequential-diagram c P)
      ( descent-data-family-cocone-sequential-diagram c' Q)
  pr1 (map-over-diagram-map-over-colimit f∞') n a =
    ( tr Q
      ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f n a)) ∘
    ( f∞' (map-cocone-sequential-diagram c n a))
  pr2 (map-over-diagram-map-over-colimit f∞') n {a} =
    pasting-vertical-coherence-square-maps
      ( tr P (coherence-cocone-sequential-diagram c n a))
      ( f∞' _)
      ( f∞' _)
      ( tr Q (ap f∞ (coherence-cocone-sequential-diagram c n a)))
      ( tr Q (htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f _ a))
      ( tr Q (htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f _ (map-sequential-diagram A n a)))
      ( ( tr
          ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
          ( naturality-map-hom-sequential-diagram B f n a)) ∘
        ( tr Q (coherence-cocone-sequential-diagram c' n (map-hom-sequential-diagram B f n a))))
      ( λ q →
        substitution-law-tr Q f∞ (coherence-cocone-sequential-diagram c n a) ∙
        inv (preserves-tr f∞' (coherence-cocone-sequential-diagram c n a) q))
      ( ( inv-htpy
          ( λ q →
            ( tr-concat
              ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
                up-c c' f n a)
              ( _)
              ( q)) ∙
            ( tr-concat
              ( coherence-cocone-sequential-diagram c' n (map-hom-sequential-diagram B f n a))
              ( ap (map-cocone-sequential-diagram c' (succ-ℕ n)) (naturality-map-hom-sequential-diagram B f n a))
              ( tr Q
                ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
                  up-c c' f n a)
                ( q))) ∙
            ( substitution-law-tr Q
              ( map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a)))) ∙h
        ( λ q →
          ap
            ( λ p → tr Q p q)
            ( inv
              ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f n a))) ∙h
        ( tr-concat
          ( ap f∞ (coherence-cocone-sequential-diagram c n a))
          ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
            up-c c' f (succ-ℕ n) (map-sequential-diagram A n a))))

  abstract
    triangle-map-over-sect-DDMO :
      coherence-triangle-maps
        ( map-over-diagram-map-over-colimit)
        ( map-over-sect-DDMO)
        ( sect-over-DDMO-map-over)
    triangle-map-over-sect-DDMO f∞' =
      eq-pair-eq-fiber
        ( eq-htpy
          ( λ n →
            eq-htpy-implicit
              ( λ a →
                eq-htpy
                  ( λ p →
                    {!!}))))

    is-equiv-map-over-sect-DDMO :
      is-equiv map-over-sect-DDMO
    is-equiv-map-over-sect-DDMO =
      is-equiv-tot-is-fiberwise-equiv
        ( λ s →
          is-equiv-map-Π-is-fiberwise-equiv
            ( λ n →
              is-equiv-comp _ _
                ( is-equiv-implicit-explicit-Π)
                ( is-equiv-map-implicit-Π-is-fiberwise-equiv
                  ( λ a →
                    is-equiv-comp _ _
                      ( funext _ _)
                      ( is-equiv-comp _ _
                        ( is-equiv-map-equiv (equiv-htpy-precomp-htpy-Π _ _ _))
                        ( is-equiv-concat-htpy _ _))))))

    is-equiv-map-over-diagram-map-over-colimit :
      is-equiv map-over-diagram-map-over-colimit
    is-equiv-map-over-diagram-map-over-colimit =
      {!is-equiv-left-map-triangle
        ( map-over-diagram-map-over-colimit)
        ( map-over-sect-DDMO)
        ( sect-over-DDMO-map-over)
        ( triangle-map-over-sect-DDMO)
        ( is-equiv) !}
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
    f'∞n-square-over {n} {a} =
      pasting-vertical-coherence-square-maps
        ( tr P (coherence-cocone-sequential-diagram c n a))
        ( f'∞)
        ( f'∞)
        ( tr Q (ap f∞ (coherence-cocone-sequential-diagram c n a)))
        ( tr Q (htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' H _ a))
        ( tr Q (htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' H _ (an a)))
        ( ( tr
            ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
            ( Hn a)) ∘
          ( tr Q (coherence-cocone-sequential-diagram c' n (fn a))))
        ( λ q →
          substitution-law-tr Q f∞ (coherence-cocone-sequential-diagram c n a) ∙
          inv (preserves-tr (λ p → f'∞ {p}) (coherence-cocone-sequential-diagram c n a) q))
        ( ( inv-htpy
            ( λ q →
              ( tr-concat
                ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
                  up-c c' H n a)
                ( _)
                ( q)) ∙
              ( tr-concat
                ( coherence-cocone-sequential-diagram c' n (fn a))
                ( ap (map-cocone-sequential-diagram c' (succ-ℕ n)) (Hn a))
                ( tr Q
                  ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
                    up-c c' H n a)
                  ( q))) ∙
              ( substitution-law-tr Q
                ( map-cocone-sequential-diagram c' (succ-ℕ n))
                ( Hn a)))) ∙h
          ( λ q →
            ap
              ( λ p → tr Q p q)
              ( inv
                ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' H n a))) ∙h
          ( tr-concat
            ( ap f∞ (coherence-cocone-sequential-diagram c n a))
            ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
              up-c c' H (succ-ℕ n) (an a))))

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
        ( tS ,
          ( λ n a →
            map-compute-dependent-identification-eq-value
              ( f'∞ ∘ sA∞)
              ( sB∞ ∘ f∞)
              ( coherence-cocone-sequential-diagram c n a)
              ( tS n a)
              ( tS (succ-ℕ n) (an a))
              ( {!f'∞n-square-over!})))
      where
        sA∞ : (x : X) → P x
        sA∞ = sect-family-sect-dd-sequential-colimit up-c P sA
        sB∞ : (y : Y) → Q y
        sB∞ = sect-family-sect-dd-sequential-colimit up-c' Q sB
        tS :
          (n : ℕ) →
          (f'∞ ∘ sA∞ ∘ (map-cocone-sequential-diagram c n)) ~
          (sB∞ ∘ f∞ ∘ map-cocone-sequential-diagram c n)
        tS n a =
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
                      ( sB)) n (fn a)))
```
