# Descent property of sequential colimits

```agda
module synthetic-homotopy-theory.descent-property-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.descent-data-sequential-colimits
open import synthetic-homotopy-theory.families-descent-data-sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

The
{{#concept "descent property" Disambiguation="sequential colimits" Agda=equiv-descent-data-family-cocone-sequential-diagram}}
of
[sequential colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md)
characterizes type families over sequential colimits as
[descent data](synthetic-homotopy-theory.descent-data-sequential-colimits.md)
over the base
[sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md).

Given a sequential diagram `(A, a)` and a
[cocone](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md) with
vertex `X`, there is a commuting triangle

```text
          cocone-map
  (X → 𝒰) ---------> cocone A 𝒰
           \       /
            \     /
             \   /
              ∨ ∨
         descent-data A .
```

From [univalence](foundation-core.univalence.md) it follows that the right map
is an equivalence. If `X` is a colimit of `A`, then we have that the top map is
an equivalence, which imples that the left map is an equivalence.

## Theorem

```agda
module _
  {l1 : Level} {A : sequential-diagram l1}
  where

  equiv-descent-data-cocone-sequential-diagram :
    {l2 : Level} →
    cocone-sequential-diagram A (UU l2) ≃
    descent-data-sequential-colimit A l2
  equiv-descent-data-cocone-sequential-diagram =
    equiv-tot
      ( λ B →
        equiv-Π-equiv-family
          ( λ n → equiv-Π-equiv-family (λ a → equiv-univalence)))

  descent-data-cocone-sequential-diagram :
    {l2 : Level} →
    cocone-sequential-diagram A (UU l2) →
    descent-data-sequential-colimit A l2
  descent-data-cocone-sequential-diagram =
    map-equiv equiv-descent-data-cocone-sequential-diagram

  is-equiv-descent-data-cocone-sequential-diagram :
    {l2 : Level} → is-equiv (descent-data-cocone-sequential-diagram {l2})
  is-equiv-descent-data-cocone-sequential-diagram =
    is-equiv-map-equiv equiv-descent-data-cocone-sequential-diagram

module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} (c : cocone-sequential-diagram A X)
  where

  triangle-descent-data-family-cocone-sequential-diagram :
    {l3 : Level} →
    coherence-triangle-maps
      ( descent-data-family-cocone-sequential-diagram c)
      ( descent-data-cocone-sequential-diagram)
      ( cocone-map-sequential-diagram c {Y = UU l3})
  triangle-descent-data-family-cocone-sequential-diagram P =
    eq-pair-eq-fiber
      ( eq-binary-htpy _ _
        ( λ n a →
          inv
            ( compute-equiv-eq-ap
              ( coherence-cocone-sequential-diagram c n a))))

module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  where

  is-equiv-descent-data-family-cocone-sequential-diagram :
    is-equiv (descent-data-family-cocone-sequential-diagram c {l3})
  is-equiv-descent-data-family-cocone-sequential-diagram =
    is-equiv-left-map-triangle
      ( descent-data-family-cocone-sequential-diagram c)
      ( descent-data-cocone-sequential-diagram)
      ( cocone-map-sequential-diagram c)
      ( triangle-descent-data-family-cocone-sequential-diagram c)
      ( up-c (UU l3))
      ( is-equiv-descent-data-cocone-sequential-diagram)

  equiv-descent-data-family-cocone-sequential-diagram :
    (X → UU l3) ≃ descent-data-sequential-colimit A l3
  pr1 equiv-descent-data-family-cocone-sequential-diagram =
    descent-data-family-cocone-sequential-diagram c
  pr2 equiv-descent-data-family-cocone-sequential-diagram =
    is-equiv-descent-data-family-cocone-sequential-diagram

  family-cocone-descent-data-sequential-colimit :
    descent-data-sequential-colimit A l3 → (X → UU l3)
  family-cocone-descent-data-sequential-colimit =
    map-inv-equiv
      ( equiv-descent-data-family-cocone-sequential-diagram)
```

```agda
open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.morphisms-dependent-sequential-diagrams
open import synthetic-homotopy-theory.descent-data-function-types-over-sequential-colimits
open import foundation.action-on-identifications-functions
open import foundation.transport-along-higher-identifications
open import foundation.transport-along-identifications
open import foundation.function-types
open import foundation.whiskering-homotopies-composition
open import foundation.homotopies
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  {P : A → UU l3} {Q : B → UU l4}
  (f : A → B) (h : (a : A) → P a → Q (f a))
  where

  other-nat-lemma :
    {x y : A} (p : x ＝ y) (q : f x ＝ f y) (α : ap f p ＝ q) →
    (z : P x) →
    tr Q q (h x z) ＝ h y (tr P p z)
  other-nat-lemma p q α z = inv (preserves-tr h p z ∙ (inv (substitution-law-tr Q f p) ∙ tr² Q α _))
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : sequential-diagram l1} {B : sequential-diagram l2}
  {X : UU l3} {c : cocone-sequential-diagram A X}
  {Y : UU l4} {c' : cocone-sequential-diagram B Y}
  (P : family-with-descent-data-sequential-colimit c l5)
  (Q : family-with-descent-data-sequential-colimit c' l6)
  (f : hom-sequential-diagram A B)
  (f∞ : X → Y)
  (C :
    (n : ℕ) →
    coherence-square-maps
      ( map-hom-sequential-diagram B f n)
      ( map-cocone-sequential-diagram c n)
      ( map-cocone-sequential-diagram c' n)
      ( f∞))
  (α :
    (n : ℕ) →
    ( (f∞ ·l (coherence-cocone-sequential-diagram c n)) ∙h
      ( C (succ-ℕ n) ·r map-sequential-diagram A n)) ~
    ( ( C n) ∙h
      ( coherence-cocone-sequential-diagram c' n ·r (map-hom-sequential-diagram B f n)) ∙h
      ( map-cocone-sequential-diagram c' (succ-ℕ n) ·l naturality-map-hom-sequential-diagram B f n)))
  where

  dd-alt-pullback : descent-data-sequential-colimit A l6
  pr1 dd-alt-pullback n a =
    family-cocone-family-with-descent-data-sequential-colimit Q
      ( map-cocone-sequential-diagram c' n
        ( map-hom-sequential-diagram B f n a))
  pr2 dd-alt-pullback n a =
    equiv-tr
      ( family-cocone-family-with-descent-data-sequential-colimit Q)
      ( ap
        ( map-cocone-sequential-diagram c' (succ-ℕ n))
        ( naturality-map-hom-sequential-diagram B f n a)) ∘e
    equiv-tr
      ( family-cocone-family-with-descent-data-sequential-colimit Q)
      ( coherence-cocone-sequential-diagram c' n
        ( map-hom-sequential-diagram B f n a))

  dd-alt-precomp : descent-data-sequential-colimit A l6
  pr1 dd-alt-precomp n a =
    family-family-with-descent-data-sequential-colimit Q n
      ( map-hom-sequential-diagram B f n a)
  pr2 dd-alt-precomp n a =
    ( equiv-tr
      ( family-family-with-descent-data-sequential-colimit Q (succ-ℕ n))
      ( naturality-map-hom-sequential-diagram B f n a)) ∘e
    ( equiv-family-family-with-descent-data-sequential-colimit Q n
      ( map-hom-sequential-diagram B f n a))

  equiv-dd-foo :
    equiv-descent-data-sequential-colimit
      ( descent-data-family-cocone-sequential-diagram c
        ( family-cocone-family-with-descent-data-sequential-colimit Q ∘ f∞))
      ( dd-alt-pullback)
  pr1 equiv-dd-foo n a =
    equiv-tr
      ( family-cocone-family-with-descent-data-sequential-colimit Q)
      ( C n a)
  pr2 equiv-dd-foo n a q =
    ( ap
      ( tr (family-cocone-family-with-descent-data-sequential-colimit Q) (C (succ-ℕ n) (map-sequential-diagram A n a)))
      ( inv
        ( substitution-law-tr
          ( family-cocone-family-with-descent-data-sequential-colimit Q)
          ( f∞)
          ( coherence-cocone-sequential-diagram c n a)))) ∙
    ( inv
      ( tr-concat
        ( ap f∞ (coherence-cocone-sequential-diagram c n a))
        ( C (succ-ℕ n) (map-sequential-diagram A n a))
        ( q))) ∙
    ( tr²
      ( family-cocone-family-with-descent-data-sequential-colimit Q)
      ( α n a)
      ( q)) ∙
    ( tr-concat (C n a ∙ pr2 c' n (pr1 f n a)) _ q) ∙
    ap
      ( tr (family-cocone-family-with-descent-data-sequential-colimit Q) (ap (pr1 c' (succ-ℕ n)) (pr2 f n a)))
      ( tr-concat (C n a) (pr2 c' n (pr1 f n a)) q)

  private
    inv-equiv-e :
      equiv-descent-data-sequential-colimit
        ( descent-data-family-cocone-sequential-diagram c'
          ( family-cocone-family-with-descent-data-sequential-colimit Q))
        ( descent-data-family-with-descent-data-sequential-colimit Q)
    inv-equiv-e =
      inv-equiv-descent-data-sequential-colimit
        ( descent-data-family-with-descent-data-sequential-colimit Q)
        ( descent-data-family-cocone-sequential-diagram c'
          ( family-cocone-family-with-descent-data-sequential-colimit Q))
        ( equiv-descent-data-family-with-descent-data-sequential-colimit Q)

  equiv-equiv-dd-foo' : (n : ℕ) (b : family-sequential-diagram B n) →
    ( family-cocone-family-with-descent-data-sequential-colimit Q
      ( map-cocone-sequential-diagram c' n b)) ≃
    ( family-family-with-descent-data-sequential-colimit Q n b)
  equiv-equiv-dd-foo' =
    equiv-equiv-descent-data-sequential-colimit
      ( descent-data-family-cocone-sequential-diagram c'
        ( family-cocone-family-with-descent-data-sequential-colimit Q))
      ( descent-data-family-with-descent-data-sequential-colimit Q)
      ( inv-equiv-e)

  equiv-dd-foo' :
    equiv-descent-data-sequential-colimit
      ( dd-alt-pullback)
      ( dd-alt-precomp)
  pr1 equiv-dd-foo' n a =
    equiv-equiv-dd-foo' n (map-hom-sequential-diagram B f n a)
  pr2 equiv-dd-foo' n a =
    pasting-vertical-coherence-square-maps
      ( map-equiv (equiv-equiv-dd-foo' n (map-hom-sequential-diagram B f n a)))
      ( tr
        ( family-cocone-family-with-descent-data-sequential-colimit Q)
        ( pr2 c' n (pr1 f n a)))
      ( map-family-family-with-descent-data-sequential-colimit Q n (map-hom-sequential-diagram B f n a))
      ( map-equiv
        ( equiv-equiv-dd-foo'
          ( succ-ℕ n)
          ( map-sequential-diagram B n (map-hom-sequential-diagram B f n a))))
      ( tr
        ( family-cocone-family-with-descent-data-sequential-colimit Q)
        ( ap (map-cocone-sequential-diagram c' (succ-ℕ n)) (pr2 f n a)))
      ( tr
        ( family-family-with-descent-data-sequential-colimit Q (succ-ℕ n))
        ( pr2 f n a))
      ( map-equiv
        ( equiv-equiv-dd-foo'
          ( succ-ℕ n)
          ( map-hom-sequential-diagram B f (succ-ℕ n) (map-sequential-diagram A n a))))
      ( coh-equiv-descent-data-sequential-colimit
        ( descent-data-family-cocone-sequential-diagram c'
          ( family-cocone-family-with-descent-data-sequential-colimit Q))
        ( descent-data-family-with-descent-data-sequential-colimit Q)
        ( inv-equiv-e)
        ( n)
        ( map-hom-sequential-diagram B f n a))
      ( ( ( map-equiv
            ( equiv-equiv-dd-foo'
              ( succ-ℕ n)
              ( map-hom-sequential-diagram B f
                ( succ-ℕ n)
                ( map-sequential-diagram A n a)))) ·l
          ( λ z →
            substitution-law-tr
              ( family-cocone-family-with-descent-data-sequential-colimit Q)
              ( map-cocone-sequential-diagram c' (succ-ℕ n))
              ( naturality-map-hom-sequential-diagram B f n a) {z})) ∙h
        ( inv-htpy
          ( other-nat-lemma id
            ( λ b → map-equiv (equiv-equiv-dd-foo' (succ-ℕ n) b))
            ( pr2 f n a)
            ( pr2 f n a)
            ( ap-id (pr2 f n a)))))

  hom-over-map-over :
    ( (x : X) →
      family-cocone-family-with-descent-data-sequential-colimit P x →
      family-cocone-family-with-descent-data-sequential-colimit Q (f∞ x)) ≃
    ( hom-dependent-sequential-diagram-over
      ( dependent-sequential-diagram-family-with-descent-data-sequential-colimit P)
      ( dependent-sequential-diagram-family-with-descent-data-sequential-colimit Q)
      ( f))
  hom-over-map-over =
    ( equiv-tot
      ( λ g →
        equiv-Π-equiv-family
          ( λ n → equiv-Π-equiv-family (λ a → equiv-inv-htpy _ _)))) ∘e
    ( equiv-hom-descent-data-map-family-cocone-sequential-diagram P
      ( family-cocone-family-with-descent-data-sequential-colimit Q ∘ f∞ ,
        dd-alt-precomp ,
        inv-equiv-descent-data-sequential-colimit
          ( descent-data-family-cocone-sequential-diagram c
            ( family-cocone-family-with-descent-data-sequential-colimit Q ∘ f∞))
          ( dd-alt-precomp)
          ( comp-equiv-descent-data-sequential-colimit
            ( descent-data-family-cocone-sequential-diagram c
              ( family-cocone-family-with-descent-data-sequential-colimit Q ∘ f∞))
            ( dd-alt-pullback)
            ( dd-alt-precomp)
            ( equiv-dd-foo')
            ( equiv-dd-foo))))
```
