# The induction principle of identity types of coequalizers

```agda
{-# OPTIONS --lossy-unification #-}
module synthetic-homotopy-theory.induction-principle-identity-types-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.singleton-induction
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universal-property-identity-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.descent-data-coequalizers
open import synthetic-homotopy-theory.descent-data-coequalizers-equivalence-families
open import synthetic-homotopy-theory.descent-data-coequalizers-function-families
open import synthetic-homotopy-theory.descent-property-coequalizers
open import synthetic-homotopy-theory.equivalences-descent-data-coequalizers
open import synthetic-homotopy-theory.families-descent-data-coequalizers
open import synthetic-homotopy-theory.flattening-lemma-coequalizers
open import synthetic-homotopy-theory.morphisms-descent-data-coequalizers
open import synthetic-homotopy-theory.sections-descent-data-coequalizers
open import synthetic-homotopy-theory.universal-property-coequalizers
```

</details>

## Idea

The formalization is inspired by {{#cite KvR21}}, but uses the dependent
induction principle instead of recursion and uniqueness (i.e. initiality), and
doesn't use wild categories for the arguments.

## Definitions

### The induction principle of descent data for identity types of coequalizers

```agda
module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  (P : descent-data-coequalizer F l3)
  (Q : descent-data-coequalizer F l4)
  where

  ev-point-hom-descent-data-coequalizer :
    {b : codomain-double-arrow F} (p : family-descent-data-coequalizer P b) →
    hom-descent-data-coequalizer P Q →
    family-descent-data-coequalizer Q b
  ev-point-hom-descent-data-coequalizer p h =
    map-hom-descent-data-coequalizer P Q h _ p

module _
  {l1 l2 l3 : Level} {F : double-arrow l1 l2}
  (P : descent-data-coequalizer F l3)
  {b₀ : codomain-double-arrow F}
  (p₀ : family-descent-data-coequalizer P b₀)
  where

  induction-principle-descent-data-identity-type-coequalizer : UUω
  induction-principle-descent-data-identity-type-coequalizer =
    {l : Level}
    (Q :
      descent-data-coequalizer
        ( double-arrow-flattening-lemma-descent-data-coequalizer P)
        ( l)) →
    (q₀ : family-descent-data-coequalizer Q (b₀ , p₀)) →
    Σ ( section-descent-data-coequalizer Q)
      ( λ s → pr1 s (b₀ , p₀) ＝ q₀)
```

### Canonical descent data for identity types of coequalizers

```agda
module _
  {l1 l2 l3 : Level} {F : double-arrow l1 l2}
  {X : UU l3} (c : cofork F X)
  (x₀ : X)
  where

  descent-data-coequalizer-identity-type :
    descent-data-coequalizer F l3
  pr1 descent-data-coequalizer-identity-type b =
    x₀ ＝ map-cofork c b
  pr2 descent-data-coequalizer-identity-type a =
    equiv-concat' x₀ (coh-cofork c a)

  equiv-descent-data-coequalizer-identity-type :
    equiv-descent-data-coequalizer
      ( descent-data-family-cofork c
        ( λ x → x₀ ＝ x))
      ( descent-data-coequalizer-identity-type)
  pr1 equiv-descent-data-coequalizer-identity-type _ =
    id-equiv
  pr2 equiv-descent-data-coequalizer-identity-type a =
    tr-Id-right (coh-cofork c a)

  family-with-descent-data-coequalizer-identity-type :
    family-with-descent-data-coequalizer c l3
  pr1 family-with-descent-data-coequalizer-identity-type x =
    x₀ ＝ x
  pr1 (pr2 family-with-descent-data-coequalizer-identity-type) =
    descent-data-coequalizer-identity-type
  pr2 (pr2 family-with-descent-data-coequalizer-identity-type) =
    equiv-descent-data-coequalizer-identity-type
```

## Properties

### The canonical descent data for identity types of coequalizers satisfies the induction principle

```agda
module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  {X : UU l3} {c : cofork F X}
  (b₀ : codomain-double-arrow F)
  (Q : family-with-descent-data-coequalizer c l4)
  where

  pentagon-ev-point-hom-descent-data-coequalizer :
    ( ( map-family-with-descent-data-coequalizer Q b₀) ∘
      ( ev-refl
        ( map-cofork c b₀)
        { B =
          λ x _ → family-cofork-family-with-descent-data-coequalizer Q x})) ~
    ( ( ev-point-hom-descent-data-coequalizer
        ( descent-data-coequalizer-identity-type c (map-cofork c b₀))
        ( descent-data-family-with-descent-data-coequalizer Q)
        ( refl)) ∘
      ( map-equiv
        ( compute-section-family-cofork-function-family
          ( family-with-descent-data-coequalizer-identity-type c
            ( map-cofork c b₀))
          ( Q))) ∘
      ( section-descent-data-section-family-cofork
        ( family-with-descent-data-coequalizer-function-family
          ( family-with-descent-data-coequalizer-identity-type c
            ( map-cofork c b₀))
          ( Q))))
  pentagon-ev-point-hom-descent-data-coequalizer = refl-htpy

module _
  {l1 l2 l3 : Level} {F : double-arrow l1 l2}
  {X : UU l3} {c : cofork F X}
  (up-c : universal-property-coequalizer c)
  (b₀ : codomain-double-arrow F)
  where

  is-equiv-ev-point-hom-descent-data-coequalizer-identity-type :
    {l4 : Level} (Q : family-with-descent-data-coequalizer c l4) →
    is-equiv
      ( ev-point-hom-descent-data-coequalizer
        ( descent-data-coequalizer-identity-type c (map-cofork c b₀))
        ( descent-data-family-with-descent-data-coequalizer Q)
        ( refl))
  is-equiv-ev-point-hom-descent-data-coequalizer-identity-type Q =
    is-equiv-right-map-triangle
      ( ( map-family-with-descent-data-coequalizer Q b₀) ∘
        ( ev-refl
          ( map-cofork c b₀)
          { B =
            λ x _ → family-cofork-family-with-descent-data-coequalizer Q x}))
      ( ev-point-hom-descent-data-coequalizer
        ( descent-data-coequalizer-identity-type c (map-cofork c b₀))
        ( descent-data-family-with-descent-data-coequalizer Q)
        ( refl))
      ( ( map-equiv
          ( compute-section-family-cofork-function-family
            ( family-with-descent-data-coequalizer-identity-type c
              ( map-cofork c b₀))
            ( Q))) ∘
        ( section-descent-data-section-family-cofork
          ( family-with-descent-data-coequalizer-function-family
            ( family-with-descent-data-coequalizer-identity-type c
              ( map-cofork c b₀))
            ( Q))))
      ( pentagon-ev-point-hom-descent-data-coequalizer b₀ Q)
      ( is-equiv-comp _ _
        ( is-equiv-ev-refl (map-cofork c b₀))
        ( is-equiv-map-family-with-descent-data-coequalizer Q b₀))
      ( is-equiv-comp _ _
        ( is-equiv-section-descent-data-section-family-cofork _ up-c)
        ( is-equiv-map-equiv
          ( compute-section-family-cofork-function-family _ _)))

module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  {X : UU l3} {c : cofork F X}
  (up-c : universal-property-coequalizer c)
  (b₀ : codomain-double-arrow F)
  where

  induction-principle-identity-type-descent-data-coequalizer-identity-type :
    induction-principle-descent-data-identity-type-coequalizer
      ( descent-data-coequalizer-identity-type c (map-cofork c b₀))
      ( refl)
  induction-principle-identity-type-descent-data-coequalizer-identity-type
    Q q₀ =
    ( ( λ b →
        map-hom-descent-data-coequalizer _ _
          ( map-inv-is-equiv is-equiv-ev-point-Q q₀)
          ( b)
          ( eq-is-contr (is-torsorial-Id (map-cofork c b₀)))) ,
      ( λ (a , p) →
        inv
          ( ( ap
              ( map-hom-descent-data-coequalizer _ _
                ( map-inv-is-equiv is-equiv-ev-point-Q q₀)
                ( right-map-double-arrow F a , p ∙ coh-cofork c a))
              ( eq-is-contr
                ( is-prop-is-contr (is-torsorial-Id (map-cofork c b₀)) _ _))) ∙
            ( coherence-hom-descent-data-coequalizer _ _
              ( map-inv-is-equiv is-equiv-ev-point-Q q₀)
              ( a , p)
              ( eq-is-contr (is-torsorial-Id (map-cofork c b₀))))))) ,
    ( ( ap
        ( map-hom-descent-data-coequalizer _ _
          ( map-inv-is-equiv is-equiv-ev-point-Q q₀)
          ( b₀ , refl))
        ( left-inv _)) ∙
      ( is-section-map-inv-is-equiv is-equiv-ev-point-Q q₀))
    where
      cofork-flattening :
        cofork
          ( double-arrow-flattening-lemma-descent-data-coequalizer
            ( descent-data-coequalizer-identity-type c (map-cofork c b₀)))
          ( Σ X (λ x → map-cofork c b₀ ＝ x))
      cofork-flattening =
        cofork-flattening-lemma-descent-coequalizer c
          ( descent-data-coequalizer-identity-type c (map-cofork c b₀))
          ( λ x → map-cofork c b₀ ＝ x)
          ( inv-equiv-descent-data-coequalizer
            ( equiv-descent-data-coequalizer-identity-type c
              ( map-cofork c b₀)))
      up-flattening : universal-property-coequalizer cofork-flattening
      up-flattening =
        flattening-lemma-descent-data-coequalizer
          ( descent-data-coequalizer-identity-type c (map-cofork c b₀))
          ( λ x → map-cofork c b₀ ＝ x)
          ( inv-equiv-descent-data-coequalizer
            ( equiv-descent-data-coequalizer-identity-type c
              ( map-cofork c b₀)))
          ( up-c)
      is-equiv-ev-point-Q :
        is-equiv
          ( ev-point-hom-descent-data-coequalizer
            ( descent-data-coequalizer-identity-type
              ( cofork-flattening)
              ( map-cofork cofork-flattening (b₀ , refl)))
            ( descent-data-family-with-descent-data-coequalizer
              ( family-with-descent-data-coequalizer-descent-data-coequalizer
                ( up-flattening)
              ( Q)))
            ( refl))
      is-equiv-ev-point-Q =
        is-equiv-ev-point-hom-descent-data-coequalizer-identity-type
          ( up-flattening)
          ( b₀ , refl)
          ( family-with-descent-data-coequalizer-descent-data-coequalizer
            ( flattening-lemma-descent-data-coequalizer
              ( descent-data-coequalizer-identity-type c (map-cofork c b₀))
              ( λ x → map-cofork c b₀ ＝ x)
              ( inv-equiv-descent-data-coequalizer
                ( equiv-descent-data-coequalizer-identity-type c
                  ( map-cofork c b₀)))
              ( up-c))
            ( Q))
```

## Theorem

This should eventually be unique uniqueness, i.e. the type of equivalences out
of the descent data for the identity type such that the equivalence sends `refl`
to `p₀` should be contractible, not just inhabited.

```agda
module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  {X : UU l3} {c : cofork F X}
  (up-c : universal-property-coequalizer c)
  (P : family-with-descent-data-coequalizer c l4)
  {b₀ : codomain-double-arrow F}
  (p₀ : family-family-with-descent-data-coequalizer P b₀)
  where

  map-compute-identity-type-coequalizer :
    (x : X) → (map-cofork c b₀ ＝ x) →
    family-cofork-family-with-descent-data-coequalizer P x
  map-compute-identity-type-coequalizer .(map-cofork c b₀) refl =
    map-inv-equiv (equiv-family-with-descent-data-coequalizer P b₀) p₀

  module _
    (ip-P :
      induction-principle-descent-data-identity-type-coequalizer
        ( descent-data-family-with-descent-data-coequalizer P)
        ( p₀))
    where

    ind-singleton-induction-principle-descent-data-identity-type-coequalizer :
      {l : Level} →
      (Q : Σ X (family-cofork-family-with-descent-data-coequalizer P) → UU l) →
      (q₀ :
        Q ( ( map-cofork c b₀) ,
            ( map-inv-equiv
              ( equiv-family-with-descent-data-coequalizer P b₀)
              ( p₀)))) →
      (x : Σ X (family-cofork-family-with-descent-data-coequalizer P)) → Q x
    ind-singleton-induction-principle-descent-data-identity-type-coequalizer
      {l} Q q₀ =
      map-inv-is-equiv
        ( is-equiv-section-descent-data-section-family-cofork
          ( Q , Q-descent-data , id-equiv-descent-data-coequalizer _)
          ( flattening-lemma-descent-data-coequalizer
            ( descent-data-family-with-descent-data-coequalizer P)
            ( family-cofork-family-with-descent-data-coequalizer P)
            ( inv-equiv-descent-data-coequalizer
              ( equiv-descent-data-family-with-descent-data-coequalizer P))
            ( up-c)))
        ( pr1 (ip-P Q-descent-data q₀))
      where
        Q-descent-data :
          descent-data-coequalizer
            ( double-arrow-flattening-lemma-descent-data-coequalizer
              ( descent-data-family-with-descent-data-coequalizer P))
            ( l)
        Q-descent-data =
          descent-data-family-cofork
            ( cofork-flattening-lemma-descent-coequalizer c
              ( descent-data-family-with-descent-data-coequalizer P)
              ( family-cofork-family-with-descent-data-coequalizer P)
              ( inv-equiv-descent-data-coequalizer
                ( equiv-descent-data-family-with-descent-data-coequalizer P)))
            ( Q)

    is-equiv-map-compute-identity-type-coequalizer :
      (x : X) → is-equiv (map-compute-identity-type-coequalizer x)
    is-equiv-map-compute-identity-type-coequalizer =
      fundamental-theorem-id
        ( is-contr-ind-singleton _ _
          ( ind-singleton-induction-principle-descent-data-identity-type-coequalizer))
        ( map-compute-identity-type-coequalizer)

    compute-identity-type-coequalizer :
      (x : X) →
      (map-cofork c b₀ ＝ x) ≃
      family-cofork-family-with-descent-data-coequalizer P x
    pr1 (compute-identity-type-coequalizer x) =
      map-compute-identity-type-coequalizer x
    pr2 (compute-identity-type-coequalizer x) =
      is-equiv-map-compute-identity-type-coequalizer x

    abstract
      uniqueness-induction-principle-identity-type-coequalizer :
        equiv-descent-data-coequalizer
          ( descent-data-coequalizer-identity-type c (map-cofork c b₀))
          ( descent-data-family-with-descent-data-coequalizer P)
      uniqueness-induction-principle-identity-type-coequalizer =
        map-equiv
          ( compute-section-family-cofork-equivalence-family
            ( family-with-descent-data-coequalizer-identity-type c
              ( map-cofork c b₀))
            ( P))
          ( section-descent-data-section-family-cofork
            ( family-with-descent-data-coequalizer-equivalence-family
              ( family-with-descent-data-coequalizer-identity-type c
                ( map-cofork c b₀))
              ( P))
            ( compute-identity-type-coequalizer))

      compute-uniqueness-induction-principle-identity-type-coequalizer :
        map-equiv-descent-data-coequalizer _ _
          ( uniqueness-induction-principle-identity-type-coequalizer)
          ( b₀)
          ( refl) ＝
        p₀
      compute-uniqueness-induction-principle-identity-type-coequalizer =
        is-section-map-inv-equiv
          ( equiv-family-with-descent-data-coequalizer P b₀)
          ( p₀)
```
