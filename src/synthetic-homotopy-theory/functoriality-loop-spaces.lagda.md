# Functoriality of the loop space operation

```agda
{-# OPTIONS --lossy-unification #-}

module synthetic-homotopy-theory.functoriality-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.faithful-maps
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels

open import structured-types.faithful-pointed-maps
open import structured-types.pointed-equivalences
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-sections
open import structured-types.pointed-types

open import synthetic-homotopy-theory.conjugation-loops
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

Any [pointed map](structured-types.pointed-maps.md) `f : A →∗ B` induces a
pointed map `pointed-map-Ω f : Ω A →∗ Ω B` on
[loop spaces](synthetic-homotopy-theory.loop-spaces.md). Furthermore, this
operation respects the groupoidal operations on loop spaces.

## Definition

### The functorial action of Ω on pointed maps

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  map-Ω : type-Ω A → type-Ω B
  map-Ω p =
    tr-type-Ω
      ( preserves-point-pointed-map f)
      ( ap (map-pointed-map f) p)

  preserves-refl-map-Ω : map-Ω refl ＝ refl
  preserves-refl-map-Ω = preserves-refl-tr-Ω (pr2 f)

  pointed-map-Ω : Ω A →∗ Ω B
  pr1 pointed-map-Ω = map-Ω
  pr2 pointed-map-Ω = preserves-refl-map-Ω

  preserves-mul-map-Ω :
    {x y : type-Ω A} → map-Ω (mul-Ω A x y) ＝ mul-Ω B (map-Ω x) (map-Ω y)
  preserves-mul-map-Ω {x} {y} =
    ( ap
      ( tr-type-Ω (preserves-point-pointed-map f))
      ( ap-concat (map-pointed-map f) x y)) ∙
    ( preserves-mul-tr-Ω
      ( preserves-point-pointed-map f)
      ( ap (map-pointed-map f) x)
      ( ap (map-pointed-map f) y))

  preserves-inv-map-Ω :
    (x : type-Ω A) → map-Ω (inv-Ω A x) ＝ inv-Ω B (map-Ω x)
  preserves-inv-map-Ω x =
    ( ap
      ( tr-type-Ω (preserves-point-pointed-map f))
      ( ap-inv (map-pointed-map f) x)) ∙
    ( preserves-inv-tr-Ω
      ( preserves-point-pointed-map f)
      ( ap (map-pointed-map f) x))
```

### The definition of the functorial action of Ω on pointed maps in terms of conjugation

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  map-Ω' : type-Ω A → type-Ω B
  map-Ω' p =
    conjugation-type-Ω
      ( preserves-point-pointed-map f)
      ( ap (map-pointed-map f) p)

  preserves-refl-map-Ω' : map-Ω' refl ＝ refl
  preserves-refl-map-Ω' = preserves-point-conjugation-Ω (pr2 f)

  pointed-map-Ω' : Ω A →∗ Ω B
  pr1 pointed-map-Ω' = map-Ω'
  pr2 pointed-map-Ω' = preserves-refl-map-Ω'

module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  preserves-mul-map-Ω' :
    (f : A →∗ B) {x y : type-Ω A} →
    map-Ω' f (mul-Ω A x y) ＝ mul-Ω B (map-Ω' f x) (map-Ω' f y)
  preserves-mul-map-Ω' (f , refl) {x} {y} =
    equational-reasoning
      ap f (x ∙ y) ∙ refl
      ＝ (ap f x ∙ ap f y) ∙ refl
        by ap (_∙ refl) (ap-concat f x y)
      ＝ ap f x ∙ (ap f y ∙ refl)
        by assoc (ap f x) (ap f y) refl
      ＝ (ap f x ∙ refl) ∙ (ap f y ∙ refl)
        by ap (_∙ (ap f y ∙ refl)) (inv right-unit)

  preserves-inv-map-Ω' :
    (f : A →∗ B) (x : type-Ω A) →
    map-Ω' f (inv-Ω A x) ＝ inv-Ω B (map-Ω' f x)
  preserves-inv-map-Ω' (f , refl) x =
    equational-reasoning
      ap f (inv x) ∙ refl
      ＝ ap f (inv x) by right-unit
      ＝ inv (ap f x) by ap-inv f x
      ＝ inv (ap f x ∙ refl) by ap inv (inv right-unit)
```

### The functorial action of Ω on pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (let a∗ = point-Pointed-Type A)
  where

  htpy-map-Ω' : (f g : A →∗ B) (H : f ~∗ g) → map-Ω' f ~ map-Ω' g
  htpy-map-Ω' f'@(f , p) g'@(g , q) (H , α) ω =
    equational-reasoning
      inv p ∙ (ap f ω ∙ p)
      ＝ inv (H a∗ ∙ q) ∙ (ap f ω ∙ (H a∗ ∙ q))
        by ap (λ u → conjugation-type-Ω u (ap f ω)) α
      ＝ (inv q ∙ inv (H a∗)) ∙ ((ap f ω ∙ H a∗) ∙ q)
        by
        ap-binary (_∙_)
          ( distributive-inv-concat (H a∗) q)
          ( inv-assoc (ap f ω) (H a∗) q)
      ＝ inv q ∙ ((inv (H a∗) ∙ (ap f ω ∙ H a∗)) ∙ q)
        by assoc²-4 (inv q) (inv (H a∗)) (ap f ω ∙ H a∗) q
      ＝ inv q ∙ (ap g ω ∙ q)
        by ap (conjugation-type-Ω q) (compute-conjugate-htpy-ap H ω)

  htpy-map-Ω : (f g : A →∗ B) (H : f ~∗ g) → map-Ω f ~ map-Ω g
  htpy-map-Ω f'@(f , p) g'@(g , refl) (H , refl) ω =
    equational-reasoning
      tr-type-Ω (H a∗ ∙ refl) (ap f ω)
      ＝ tr-type-Ω (H a∗) (ap f ω)
        by ap (λ u → tr-type-Ω u (ap f ω)) right-unit
      ＝ inv (H a∗) ∙ (ap f ω ∙ H a∗)
        by eq-conjugation-tr-type-Ω (H a∗) (ap f ω)
      ＝ ap g ω by compute-conjugate-htpy-ap H ω

  abstract
    coherence-point-htpy-map-Ω :
      (f g : A →∗ B) (H : f ~∗ g) →
      coherence-point-unpointed-htpy-pointed-Π
        ( pointed-map-Ω f)
        ( pointed-map-Ω g)
        ( htpy-map-Ω f g H)
    coherence-point-htpy-map-Ω f'@(f , p) g'@(g , refl) (H , refl) =
      equational-reasoning
        preserves-refl-tr-Ω (H a∗ ∙ refl)
        ＝ ap (λ u → tr-type-Ω u refl) right-unit ∙ preserves-refl-tr-Ω (H a∗)
          by lemma (H a∗)
        ＝
          ( ap (λ u → tr-type-Ω u refl) right-unit) ∙
          ( eq-conjugation-tr-type-Ω (H a∗) refl ∙ left-inv (H a∗))
          by
          ap
            ( (ap (λ u → tr-type-Ω u refl) right-unit) ∙_)
            ( inv
              ( is-section-inv-concat'
                ( left-inv (H a∗))
                ( preserves-refl-tr-Ω (H a∗))) ∙
              ap
                ( _∙ left-inv (H a∗))
                ( compute-eq-conjugation-tr-type-Ω-refl (H a∗)))
        ＝
          ( ap (λ u → tr-type-Ω u refl) right-unit) ∙
          ( eq-conjugation-tr-type-Ω (H a∗) refl) ∙
          ( left-inv (H a∗))
          by
          inv-assoc
            ( ap (λ u → tr-type-Ω u refl) right-unit)
            ( eq-conjugation-tr-type-Ω (H a∗) refl)
            ( left-inv (H a∗))
        ＝
          ( ap (λ u → tr-type-Ω u refl) right-unit) ∙
          ( eq-conjugation-tr-type-Ω (H a∗) refl) ∙
          ( left-inv (H a∗)) ∙
          ( refl)
          by inv right-unit
      where
      lemma :
        {x y : type-Pointed-Type B} (p : x ＝ y) →
        preserves-refl-tr-Ω (p ∙ refl) ＝
        ap (λ u → tr-type-Ω u refl) right-unit ∙ preserves-refl-tr-Ω p
      lemma refl = refl

  pointed-htpy-Ω :
    (f g : A →∗ B) (H : f ~∗ g) → pointed-map-Ω f ~∗ pointed-map-Ω g
  pointed-htpy-Ω f g H = (htpy-map-Ω f g H , coherence-point-htpy-map-Ω f g H)
```

**Comment.** There should be a nicer construction of
`coherence-point-htpy-map-Ω` by designing the appropriate lemmas. Since it is
undesirable to compute with the current construction, it is marked as
`abstract`.

## Properties

### Faithful pointed maps induce embeddings on loop spaces

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  is-emb-map-Ω :
    (f : A →∗ B) → is-faithful (map-pointed-map f) → is-emb (map-Ω f)
  is-emb-map-Ω f H =
    is-emb-comp
      ( tr-type-Ω (preserves-point-pointed-map f))
      ( ap (map-pointed-map f))
      ( is-emb-is-equiv (is-equiv-tr-type-Ω (preserves-point-pointed-map f)))
      ( H (point-Pointed-Type A) (point-Pointed-Type A))

  emb-Ω :
    faithful-pointed-map A B → type-Ω A ↪ type-Ω B
  pr1 (emb-Ω f) =
    map-Ω (pointed-map-faithful-pointed-map f)
  pr2 (emb-Ω f) =
    is-emb-map-Ω
      ( pointed-map-faithful-pointed-map f)
      ( is-faithful-faithful-pointed-map f)
```

### Pointed embeddings induce pointed equivalences on loop spaces

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B) (is-emb-f : is-emb (map-pointed-map f))
  where

  is-equiv-map-Ω-is-emb : is-equiv (map-Ω f)
  is-equiv-map-Ω-is-emb =
    is-equiv-comp
      ( tr-type-Ω (preserves-point-pointed-map f))
      ( ap (map-pointed-map f))
      ( is-emb-f (point-Pointed-Type A) (point-Pointed-Type A))
      ( is-equiv-tr-type-Ω (preserves-point-pointed-map f))

  equiv-map-Ω-is-emb : type-Ω A ≃ type-Ω B
  pr1 equiv-map-Ω-is-emb = map-Ω f
  pr2 equiv-map-Ω-is-emb = is-equiv-map-Ω-is-emb

  pointed-equiv-pointed-map-Ω-is-emb : Ω A ≃∗ Ω B
  pr1 pointed-equiv-pointed-map-Ω-is-emb = equiv-map-Ω-is-emb
  pr2 pointed-equiv-pointed-map-Ω-is-emb = preserves-refl-map-Ω f
```

### The operator `pointed-map-Ω` preserves identities

```agda
module _
  {l1 : Level} {A : Pointed-Type l1}
  where

  preserves-id-map-Ω : map-Ω (id-pointed-map {A = A}) ~ id
  preserves-id-map-Ω = ap-id

  preserves-id-pointed-map-Ω :
    pointed-map-Ω (id-pointed-map {A = A}) ~∗ id-pointed-map
  preserves-id-pointed-map-Ω = preserves-id-map-Ω , refl
```

### The operator `pointed-map-Ω` preserves composition

```agda
module _
  {l1 l2 l3 : Level}
  {A : Pointed-Type l1} {B : Pointed-Type l2} {C : Pointed-Type l3}
  where

  preserves-comp-map-Ω :
    (g : B →∗ C) (f : A →∗ B) → map-Ω (g ∘∗ f) ~ map-Ω g ∘ map-Ω f
  preserves-comp-map-Ω g∗@(g , refl) f∗@(f , refl) = ap-comp g f

  coherence-point-comp-map-Ω :
    (g : B →∗ C) (f : A →∗ B) →
    coherence-point-unpointed-htpy-pointed-Π
      ( pointed-map-Ω (g ∘∗ f))
      ( pointed-map-Ω g ∘∗ pointed-map-Ω f)
      ( preserves-comp-map-Ω g f)
  coherence-point-comp-map-Ω g∗@(g , refl) f∗@(f , refl) = refl

  preserves-comp-pointed-map-Ω :
    (g : B →∗ C) (f : A →∗ B) →
    pointed-map-Ω (g ∘∗ f) ~∗ pointed-map-Ω g ∘∗ pointed-map-Ω f
  preserves-comp-pointed-map-Ω g f =
    ( preserves-comp-map-Ω g f , coherence-point-comp-map-Ω g f)
```

### The operator `pointed-map-Ω` preserves equivalences

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (e : A ≃∗ B)
  where

  equiv-map-Ω-pointed-equiv :
    type-Ω A ≃ type-Ω B
  equiv-map-Ω-pointed-equiv =
    equiv-map-Ω-is-emb
      ( pointed-map-pointed-equiv e)
      ( is-emb-is-equiv (is-equiv-map-pointed-equiv e))
```

### The operator `pointed-map-Ω` preserves pointed equivalences

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (e : A ≃∗ B)
  where

  pointed-equiv-Ω-pointed-equiv :
    Ω A ≃∗ Ω B
  pr1 pointed-equiv-Ω-pointed-equiv =
    equiv-map-Ω-pointed-equiv e
  pr2 pointed-equiv-Ω-pointed-equiv =
    preserves-refl-map-Ω (pointed-map-pointed-equiv e)
```

### The operator `pointed-map-Ω` preserves pointed sections

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  (f : A →∗ B)
  where

  pointed-section-Ω-pointed-section :
    pointed-section f → pointed-section (pointed-map-Ω f)
  pointed-section-Ω-pointed-section (s , H) =
    ( pointed-map-Ω s ,
      concat-pointed-htpy
        ( inv-pointed-htpy (preserves-comp-pointed-map-Ω f s))
        ( concat-pointed-htpy
          ( pointed-htpy-Ω (f ∘∗ s) id-pointed-map H)
          ( preserves-id-pointed-map-Ω)))
```
