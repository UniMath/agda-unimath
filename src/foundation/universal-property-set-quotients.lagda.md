# The universal property of set quotients

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.universal-property-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.effective-maps-equivalence-relations
open import foundation.epimorphisms-with-respect-to-sets
open import foundation.equivalence-classes
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.images
open import foundation.injective-maps
open import foundation.locally-small-types
open import foundation.logical-equivalences
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-image
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.small-types
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.type-theoretic-principle-of-choice
open import foundation-core.univalence
```

</details>

## Idea

The universal property of set quotients characterizes maps out of set quotients.

## Definitions

### The universal property of set quotients

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  precomp-Set-Quotient :
    {l : Level} (X : Set l) →
    (hom-Set B X) → reflecting-map-equivalence-relation R (type-Set X)
  pr1 (precomp-Set-Quotient X g) =
    g ∘ (map-reflecting-map-equivalence-relation R f)
  pr2 (precomp-Set-Quotient X g) r =
    ap g (reflects-map-reflecting-map-equivalence-relation R f r)

is-set-quotient :
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B)) → UUω
is-set-quotient R B f =
  {l : Level} (X : Set l) → is-equiv (precomp-Set-Quotient R B f X)

module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  universal-property-set-quotient : UUω
  universal-property-set-quotient =
    {l : Level} (X : Set l)
    (g : reflecting-map-equivalence-relation R (type-Set X)) →
    is-contr
      ( Σ ( hom-Set B X)
          ( λ h →
            ( h ∘ map-reflecting-map-equivalence-relation R f) ~
            ( map-reflecting-map-equivalence-relation R g)))
```

## Properties

### Precomposing the identity function by a reflecting map yields the original reflecting map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  precomp-id-Set-Quotient : precomp-Set-Quotient R B f B id ＝ f
  precomp-id-Set-Quotient =
    eq-htpy-reflecting-map-equivalence-relation R B
      ( precomp-Set-Quotient R B f B id)
      ( f)
      ( refl-htpy)
```

### If a reflecting map is a set quotient, then it satisfies the universal property of the set quotient

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  universal-property-set-quotient-is-set-quotient :
    is-set-quotient R B f → universal-property-set-quotient R B f
  universal-property-set-quotient-is-set-quotient Q X g =
    is-contr-equiv'
      ( fiber (precomp-Set-Quotient R B f X) g)
      ( equiv-tot
        ( λ h →
          extensionality-reflecting-map-equivalence-relation R X
            ( precomp-Set-Quotient R B f X h)
            ( g)))
      ( is-contr-map-is-equiv (Q X) g)

  map-universal-property-set-quotient-is-set-quotient :
    {l4 : Level} (Uf : is-set-quotient R B f)
    (C : Set l4) (g : reflecting-map-equivalence-relation R (type-Set C)) →
    type-Set B → type-Set C
  map-universal-property-set-quotient-is-set-quotient Uf C g =
    pr1 (center (universal-property-set-quotient-is-set-quotient Uf C g))

  triangle-universal-property-set-quotient-is-set-quotient :
    {l4 : Level} (Uf : is-set-quotient R B f)
    (C : Set l4) (g : reflecting-map-equivalence-relation R (type-Set C)) →
    ( ( map-universal-property-set-quotient-is-set-quotient Uf C g) ∘
      ( map-reflecting-map-equivalence-relation R f)) ~
    ( map-reflecting-map-equivalence-relation R g)
  triangle-universal-property-set-quotient-is-set-quotient Uf C g =
    ( pr2 (center (universal-property-set-quotient-is-set-quotient Uf C g)))
```

### If a reflecting map satisfies the universal property of the set quotient, then it is a set quotient

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  is-set-quotient-universal-property-set-quotient :
    universal-property-set-quotient R B f → is-set-quotient R B f
  is-set-quotient-universal-property-set-quotient Uf X =
    is-equiv-is-contr-map
      ( λ g →
        is-contr-equiv
          ( Σ ( hom-Set B X)
              ( λ h →
                ( h ∘ map-reflecting-map-equivalence-relation R f) ~
                ( map-reflecting-map-equivalence-relation R g)))
          ( equiv-tot
            ( λ h →
              extensionality-reflecting-map-equivalence-relation R X
                ( precomp-Set-Quotient R B f X h)
                ( g)))
          ( Uf X g))
```

### A map out of a type equipped with an equivalence relation is effective if and only if it is an image factorization

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (q : A → type-Set B)
  where

  is-effective-is-image :
    (i : type-Set B ↪ (A → Prop l2)) →
    (T : (prop-equivalence-relation R) ~ ((map-emb i) ∘ q)) →
    is-image (prop-equivalence-relation R) i (pair q T) →
    is-effective R q
  is-effective-is-image i T H x y =
    ( is-effective-class R x y) ∘e
    ( ( inv-equiv (equiv-ap-emb (emb-equivalence-class R))) ∘e
      ( ( inv-equiv (convert-eq-values T x y)) ∘e
        ( equiv-ap-emb i)))

  is-surjective-and-effective-is-image :
    (i : type-Set B ↪ (A → Prop l2)) →
    (T : (prop-equivalence-relation R) ~ ((map-emb i) ∘ q)) →
    is-image (prop-equivalence-relation R) i (pair q T) →
    is-surjective-and-effective R q
  pr1 (is-surjective-and-effective-is-image i T H) =
    is-surjective-is-image (prop-equivalence-relation R) i (pair q T) H
  pr2 (is-surjective-and-effective-is-image i T H) =
    is-effective-is-image i T H

  is-locally-small-is-surjective-and-effective :
    is-surjective-and-effective R q → is-locally-small l2 (type-Set B)
  is-locally-small-is-surjective-and-effective e x y =
    apply-twice-universal-property-trunc-Prop
      ( pr1 e x)
      ( pr1 e y)
      ( is-small-Prop l2 (x ＝ y))
      ( α)
    where
    α : fiber q x → fiber q y → is-small l2 (x ＝ y)
    pr1 (α (pair a refl) (pair b refl)) = sim-equivalence-relation R a b
    pr2 (α (pair a refl) (pair b refl)) = pr2 e a b

  large-map-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B → A → Prop l3
  large-map-emb-is-surjective-and-effective H b a = Id-Prop B b (q a)

  small-map-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B → A →
    Σ (Prop l3) (λ P → is-small l2 (type-Prop P))
  pr1 (small-map-emb-is-surjective-and-effective H b a) =
    large-map-emb-is-surjective-and-effective H b a
  pr2 (small-map-emb-is-surjective-and-effective H b a) =
    is-locally-small-is-surjective-and-effective H b (q a)

  map-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B → A → Prop l2
  pr1 (map-emb-is-surjective-and-effective H b a) =
    pr1 (pr2 (small-map-emb-is-surjective-and-effective H b a))
  pr2 (map-emb-is-surjective-and-effective H b a) =
    is-prop-equiv'
      ( pr2 (pr2 (small-map-emb-is-surjective-and-effective H b a)))
      ( is-prop-type-Prop
        ( large-map-emb-is-surjective-and-effective H b a))

  compute-map-emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) (b : type-Set B) (a : A) →
    type-Prop (large-map-emb-is-surjective-and-effective H b a) ≃
    type-Prop (map-emb-is-surjective-and-effective H b a)
  compute-map-emb-is-surjective-and-effective H b a =
    pr2 (pr2 (small-map-emb-is-surjective-and-effective H b a))

  triangle-emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    prop-equivalence-relation R ~ (map-emb-is-surjective-and-effective H ∘ q)
  triangle-emb-is-surjective-and-effective H a =
    eq-htpy
      ( λ x →
        eq-equiv-Prop
          ( ( compute-map-emb-is-surjective-and-effective H (q a) x) ∘e
            ( inv-equiv (pr2 H a x))))

  is-emb-map-emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    is-emb (map-emb-is-surjective-and-effective H)
  is-emb-map-emb-is-surjective-and-effective H =
    is-emb-is-injective
      ( is-set-function-type is-set-type-Prop)
      ( λ {x} {y} p →
        apply-universal-property-trunc-Prop
          ( pr1 H y)
          ( Id-Prop B x y)
          ( α p))
    where
    α :
      {x y : type-Set B}
      (p :
        ( map-emb-is-surjective-and-effective H x) ＝
        ( map-emb-is-surjective-and-effective H y)) →
      fiber q y →
      type-Prop (Id-Prop B x y)
    α {x} p (pair a refl) =
      map-inv-equiv
        ( ( inv-equiv
            ( pr2
              ( is-locally-small-is-surjective-and-effective
                H (q a) (q a)))) ∘e
          ( ( equiv-eq (ap pr1 (htpy-eq p a))) ∘e
            ( pr2
              ( is-locally-small-is-surjective-and-effective H x (q a)))))
        ( refl)

  emb-is-surjective-and-effective :
    (H : is-surjective-and-effective R q) →
    type-Set B ↪ (A → Prop l2)
  pr1 (emb-is-surjective-and-effective H) =
    map-emb-is-surjective-and-effective H
  pr2 (emb-is-surjective-and-effective H) =
    is-emb-map-emb-is-surjective-and-effective H

  is-emb-large-map-emb-is-surjective-and-effective :
    (e : is-surjective-and-effective R q) →
    is-emb (large-map-emb-is-surjective-and-effective e)
  is-emb-large-map-emb-is-surjective-and-effective e =
    is-emb-is-injective
      ( is-set-function-type is-set-type-Prop)
      ( λ {x} {y} p →
        apply-universal-property-trunc-Prop
          ( pr1 e y)
          ( Id-Prop B x y)
          ( α p))
    where
    α :
      {x y : type-Set B}
      (p :
        ( large-map-emb-is-surjective-and-effective e x) ＝
        ( large-map-emb-is-surjective-and-effective e y)) →
      fiber q y →
      type-Prop (Id-Prop B x y)
    α p (pair a refl) = map-inv-equiv (equiv-eq (ap pr1 (htpy-eq p a))) refl

  large-emb-is-surjective-and-effective :
    is-surjective-and-effective R q → type-Set B ↪ (A → Prop l3)
  pr1 (large-emb-is-surjective-and-effective e) =
    large-map-emb-is-surjective-and-effective e
  pr2 (large-emb-is-surjective-and-effective e) =
    is-emb-large-map-emb-is-surjective-and-effective e

  is-image-is-surjective-and-effective :
    ( H : is-surjective-and-effective R q) →
    is-image
      ( prop-equivalence-relation R)
      ( emb-is-surjective-and-effective H)
      ( pair q (triangle-emb-is-surjective-and-effective H))
  is-image-is-surjective-and-effective H =
    is-image-is-surjective
      ( prop-equivalence-relation R)
      ( emb-is-surjective-and-effective H)
      ( pair q (triangle-emb-is-surjective-and-effective H))
      ( pr1 H)
```

### Any set quotient `q : A → B` of an equivalence relation `R` on `A` is surjective

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  where

  is-surjective-is-set-quotient :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    is-surjective (map-reflecting-map-equivalence-relation R q)
  is-surjective-is-set-quotient q Q b =
    tr
      ( λ y →
        type-trunc-Prop (fiber (map-reflecting-map-equivalence-relation R q) y))
      ( htpy-eq
        ( ap pr1
          ( eq-is-contr
            ( universal-property-set-quotient-is-set-quotient R B q Q B q)
            { inclusion-im (map-reflecting-map-equivalence-relation R q) ∘ β ,
              δ}
            { id , refl-htpy}))
        ( b))
      ( pr2 (β b))
    where
    α :
      reflects-equivalence-relation R
        ( map-unit-im (map-reflecting-map-equivalence-relation R q))
    α {x} {y} r =
      is-injective-is-emb
        ( is-emb-inclusion-im (map-reflecting-map-equivalence-relation R q))
        ( map-equiv
          ( convert-eq-values
            ( triangle-unit-im (map-reflecting-map-equivalence-relation R q))
            ( x)
            ( y))
          ( reflects-map-reflecting-map-equivalence-relation R q r))
    β : type-Set B → im (map-reflecting-map-equivalence-relation R q)
    β = map-inv-is-equiv
        ( Q ( pair
              ( im (map-reflecting-map-equivalence-relation R q))
                ( is-set-im
                  ( map-reflecting-map-equivalence-relation R q)
                  ( is-set-type-Set B))))
          ( pair (map-unit-im (map-reflecting-map-equivalence-relation R q)) α)
    γ :
      ( β ∘ (map-reflecting-map-equivalence-relation R q)) ~
      ( map-unit-im (map-reflecting-map-equivalence-relation R q))
    γ =
      htpy-eq
        ( ap
            ( pr1)
            ( is-section-map-inv-is-equiv
              ( Q ( pair
                    ( im (map-reflecting-map-equivalence-relation R q))
                    ( is-set-im
                      ( map-reflecting-map-equivalence-relation R q)
                      ( is-set-type-Set B))))
              ( map-unit-im (map-reflecting-map-equivalence-relation R q) , α)))
    δ :
      ( ( inclusion-im (map-reflecting-map-equivalence-relation R q) ∘ β) ∘
        ( map-reflecting-map-equivalence-relation R q)) ~
      ( map-reflecting-map-equivalence-relation R q)
    δ =
      ( inclusion-im (map-reflecting-map-equivalence-relation R q) ·l γ) ∙h
      ( triangle-unit-im (map-reflecting-map-equivalence-relation R q))
```

### Any set quotient `q : A → B` of an equivalence relation `R` on `A` is effective

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  where

  is-effective-is-set-quotient :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    is-effective R (map-reflecting-map-equivalence-relation R q)
  is-effective-is-set-quotient q Q x y =
    inv-equiv (compute-P y) ∘e δ (map-reflecting-map-equivalence-relation R q y)
    where
    α : Σ (A → Prop l2) (reflects-equivalence-relation R)
    α = pair
        ( prop-equivalence-relation R x)
        ( λ r →
          eq-iff
            ( transitive-equivalence-relation R _ _ _ r)
            ( transitive-equivalence-relation R _ _ _
              ( symmetric-equivalence-relation R _ _ r)))
    P : type-Set B → Prop l2
    P = map-inv-is-equiv (Q (Prop-Set l2)) α
    compute-P :
      (a : A) →
      sim-equivalence-relation R x a ≃
      type-Prop (P (map-reflecting-map-equivalence-relation R q a))
    compute-P a =
      equiv-eq
        ( ap pr1
          ( htpy-eq
            ( ap pr1
              ( inv (is-section-map-inv-is-equiv (Q (Prop-Set l2)) α)))
            ( a)))
    point-P : type-Prop (P (map-reflecting-map-equivalence-relation R q x))
    point-P = map-equiv (compute-P x) (refl-equivalence-relation R x)
    center-total-P : Σ (type-Set B) (λ b → type-Prop (P b))
    center-total-P =
      pair (map-reflecting-map-equivalence-relation R q x) point-P
    contraction-total-P :
      (u : Σ (type-Set B) (λ b → type-Prop (P b))) → center-total-P ＝ u
    contraction-total-P (pair b p) =
      eq-type-subtype P
        ( apply-universal-property-trunc-Prop
          ( is-surjective-is-set-quotient R B q Q b)
          ( Id-Prop B (map-reflecting-map-equivalence-relation R q x) b)
          ( λ v →
            ( reflects-map-reflecting-map-equivalence-relation R q
              ( map-inv-equiv
                ( compute-P (pr1 v))
                ( inv-tr (type-Prop ∘ P) (pr2 v) p))) ∙
            ( pr2 v)))
    is-torsorial-P : is-torsorial (λ b → type-Prop (P b))
    is-torsorial-P = pair center-total-P contraction-total-P
    β :
      (b : type-Set B) →
      map-reflecting-map-equivalence-relation R q x ＝ b → type-Prop (P b)
    β .(map-reflecting-map-equivalence-relation R q x) refl = point-P
    γ : (b : type-Set B) → is-equiv (β b)
    γ = fundamental-theorem-id is-torsorial-P β
    δ :
      (b : type-Set B) →
      (map-reflecting-map-equivalence-relation R q x ＝ b) ≃ type-Prop (P b)
    δ b = pair (β b) (γ b)

  apply-effectiveness-is-set-quotient :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    {x y : A} →
    ( map-reflecting-map-equivalence-relation R q x ＝
      map-reflecting-map-equivalence-relation R q y) →
    sim-equivalence-relation R x y
  apply-effectiveness-is-set-quotient q H {x} {y} =
    map-equiv (is-effective-is-set-quotient q H x y)

  apply-effectiveness-is-set-quotient' :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    {x y : A} → sim-equivalence-relation R x y →
    map-reflecting-map-equivalence-relation R q x ＝
    map-reflecting-map-equivalence-relation R q y
  apply-effectiveness-is-set-quotient' q H {x} {y} =
    map-inv-equiv (is-effective-is-set-quotient q H x y)

  is-surjective-and-effective-is-set-quotient :
    (q : reflecting-map-equivalence-relation R (type-Set B)) →
    is-set-quotient R B q →
    is-surjective-and-effective R (map-reflecting-map-equivalence-relation R q)
  pr1 (is-surjective-and-effective-is-set-quotient q Q) =
    is-surjective-is-set-quotient R B q Q
  pr2 (is-surjective-and-effective-is-set-quotient q Q) =
    is-effective-is-set-quotient q Q
```

### Any surjective and effective map is a set quotient

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (q : reflecting-map-equivalence-relation R (type-Set B))
  where

  private
    module _
      ( E :
        is-surjective-and-effective R
          ( map-reflecting-map-equivalence-relation R q))
      { l : Level}
      ( X : Set l)
      ( f : reflecting-map-equivalence-relation R (type-Set X))
      where

      P-Prop : (b : type-Set B) (x : type-Set X) → Prop (l1 ⊔ l3 ⊔ l)
      P-Prop b x =
        exists-structure-Prop A
          ( λ a →
            ( map-reflecting-map-equivalence-relation R f a ＝ x) ×
            ( map-reflecting-map-equivalence-relation R q a ＝ b))

      P : (b : type-Set B) (x : type-Set X) → UU (l1 ⊔ l3 ⊔ l)
      P b x = type-Prop (P-Prop b x)

      all-elements-equal-total-P :
        (b : type-Set B) → all-elements-equal (Σ (type-Set X) (P b))
      all-elements-equal-total-P b x y =
        eq-type-subtype
          ( P-Prop b)
          ( apply-twice-universal-property-trunc-Prop
            ( pr2 x)
            ( pr2 y)
            ( Id-Prop X (pr1 x) (pr1 y))
            ( λ u v →
              ( inv (pr1 (pr2 u))) ∙
              ( ( pr2 f
                  ( map-equiv
                    ( pr2 E (pr1 u) (pr1 v))
                    ( (pr2 (pr2 u)) ∙ (inv (pr2 (pr2 v)))))) ∙
                ( pr1 (pr2 v)))))

      is-prop-total-P : (b : type-Set B) → is-prop (Σ (type-Set X) (P b))
      is-prop-total-P b =
        is-prop-all-elements-equal (all-elements-equal-total-P b)

      α : (b : type-Set B) → Σ (type-Set X) (P b)
      α =
        map-inv-is-equiv
          ( dependent-universal-property-surjection-is-surjective
            ( map-reflecting-map-equivalence-relation R q)
            ( pr1 E)
            ( λ b →
              pair
                ( Σ (type-Set X) (P b))
                ( is-prop-total-P b)))
          ( λ a → pair (pr1 f a) (unit-trunc-Prop (pair a (pair refl refl))))

      β :
        (a : A) →
        ( α (map-reflecting-map-equivalence-relation R q a)) ＝
        ( pair (pr1 f a) (unit-trunc-Prop (pair a (pair refl refl))))
      β = htpy-eq
            ( is-section-map-inv-is-equiv
              ( dependent-universal-property-surjection-is-surjective
                ( map-reflecting-map-equivalence-relation R q)
                ( pr1 E)
                ( λ b → pair (Σ (type-Set X) (P b)) (is-prop-total-P b)))
              ( λ a →
                pair (pr1 f a) (unit-trunc-Prop (pair a (pair refl refl)))))

  is-set-quotient-is-surjective-and-effective :
    ( E :
      is-surjective-and-effective R
        ( map-reflecting-map-equivalence-relation R q)) →
    is-set-quotient R B q
  is-set-quotient-is-surjective-and-effective E X =
    is-equiv-is-contr-map
      ( λ f →
        is-proof-irrelevant-is-prop
        ( is-prop-equiv
          ( equiv-tot
            ( λ _ →
              equiv-ap-inclusion-subtype
                ( reflects-prop-equivalence-relation R X)))
          ( is-prop-map-is-emb
            ( is-epimorphism-is-surjective-Set (pr1 E) X)
            ( pr1 f)))
        ( pair
          ( λ b → pr1 (α E X f b))
          ( eq-type-subtype
            ( reflects-prop-equivalence-relation R X)
            ( eq-htpy (λ a → ap pr1 (β E X f a))))))

  universal-property-set-quotient-is-surjective-and-effective :
    ( E :
      is-surjective-and-effective R
        ( map-reflecting-map-equivalence-relation R q)) →
    universal-property-set-quotient R B q
  universal-property-set-quotient-is-surjective-and-effective E =
    universal-property-set-quotient-is-set-quotient R B q
      ( is-set-quotient-is-surjective-and-effective E)
```

### The large set quotient satisfies the universal property of set quotients

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  universal-property-equivalence-class :
    universal-property-set-quotient R
      ( equivalence-class-Set R)
      ( quotient-reflecting-map-equivalence-class R)
  universal-property-equivalence-class =
    universal-property-set-quotient-is-surjective-and-effective R
      ( equivalence-class-Set R)
      ( quotient-reflecting-map-equivalence-class R)
      ( is-surjective-and-effective-class R)

  is-set-quotient-equivalence-class :
    is-set-quotient R
      ( equivalence-class-Set R)
      ( quotient-reflecting-map-equivalence-class R)
  is-set-quotient-equivalence-class =
    is-set-quotient-universal-property-set-quotient R
      ( equivalence-class-Set R)
      ( quotient-reflecting-map-equivalence-class R)
      ( universal-property-equivalence-class)

  map-universal-property-equivalence-class :
    {l4 : Level} (C : Set l4)
    (g : reflecting-map-equivalence-relation R (type-Set C)) →
    equivalence-class R → type-Set C
  map-universal-property-equivalence-class C g =
    pr1 (center (universal-property-equivalence-class C g))

  triangle-universal-property-equivalence-class :
    {l4 : Level} (C : Set l4)
    (g : reflecting-map-equivalence-relation R (type-Set C)) →
    ( ( map-universal-property-equivalence-class C g) ∘
      ( class R)) ~
    ( map-reflecting-map-equivalence-relation R g)
  triangle-universal-property-equivalence-class C g =
    pr2 (center (universal-property-equivalence-class C g))
```

### The induction property of set quotients

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (Q : Set l3)
  (q : reflecting-map-equivalence-relation R (type-Set Q))
  (U : is-set-quotient R Q q)
  where

  ind-is-set-quotient :
    {l : Level} (P : type-Set Q → Prop l) →
    ((a : A) → type-Prop (P (map-reflecting-map-equivalence-relation R q a))) →
    ((x : type-Set Q) → type-Prop (P x))
  ind-is-set-quotient =
    apply-dependent-universal-property-surjection-is-surjective
      ( map-reflecting-map-equivalence-relation R q)
      ( is-surjective-is-set-quotient R Q q U)
```

### Injectiveness of maps defined by the universal property of the set quotient

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (Q : Set l3)
  (q : reflecting-map-equivalence-relation R (type-Set Q))
  (U : is-set-quotient R Q q)
  where

  is-injective-map-universal-property-set-quotient-is-set-quotient :
    {l4 : Level} (B : Set l4)
    (f : reflecting-map-equivalence-relation R (type-Set B))
    ( H :
      (x y : A) →
      ( map-reflecting-map-equivalence-relation R f x ＝
        map-reflecting-map-equivalence-relation R f y) →
      sim-equivalence-relation R x y) →
    is-injective
      ( map-universal-property-set-quotient-is-set-quotient R Q q U B f)
  is-injective-map-universal-property-set-quotient-is-set-quotient
    B f H {x} {y} =
    ind-is-set-quotient R Q q U
      ( λ u →
        function-Prop
          ( map-universal-property-set-quotient-is-set-quotient R Q q U B f u ＝
            map-universal-property-set-quotient-is-set-quotient R Q q U B f y)
          ( Id-Prop Q u y))
      ( λ a →
        ( ind-is-set-quotient R Q q U
          ( λ v →
            function-Prop
              ( ( map-reflecting-map-equivalence-relation R f a) ＝
                ( map-universal-property-set-quotient-is-set-quotient
                  R Q q U B f v))
              ( Id-Prop Q (map-reflecting-map-equivalence-relation R q a) v))
          ( λ b p →
            reflects-map-reflecting-map-equivalence-relation R q
              ( H a b
                ( ( p) ∙
                  ( triangle-universal-property-set-quotient-is-set-quotient
                    R Q q U B f b))))
          ( y)) ∘
        ( concat
          ( inv
            ( triangle-universal-property-set-quotient-is-set-quotient
              R Q q U B f a))
          ( map-universal-property-set-quotient-is-set-quotient R Q q U B f y)))
      ( x)

  is-emb-map-universal-property-set-quotient-is-set-quotient :
    {l4 : Level} (B : Set l4)
    (f : reflecting-map-equivalence-relation R (type-Set B))
    ( H : (x y : A) →
          ( map-reflecting-map-equivalence-relation R f x ＝
            map-reflecting-map-equivalence-relation R f y) →
          sim-equivalence-relation R x y) →
    is-emb
      ( map-universal-property-set-quotient-is-set-quotient R Q q U B f)
  is-emb-map-universal-property-set-quotient-is-set-quotient B f H =
    is-emb-is-injective
      ( is-set-type-Set B)
      ( is-injective-map-universal-property-set-quotient-is-set-quotient B f H)
```

### The type of extensions of maps into a set along a surjection is equivalent to the proposition that that map equalizes the values that the surjection equalizes

Consider a surjective map `f : A ↠ B` and a map `g : A → C` into a set `C`.
Recall from
[Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
that the type

```text
  Σ (B → C) (λ h → g ~ h ∘ f)
```

of extensions of `g` along `f` is a proposition. This proposition is equivalent
to the proposition

```text
  (a a' : A) → f a ＝ f a' → g a ＝ g a'.
```

**Proof:** The tricky direction is to construct an extension of `g` along `f`
whenever the above proposition holds. Note that we may compose `f` with the
[set truncation](foundation.set-truncations.md) of `B`, this results in a map

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A ↠ B)
  (C : Set l3) (g : A → type-Set C)
  where

  equalizes-equal-values-prop-surjection-Set : Prop (l1 ⊔ l2 ⊔ l3)
  equalizes-equal-values-prop-surjection-Set =
    Π-Prop A
      ( λ a →
        Π-Prop A
          ( λ a' →
            function-Prop
              ( map-surjection f a ＝ map-surjection f a')
              ( Id-Prop C (g a) (g a'))))

  equalizes-equal-values-surjection-Set : UU (l1 ⊔ l2 ⊔ l3)
  equalizes-equal-values-surjection-Set =
    type-Prop equalizes-equal-values-prop-surjection-Set

  is-prop-equalizes-equal-values-surjection-Set :
    is-prop equalizes-equal-values-surjection-Set
  is-prop-equalizes-equal-values-surjection-Set =
    is-prop-type-Prop equalizes-equal-values-prop-surjection-Set

  equalizes-equal-values-extension-along-surjection-Set :
    extension-along-surjection-Set f C g → equalizes-equal-values-surjection-Set
  equalizes-equal-values-extension-along-surjection-Set (h , q) a a' p =
    q a ∙ (ap h p ∙ inv (q a'))

  extension-equalizes-equal-values-surjection-Set :
    equalizes-equal-values-surjection-Set → extension-along-surjection-Set f C g
  extension-equalizes-equal-values-surjection-Set H =
    map-equiv
      ( e)
      ( apply-dependent-universal-property-surjection
        ( f)
        ( λ b → P b , is-prop-P b)
        ( λ a → (g a , λ (a' , p') → H a' a p')))
    where
      P : B → UU (l1 ⊔ l2 ⊔ l3)
      P b =
        Σ (type-Set C) (λ c → (s : fiber (map-surjection f) b) → g (pr1 s) ＝ c)

      e : ((b : B) → P b) ≃
          Σ (B → type-Set C) (λ h → g ~ (h ∘ map-surjection f))
      e =
        ( equiv-tot
          ( λ h →
            equiv-precomp-Π (inv-equiv-total-fiber (map-surjection f)) _)) ∘e
        ( equiv-tot (λ h → inv-equiv equiv-ev-pair)) ∘e
        ( distributive-Π-Σ)

      is-prop-P : (b : B) → is-prop (P b)
      is-prop-P b =
        is-prop-all-elements-equal
          ( λ (pair c q) (pair c' q') →
            eq-type-subtype
              ( λ c'' →
                Π-Prop
                  (fiber (map-surjection f) b)
                  (λ s → Id-Prop C (g (pr1 s)) c''))
              ( map-universal-property-trunc-Prop
                ( Id-Prop C c c')
                ( λ s → inv (q s) ∙ q' s)
                ( is-surjective-map-surjection f b)))

  equiv-equalizes-equal-values-extension-along-surjection-Set :
    extension-along-surjection-Set f C g ≃ equalizes-equal-values-surjection-Set
  pr1 equiv-equalizes-equal-values-extension-along-surjection-Set =
    equalizes-equal-values-extension-along-surjection-Set
  pr2 equiv-equalizes-equal-values-extension-along-surjection-Set =
    is-equiv-has-converse-is-prop
      ( is-prop-extension-along-surjection-Set f C g)
      ( is-prop-equalizes-equal-values-surjection-Set)
      ( extension-equalizes-equal-values-surjection-Set)

  function-extension-equalizes-equal-values-surjection-Set :
    equalizes-equal-values-surjection-Set → B → type-Set C
  function-extension-equalizes-equal-values-surjection-Set =
    pr1 ∘
    map-inv-equiv equiv-equalizes-equal-values-extension-along-surjection-Set

  coherence-triangle-extension-equalizes-equal-values-surjection-Set :
    (H : equalizes-equal-values-surjection-Set) →
    coherence-triangle-maps
      ( g)
      ( function-extension-equalizes-equal-values-surjection-Set H)
      ( map-surjection f)
  coherence-triangle-extension-equalizes-equal-values-surjection-Set =
    pr2 ∘
    map-inv-equiv equiv-equalizes-equal-values-extension-along-surjection-Set
```
