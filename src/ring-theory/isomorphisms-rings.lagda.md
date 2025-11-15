# Isomorphisms of rings

```agda
module ring-theory.isomorphisms-rings where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.implicit-function-types
open import foundation.iterated-dependent-product-types
open import foundation.multivariable-homotopies
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.homomorphisms-abelian-groups
open import group-theory.homomorphisms-monoids
open import group-theory.isomorphisms-abelian-groups
open import group-theory.isomorphisms-monoids

open import ring-theory.homomorphisms-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.precategory-of-rings
open import ring-theory.rings
```

</details>

## Idea

{{#concept "Ring isomorphisms" WD="ring isomorphism" WDID=Q135670074 Agda=iso-Ring}}
are [ring homomorphisms](ring-theory.homomorphisms-rings.md) with a two-sided
inverse homomorphism.

## Definition

### The predicate of being an isomorphism of rings

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2) (f : hom-Ring R S)
  where

  is-iso-prop-Ring : Prop (l1 ⊔ l2)
  is-iso-prop-Ring =
    is-iso-prop-Large-Precategory Ring-Large-Precategory {X = R} {Y = S} f

  is-iso-Ring : UU (l1 ⊔ l2)
  is-iso-Ring =
    is-iso-Large-Precategory Ring-Large-Precategory {X = R} {Y = S} f

  is-prop-is-iso-Ring : is-prop is-iso-Ring
  is-prop-is-iso-Ring =
    is-prop-is-iso-Large-Precategory
      ( Ring-Large-Precategory)
      { X = R}
      { Y = S}
      ( f)

  hom-inv-is-iso-Ring : is-iso-Ring → hom-Ring S R
  hom-inv-is-iso-Ring =
    hom-inv-is-iso-Large-Precategory
      ( Ring-Large-Precategory)
      { X = R}
      { Y = S}
      ( f)

  is-section-hom-inv-is-iso-Ring :
    (U : is-iso-Ring) →
    comp-hom-Ring S R S f (hom-inv-is-iso-Ring U) ＝ id-hom-Ring S
  is-section-hom-inv-is-iso-Ring =
    is-section-hom-inv-is-iso-Large-Precategory
      ( Ring-Large-Precategory)
      { X = R}
      { Y = S}
      ( f)

  is-retraction-hom-inv-is-iso-Ring :
    (U : is-iso-Ring) →
    comp-hom-Ring R S R (hom-inv-is-iso-Ring U) f ＝ id-hom-Ring R
  is-retraction-hom-inv-is-iso-Ring =
    is-retraction-hom-inv-is-iso-Large-Precategory
      ( Ring-Large-Precategory)
      { X = R}
      { Y = S}
      ( f)

  map-inv-is-iso-Ring : is-iso-Ring → type-Ring S → type-Ring R
  map-inv-is-iso-Ring U =
    map-hom-Ring S R (hom-inv-is-iso-Ring U)

  is-section-map-inv-is-iso-Ring :
    (U : is-iso-Ring) → map-hom-Ring R S f ∘ map-inv-is-iso-Ring U ~ id
  is-section-map-inv-is-iso-Ring U =
    htpy-eq-hom-Ring S S
      ( comp-hom-Ring S R S f (hom-inv-is-iso-Ring U))
      ( id-hom-Ring S)
      ( is-section-hom-inv-is-iso-Ring U)

  is-retraction-map-inv-is-iso-Ring :
    (U : is-iso-Ring) → map-inv-is-iso-Ring U ∘ map-hom-Ring R S f ~ id
  is-retraction-map-inv-is-iso-Ring U =
    htpy-eq-hom-Ring R R
      ( comp-hom-Ring R S R (hom-inv-is-iso-Ring U) f)
      ( id-hom-Ring R)
      ( is-retraction-hom-inv-is-iso-Ring U)
```

### Isomorphisms of rings

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  where

  iso-Ring : UU (l1 ⊔ l2)
  iso-Ring = iso-Large-Precategory Ring-Large-Precategory R S

  hom-iso-Ring : iso-Ring → hom-Ring R S
  hom-iso-Ring =
    hom-iso-Large-Precategory Ring-Large-Precategory {X = R} {Y = S}

  map-iso-Ring : iso-Ring → type-Ring R → type-Ring S
  map-iso-Ring f = map-hom-Ring R S (hom-iso-Ring f)

  preserves-zero-iso-Ring :
    (f : iso-Ring) → map-iso-Ring f (zero-Ring R) ＝ zero-Ring S
  preserves-zero-iso-Ring f = preserves-zero-hom-Ring R S (hom-iso-Ring f)

  preserves-one-iso-Ring :
    (f : iso-Ring) → map-iso-Ring f (one-Ring R) ＝ one-Ring S
  preserves-one-iso-Ring f = preserves-one-hom-Ring R S (hom-iso-Ring f)

  preserves-add-iso-Ring :
    (f : iso-Ring) {x y : type-Ring R} →
    map-iso-Ring f (add-Ring R x y) ＝
    add-Ring S (map-iso-Ring f x) (map-iso-Ring f y)
  preserves-add-iso-Ring f = preserves-add-hom-Ring R S (hom-iso-Ring f)

  preserves-neg-iso-Ring :
    (f : iso-Ring) {x : type-Ring R} →
    map-iso-Ring f (neg-Ring R x) ＝ neg-Ring S (map-iso-Ring f x)
  preserves-neg-iso-Ring f = preserves-neg-hom-Ring R S (hom-iso-Ring f)

  preserves-mul-iso-Ring :
    (f : iso-Ring) {x y : type-Ring R} →
    map-iso-Ring f (mul-Ring R x y) ＝
    mul-Ring S (map-iso-Ring f x) (map-iso-Ring f y)
  preserves-mul-iso-Ring f =
    preserves-mul-hom-Ring R S (hom-iso-Ring f)

  is-iso-iso-Ring :
    (f : iso-Ring) → is-iso-Ring R S (hom-iso-Ring f)
  is-iso-iso-Ring =
    is-iso-iso-Large-Precategory Ring-Large-Precategory {X = R} {Y = S}

  hom-inv-iso-Ring : iso-Ring → hom-Ring S R
  hom-inv-iso-Ring =
    hom-inv-iso-Large-Precategory Ring-Large-Precategory {X = R} {Y = S}

  map-inv-iso-Ring : iso-Ring → type-Ring S → type-Ring R
  map-inv-iso-Ring f = map-hom-Ring S R (hom-inv-iso-Ring f)

  preserves-zero-inv-iso-Ring :
    (f : iso-Ring) → map-inv-iso-Ring f (zero-Ring S) ＝ zero-Ring R
  preserves-zero-inv-iso-Ring f =
    preserves-zero-hom-Ring S R (hom-inv-iso-Ring f)

  preserves-one-inv-iso-Ring :
    (f : iso-Ring) → map-inv-iso-Ring f (one-Ring S) ＝ one-Ring R
  preserves-one-inv-iso-Ring f =
    preserves-one-hom-Ring S R (hom-inv-iso-Ring f)

  preserves-add-inv-iso-Ring :
    (f : iso-Ring) {x y : type-Ring S} →
    map-inv-iso-Ring f (add-Ring S x y) ＝
    add-Ring R (map-inv-iso-Ring f x) (map-inv-iso-Ring f y)
  preserves-add-inv-iso-Ring f =
    preserves-add-hom-Ring S R (hom-inv-iso-Ring f)

  preserves-neg-inv-iso-Ring :
    (f : iso-Ring) {x : type-Ring S} →
    map-inv-iso-Ring f (neg-Ring S x) ＝ neg-Ring R (map-inv-iso-Ring f x)
  preserves-neg-inv-iso-Ring f =
    preserves-neg-hom-Ring S R (hom-inv-iso-Ring f)

  preserves-mul-inv-iso-Ring :
    (f : iso-Ring) {x y : type-Ring S} →
    map-inv-iso-Ring f (mul-Ring S x y) ＝
    mul-Ring R (map-inv-iso-Ring f x) (map-inv-iso-Ring f y)
  preserves-mul-inv-iso-Ring f =
    preserves-mul-hom-Ring S R (hom-inv-iso-Ring f)

  is-section-hom-inv-iso-Ring :
    (f : iso-Ring) →
    comp-hom-Ring S R S (hom-iso-Ring f) (hom-inv-iso-Ring f) ＝ id-hom-Ring S
  is-section-hom-inv-iso-Ring =
    is-section-hom-inv-iso-Large-Precategory
      ( Ring-Large-Precategory)
      { X = R}
      { Y = S}

  is-section-map-inv-iso-Ring :
    (f : iso-Ring) → map-iso-Ring f ∘ map-inv-iso-Ring f ~ id
  is-section-map-inv-iso-Ring f =
    htpy-eq-hom-Ring S S
      ( comp-hom-Ring S R S (hom-iso-Ring f) (hom-inv-iso-Ring f))
      ( id-hom-Ring S)
      ( is-section-hom-inv-iso-Ring f)

  is-retraction-hom-inv-iso-Ring :
    (f : iso-Ring) →
    comp-hom-Ring R S R (hom-inv-iso-Ring f) (hom-iso-Ring f) ＝ id-hom-Ring R
  is-retraction-hom-inv-iso-Ring =
    is-retraction-hom-inv-iso-Large-Precategory
      ( Ring-Large-Precategory)
      { X = R}
      { Y = S}

  is-retraction-map-inv-iso-Ring :
    (f : iso-Ring) → map-inv-iso-Ring f ∘ map-iso-Ring f ~ id
  is-retraction-map-inv-iso-Ring f =
    htpy-eq-hom-Ring R R
      ( comp-hom-Ring R S R (hom-inv-iso-Ring f) (hom-iso-Ring f))
      ( id-hom-Ring R)
      ( is-retraction-hom-inv-iso-Ring f)

  iso-multiplicative-monoid-iso-Ring :
    (f : iso-Ring) →
    iso-Monoid (multiplicative-monoid-Ring R) (multiplicative-monoid-Ring S)
  pr1 (iso-multiplicative-monoid-iso-Ring f) =
    hom-multiplicative-monoid-hom-Ring R S (hom-iso-Ring f)
  pr1 (pr2 (iso-multiplicative-monoid-iso-Ring f)) =
    hom-multiplicative-monoid-hom-Ring S R (hom-inv-iso-Ring f)
  pr1 (pr2 (pr2 (iso-multiplicative-monoid-iso-Ring f))) =
    eq-htpy-hom-Monoid
      ( multiplicative-monoid-Ring S)
      ( multiplicative-monoid-Ring S)
      ( comp-hom-Monoid
        ( multiplicative-monoid-Ring S)
        ( multiplicative-monoid-Ring R)
        ( multiplicative-monoid-Ring S)
        ( hom-multiplicative-monoid-hom-Ring R S (hom-iso-Ring f))
        ( hom-multiplicative-monoid-hom-Ring S R (hom-inv-iso-Ring f)))
      ( id-hom-Monoid (multiplicative-monoid-Ring S))
      ( is-section-map-inv-iso-Ring f)
  pr2 (pr2 (pr2 (iso-multiplicative-monoid-iso-Ring f))) =
    eq-htpy-hom-Monoid
      ( multiplicative-monoid-Ring R)
      ( multiplicative-monoid-Ring R)
      ( comp-hom-Monoid
        ( multiplicative-monoid-Ring R)
        ( multiplicative-monoid-Ring S)
        ( multiplicative-monoid-Ring R)
        ( hom-multiplicative-monoid-hom-Ring S R (hom-inv-iso-Ring f))
        ( hom-multiplicative-monoid-hom-Ring R S (hom-iso-Ring f)))
      ( id-hom-Monoid (multiplicative-monoid-Ring R))
      ( is-retraction-map-inv-iso-Ring f)
```

### The identity isomorphism of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-iso-id-hom-Ring : is-iso-Ring R R (id-hom-Ring R)
  is-iso-id-hom-Ring =
    is-iso-id-hom-Large-Precategory Ring-Large-Precategory {X = R}

  id-iso-Ring : iso-Ring R R
  pr1 id-iso-Ring = id-hom-Ring R
  pr2 id-iso-Ring = is-iso-id-hom-Ring
```

### Converting identifications of rings to isomorphisms of rings

```agda
iso-eq-Ring :
  { l : Level} (R S : Ring l) → R ＝ S → iso-Ring R S
iso-eq-Ring R S = iso-eq-Large-Precategory Ring-Large-Precategory R S
```

## Properties

### A ring homomorphism is an isomorphism if and only if the underlying homomorphism of abelian groups is an isomorphism

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  where

  iso-ab-Ring : UU (l1 ⊔ l2)
  iso-ab-Ring =
    Σ ( iso-Ab (ab-Ring R) (ab-Ring S))
      ( λ f →
        is-ring-homomorphism-hom-Ab R S
          ( hom-iso-Ab (ab-Ring R) (ab-Ring S) f))

  iso-ab-iso-ab-Ring :
    iso-ab-Ring → iso-Ab (ab-Ring R) (ab-Ring S)
  iso-ab-iso-ab-Ring = pr1

  is-iso-ab-hom-Ring : hom-Ring R S → UU (l1 ⊔ l2)
  is-iso-ab-hom-Ring f =
    is-iso-Ab (ab-Ring R) (ab-Ring S) (hom-ab-hom-Ring R S f)

  is-iso-ab-is-iso-Ring :
    (f : hom-Ring R S) →
    is-iso-Ring R S f → is-iso-ab-hom-Ring f
  pr1 (is-iso-ab-is-iso-Ring f U) =
    hom-ab-hom-Ring S R (hom-inv-is-iso-Ring R S f U)
  pr1 (pr2 (is-iso-ab-is-iso-Ring f U)) =
    ap
      ( hom-ab-hom-Ring S S)
      ( is-section-hom-inv-is-iso-Ring R S f U)
  pr2 (pr2 (is-iso-ab-is-iso-Ring f U)) =
    ap
      ( hom-ab-hom-Ring R R)
      ( is-retraction-hom-inv-is-iso-Ring R S f U)

  abstract
    preserves-mul-inv-is-iso-Ab :
      (f : hom-Ab (ab-Ring R) (ab-Ring S)) →
      (U : is-iso-Ab (ab-Ring R) (ab-Ring S) f) →
      preserves-mul-hom-Ab R S f →
      preserves-mul-hom-Ab S R
        ( hom-inv-is-iso-Ab (ab-Ring R) (ab-Ring S) f U)
    preserves-mul-inv-is-iso-Ab f U μ {x} {y} =
      ( inv
        ( ap
          ( map-inv-is-iso-Ab (ab-Ring R) (ab-Ring S) f U)
          ( ( μ) ∙
            ( ap-mul-Ring S
              ( is-section-map-inv-is-iso-Ab (ab-Ring R) (ab-Ring S) f U x)
              ( is-section-map-inv-is-iso-Ab
                ( ab-Ring R)
                ( ab-Ring S)
                ( f)
                ( U)
                ( y)))))) ∙
      ( is-retraction-map-inv-is-iso-Ab
        ( ab-Ring R)
        ( ab-Ring S)
        ( f)
        ( U)
        ( mul-Ring R
          ( map-inv-is-iso-Ab (ab-Ring R) (ab-Ring S) f U x)
          ( map-inv-is-iso-Ab (ab-Ring R) (ab-Ring S) f U y)))

  preserves-unit-inv-is-iso-Ab :
    (f : hom-Ab (ab-Ring R) (ab-Ring S)) →
    (U : is-iso-Ab (ab-Ring R) (ab-Ring S) f) →
    preserves-unit-hom-Ab R S f →
    preserves-unit-hom-Ab S R
      ( hom-inv-is-iso-Ab (ab-Ring R) (ab-Ring S) f U)
  preserves-unit-inv-is-iso-Ab f U ν =
    ( inv (ap (map-inv-is-iso-Ab (ab-Ring R) (ab-Ring S) f U) ν)) ∙
    ( is-retraction-map-inv-is-iso-Ab (ab-Ring R) (ab-Ring S) f U _)

  is-ring-homomorphism-inv-is-iso-Ab :
    (f : hom-Ab (ab-Ring R) (ab-Ring S)) →
    (U : is-iso-Ab (ab-Ring R) (ab-Ring S) f) →
    is-ring-homomorphism-hom-Ab R S f →
    is-ring-homomorphism-hom-Ab S R
      ( hom-inv-is-iso-Ab (ab-Ring R) (ab-Ring S) f U)
  pr1 (is-ring-homomorphism-inv-is-iso-Ab f U (μ , ν)) =
    preserves-mul-inv-is-iso-Ab f U μ
  pr2 (is-ring-homomorphism-inv-is-iso-Ab f U (μ , ν)) =
    preserves-unit-inv-is-iso-Ab f U ν

  inv-hom-ring-is-iso-Ab :
    (f : hom-Ring R S) →
    is-iso-Ab (ab-Ring R) (ab-Ring S) (hom-ab-hom-Ring R S f) →
    hom-Ring S R
  pr1 (inv-hom-ring-is-iso-Ab f U) =
    hom-inv-is-iso-Ab (ab-Ring R) (ab-Ring S) (hom-ab-hom-Ring R S f) U
  pr2 (inv-hom-ring-is-iso-Ab f U) =
    is-ring-homomorphism-inv-is-iso-Ab
      ( hom-ab-hom-Ring R S f)
      ( U)
      ( is-ring-homomorphism-hom-Ring R S f)

  abstract
    is-iso-ring-is-iso-Ab :
      (f : hom-Ring R S) →
      is-iso-Ab (ab-Ring R) (ab-Ring S) (hom-ab-hom-Ring R S f) →
      is-iso-Ring R S f
    pr1 (is-iso-ring-is-iso-Ab f U) =
      inv-hom-ring-is-iso-Ab f U
    pr1 (pr2 (is-iso-ring-is-iso-Ab f U)) =
      eq-htpy-hom-Ring S S
        ( comp-hom-Ring S R S f
          ( inv-hom-ring-is-iso-Ab f U))
        ( id-hom-Ring S)
        ( htpy-eq-hom-Ab (ab-Ring S) (ab-Ring S)
          ( hom-ab-hom-Ring S S
            ( comp-hom-Ring S R S f
              ( inv-hom-ring-is-iso-Ab f U)))
          ( id-hom-Ab (ab-Ring S))
          ( is-section-hom-inv-is-iso-Ab
            ( ab-Ring R)
            ( ab-Ring S)
            ( hom-ab-hom-Ring R S f)
            ( U)))
    pr2 (pr2 (is-iso-ring-is-iso-Ab f U)) =
      eq-htpy-hom-Ring R R
        ( comp-hom-Ring R S R
          ( inv-hom-ring-is-iso-Ab f U)
          ( f))
        ( id-hom-Ring R)
        ( htpy-eq-hom-Ab (ab-Ring R) (ab-Ring R)
          ( hom-ab-hom-Ring R R
            ( comp-hom-Ring R S R
              ( inv-hom-ring-is-iso-Ab f U)
              ( f)))
          ( id-hom-Ab (ab-Ring R))
          ( is-retraction-hom-inv-is-iso-Ab
            ( ab-Ring R)
            ( ab-Ring S)
            ( hom-ab-hom-Ring R S f)
            ( U)))

  iso-ab-iso-Ring :
    iso-Ring R S → iso-Ab (ab-Ring R) (ab-Ring S)
  pr1 (iso-ab-iso-Ring f) = hom-ab-hom-Ring R S (hom-iso-Ring R S f)
  pr2 (iso-ab-iso-Ring f) =
    is-iso-ab-is-iso-Ring
      ( hom-iso-Ring R S f)
      ( is-iso-iso-Ring R S f)

  equiv-iso-ab-iso-Ring : iso-Ring R S ≃ iso-ab-Ring
  equiv-iso-ab-iso-Ring =
    ( inv-associative-Σ) ∘e
    ( equiv-tot (λ f → commutative-product)) ∘e
    ( associative-Σ) ∘e
    ( equiv-type-subtype
      ( is-prop-is-iso-Ring R S)
      ( λ f → is-prop-is-iso-Ab (ab-Ring R) (ab-Ring S) (hom-ab-hom-Ring R S f))
      ( is-iso-ab-is-iso-Ring)
      ( is-iso-ring-is-iso-Ab))
```

### Characterizing identifications of rings

```agda
module _
  {l : Level} (R : Ring l)
  where

  abstract
    is-torsorial-iso-Ring : is-torsorial (λ (S : Ring l) → iso-Ring R S)
    is-torsorial-iso-Ring =
      is-contr-equiv
        ( Σ (Ring l) (iso-ab-Ring R))
        ( equiv-tot (equiv-iso-ab-iso-Ring R))
        ( is-torsorial-Eq-structure
          ( is-torsorial-iso-Ab (ab-Ring R))
          ( ab-Ring R , id-iso-Ab (ab-Ring R))
          ( is-torsorial-Eq-structure
            ( is-torsorial-Eq-subtype
              ( is-torsorial-multivariable-implicit-htpy 2 (mul-Ring R))
              ( λ μ →
                is-prop-iterated-Π 3
                  ( λ x y z → is-set-type-Ring R (μ (μ x y) z) (μ x (μ y z))))
              ( mul-Ring R)
              ( λ {x} {y} → refl)
              ( associative-mul-Ring R))
            ( (mul-Ring R , associative-mul-Ring R) , λ {x} {y} → refl)
            ( is-torsorial-Eq-subtype
              ( is-torsorial-Eq-subtype
                ( is-torsorial-Id (one-Ring R))
                ( λ x →
                  is-prop-product
                    ( is-prop-Π (λ y → is-set-type-Ring R (mul-Ring R x y) y))
                    ( is-prop-Π (λ y → is-set-type-Ring R (mul-Ring R y x) y)))
                ( one-Ring R)
                ( refl)
                ( left-unit-law-mul-Ring R , right-unit-law-mul-Ring R))
              ( λ u →
                is-prop-product
                  ( is-prop-iterated-Π 3
                    ( λ x y z →
                      is-set-type-Ring R
                        ( mul-Ring R x (add-Ring R y z))
                        ( add-Ring R (mul-Ring R x y) (mul-Ring R x z))))
                  ( is-prop-iterated-Π 3
                    ( λ x y z →
                      is-set-type-Ring R
                        ( mul-Ring R (add-Ring R x y) z)
                        ( add-Ring R (mul-Ring R x z) (mul-Ring R y z)))))
              ( is-unital-Ring R)
              ( refl)
              ( left-distributive-mul-add-Ring R ,
                right-distributive-mul-add-Ring R))))

  is-equiv-iso-eq-Ring :
    (S : Ring l) → is-equiv (iso-eq-Ring R S)
  is-equiv-iso-eq-Ring =
    fundamental-theorem-id
      ( is-torsorial-iso-Ring)
      ( iso-eq-Ring R)

  extensionality-Ring : (S : Ring l) → (R ＝ S) ≃ iso-Ring R S
  pr1 (extensionality-Ring S) = iso-eq-Ring R S
  pr2 (extensionality-Ring S) = is-equiv-iso-eq-Ring S

  eq-iso-Ring : (S : Ring l) → iso-Ring R S → R ＝ S
  eq-iso-Ring S = map-inv-is-equiv (is-equiv-iso-eq-Ring S)
```

### Any ring isomorphism preserves and reflects invertible elements

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : Ring l2)
  (f : iso-Ring R S)
  where

  preserves-invertible-elements-iso-Ring :
    {x : type-Ring R} →
    is-invertible-element-Ring R x →
    is-invertible-element-Ring S (map-iso-Ring R S f x)
  preserves-invertible-elements-iso-Ring =
    preserves-invertible-elements-iso-Monoid
      ( multiplicative-monoid-Ring R)
      ( multiplicative-monoid-Ring S)
      ( iso-multiplicative-monoid-iso-Ring R S f)

  reflects-invertible-elements-iso-Ring :
    {x : type-Ring R} →
    is-invertible-element-Ring S (map-iso-Ring R S f x) →
    is-invertible-element-Ring R x
  reflects-invertible-elements-iso-Ring =
    reflects-invertible-elements-iso-Monoid
      ( multiplicative-monoid-Ring R)
      ( multiplicative-monoid-Ring S)
      ( iso-multiplicative-monoid-iso-Ring R S f)
```
