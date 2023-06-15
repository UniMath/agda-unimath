# Isomorphisms of rings

```agda
module ring-theory.isomorphisms-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.homomorphisms-abelian-groups
open import group-theory.isomorphisms-abelian-groups

open import ring-theory.homomorphisms-rings
open import ring-theory.rings
```

</details>

## Definition

```agda
is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  type-hom-Ring R1 R2 → UU (l1 ⊔ l2)
is-iso-hom-Ring R1 R2 f =
  Σ ( type-hom-Ring R2 R1)
    ( λ g →
      ( Id (comp-hom-Ring R2 R1 R2 f g) (id-hom-Ring R2)) ×
      ( Id (comp-hom-Ring R1 R2 R1 g f) (id-hom-Ring R1)))
```

### Components of a ring isomorphism

```agda
inv-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : type-hom-Ring R1 R2) →
  is-iso-hom-Ring R1 R2 f → type-hom-Ring R2 R1
inv-is-iso-hom-Ring R1 R2 f = pr1

is-section-inv-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : type-hom-Ring R1 R2) →
  ( is-iso-f : is-iso-hom-Ring R1 R2 f) →
  Id
    ( comp-hom-Ring R2 R1 R2 f (inv-is-iso-hom-Ring R1 R2 f is-iso-f))
    ( id-hom-Ring R2)
is-section-inv-is-iso-hom-Ring R1 R2 f is-iso-f = pr1 (pr2 is-iso-f)

is-retraction-inv-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : type-hom-Ring R1 R2) →
  ( is-iso-f : is-iso-hom-Ring R1 R2 f) →
  Id
    ( comp-hom-Ring R1 R2 R1 (inv-is-iso-hom-Ring R1 R2 f is-iso-f) f)
    ( id-hom-Ring R1)
is-retraction-inv-is-iso-hom-Ring R1 R2 f is-iso-f = pr2 (pr2 is-iso-f)

inv-map-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : type-hom-Ring R1 R2) →
  is-iso-hom-Ring R1 R2 f → type-Ring R2 → type-Ring R1
inv-map-is-iso-hom-Ring R1 R2 f is-iso-f =
  map-hom-Ring R2 R1 (inv-is-iso-hom-Ring R1 R2 f is-iso-f)

is-section-inv-map-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : type-hom-Ring R1 R2) →
  ( is-iso-f : is-iso-hom-Ring R1 R2 f) →
  ( (map-hom-Ring R1 R2 f) ∘ (inv-map-is-iso-hom-Ring R1 R2 f is-iso-f)) ~ id
is-section-inv-map-is-iso-hom-Ring R1 R2 f is-iso-f =
  htpy-eq-hom-Ring R2 R2
    ( comp-hom-Ring R2 R1 R2 f (inv-is-iso-hom-Ring R1 R2 f is-iso-f))
    ( id-hom-Ring R2)
    ( is-section-inv-is-iso-hom-Ring R1 R2 f is-iso-f)

is-retraction-inv-map-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : type-hom-Ring R1 R2) →
  ( is-iso-f : is-iso-hom-Ring R1 R2 f) →
  ( (inv-map-is-iso-hom-Ring R1 R2 f is-iso-f) ∘ (map-hom-Ring R1 R2 f)) ~ id
is-retraction-inv-map-is-iso-hom-Ring R1 R2 f is-iso-f =
  htpy-eq-hom-Ring R1 R1
    ( comp-hom-Ring R1 R2 R1 (inv-is-iso-hom-Ring R1 R2 f is-iso-f) f)
    ( id-hom-Ring R1)
    ( is-retraction-inv-is-iso-hom-Ring R1 R2 f is-iso-f)
```

## Properties

### Being invertible is a property

```agda
all-elements-equal-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : type-hom-Ring R1 R2) →
  all-elements-equal (is-iso-hom-Ring R1 R2 f)
all-elements-equal-is-iso-hom-Ring R1 R2 f inv-f inv-f' =
  eq-type-subtype
    ( λ g →
      prod-Prop
        ( Id-Prop
          ( hom-Ring R2 R2)
          ( comp-hom-Ring R2 R1 R2 f g)
          ( id-hom-Ring R2))
        ( Id-Prop
          ( hom-Ring R1 R1)
          ( comp-hom-Ring R1 R2 R1 g f)
          ( id-hom-Ring R1)))
    ( eq-htpy-hom-Ring R2 R1
      ( inv-is-iso-hom-Ring R1 R2 f inv-f)
      ( inv-is-iso-hom-Ring R1 R2 f inv-f')
      ( λ x →
        ( inv
          ( ap
            ( map-hom-Ring R2 R1 (pr1 inv-f))
            ( is-section-inv-map-is-iso-hom-Ring R1 R2 f inv-f' x))) ∙
        ( is-retraction-inv-map-is-iso-hom-Ring R1 R2 f inv-f
          ( map-hom-Ring R2 R1 (pr1 inv-f') x))))

is-prop-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : type-hom-Ring R1 R2) →
  is-prop (is-iso-hom-Ring R1 R2 f)
is-prop-is-iso-hom-Ring R1 R2 f =
  is-prop-all-elements-equal (all-elements-equal-is-iso-hom-Ring R1 R2 f)

iso-Ring :
  { l1 l2 : Level} → Ring l1 → Ring l2 → UU (l1 ⊔ l2)
iso-Ring R1 R2 = Σ (type-hom-Ring R1 R2) (is-iso-hom-Ring R1 R2)

hom-iso-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  iso-Ring R1 R2 → type-hom-Ring R1 R2
hom-iso-Ring R1 R2 = pr1

is-iso-hom-iso-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  ( f : iso-Ring R1 R2) → is-iso-hom-Ring R1 R2 (hom-iso-Ring R1 R2 f)
is-iso-hom-iso-Ring R1 R2 = pr2

inv-hom-iso-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  iso-Ring R1 R2 → type-hom-Ring R2 R1
inv-hom-iso-Ring R1 R2 f =
  inv-is-iso-hom-Ring R1 R2
    ( hom-iso-Ring R1 R2 f)
    ( is-iso-hom-iso-Ring R1 R2 f)

is-iso-id-hom-Ring :
  { l1 : Level} (R1 : Ring l1) → is-iso-hom-Ring R1 R1 (id-hom-Ring R1)
pr1 (is-iso-id-hom-Ring R1) = id-hom-Ring R1
pr1 (pr2 (is-iso-id-hom-Ring R1)) =
  left-unit-law-comp-hom-Ring R1 R1 (id-hom-Ring R1)
pr2 (pr2 (is-iso-id-hom-Ring R1)) =
  left-unit-law-comp-hom-Ring R1 R1 (id-hom-Ring R1)

id-iso-Ring :
  { l1 : Level} (R1 : Ring l1) → iso-Ring R1 R1
pr1 (id-iso-Ring R1) = id-hom-Ring R1
pr2 (id-iso-Ring R1) = is-iso-id-hom-Ring R1

iso-eq-Ring :
  { l : Level} (R1 R2 : Ring l) → Id R1 R2 → iso-Ring R1 R2
iso-eq-Ring R1 .R1 refl = id-iso-Ring R1
```

We first show that a ring homomorphism is an isomorphism if and only if the
underlying homomorphism of abelian groups is an isomorphism.

```agda
is-iso-hom-Ab-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  type-hom-Ring R1 R2 → UU (l1 ⊔ l2)
is-iso-hom-Ab-hom-Ring R1 R2 f =
  is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) (hom-ab-hom-Ring R1 R2 f)

is-iso-hom-Ab-is-iso-hom-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : type-hom-Ring R1 R2) →
  is-iso-hom-Ring R1 R2 f →
  is-iso-hom-Ab-hom-Ring R1 R2 f
pr1 (is-iso-hom-Ab-is-iso-hom-Ring R1 R2 f is-iso-f) =
  hom-ab-hom-Ring R2 R1 (inv-is-iso-hom-Ring R1 R2 f is-iso-f)
pr1 (pr2 (is-iso-hom-Ab-is-iso-hom-Ring R1 R2 f is-iso-f)) =
  ap
    ( hom-ab-hom-Ring R2 R2)
    ( is-section-inv-is-iso-hom-Ring R1 R2 f is-iso-f)
pr2 (pr2 (is-iso-hom-Ab-is-iso-hom-Ring R1 R2 f is-iso-f)) =
  ap
    ( hom-ab-hom-Ring R1 R1)
    ( is-retraction-inv-is-iso-hom-Ring R1 R2 f is-iso-f)

abstract
  preserves-mul-inv-is-iso-hom-Ab :
    { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
    ( f : type-hom-Ab (ab-Ring R1) (ab-Ring R2)) →
    ( is-iso-f : is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f) →
    ( pres-mul-f : preserves-mul-hom-Ab R1 R2 f) →
    preserves-mul-hom-Ab R2 R1
      ( inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f)
  preserves-mul-inv-is-iso-hom-Ab R1 R2 f is-iso-f pres-mul-f x y =
    ( inv
      ( ap
        ( map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f)
        ( ( pres-mul-f
            ( map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f x)
            ( map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f y)) ∙
          ( ( ap
              ( mul-Ring R2
                ( map-hom-Ab (ab-Ring R1) (ab-Ring R2) f
                  ( map-inv-is-iso-hom-Ab
                    ( ab-Ring R1)
                    ( ab-Ring R2)
                    ( f)
                    ( is-iso-f)
                    ( x))))
              ( is-section-map-inv-is-iso-hom-Ab
                ( ab-Ring R1)
                ( ab-Ring R2)
                ( f)
                ( is-iso-f)
                ( y))) ∙
            ( ap
              ( λ z → mul-Ring R2 z y)
              ( is-section-map-inv-is-iso-hom-Ab
                ( ab-Ring R1)
                ( ab-Ring R2)
                ( f)
                ( is-iso-f)
                ( x))))))) ∙
    ( is-retraction-map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f
      ( mul-Ring R1
        ( map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f x)
        ( map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f y)))

preserves-unit-inv-is-iso-hom-Ab :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2)
  ( f : type-hom-Ab (ab-Ring R1) (ab-Ring R2)) →
  ( is-iso-f : is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f)
  ( pres-unit-f : preserves-unit-hom-Ab R1 R2 f) →
  preserves-unit-hom-Ab R2 R1
    ( inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f)
preserves-unit-inv-is-iso-hom-Ab R1 R2 f is-iso-f pres-unit-f =
  ( inv
    ( ap
      ( map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f)
      ( pres-unit-f))) ∙
  ( is-retraction-map-inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f
    ( one-Ring R1))

is-ring-homomorphism-inv-is-iso-hom-Ab :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2)
  ( f : type-hom-Ab (ab-Ring R1) (ab-Ring R2)) →
  ( is-iso-f : is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f) →
  ( is-ring-hom-f : is-ring-homomorphism-hom-Ab R1 R2 f) →
  is-ring-homomorphism-hom-Ab R2 R1
    ( inv-is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) f is-iso-f)
pr1
  ( is-ring-homomorphism-inv-is-iso-hom-Ab
      R1 R2 f is-iso-f (pres-mul-f , pres-unit-f)) =
    preserves-mul-inv-is-iso-hom-Ab R1 R2 f is-iso-f pres-mul-f
pr2
  ( is-ring-homomorphism-inv-is-iso-hom-Ab
      R1 R2 f is-iso-f (pres-mul-f , pres-unit-f)) =
    preserves-unit-inv-is-iso-hom-Ab R1 R2 f is-iso-f pres-unit-f

inv-hom-Ring-is-iso-hom-Ab :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) (f : type-hom-Ring R1 R2) →
  ( is-iso-f :
    is-iso-hom-Ab
      ( ab-Ring R1)
      ( ab-Ring R2)
      ( hom-ab-hom-Ring R1 R2 f)) →
  type-hom-Ring R2 R1
pr1 (inv-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f) =
  inv-is-iso-hom-Ab
    ( ab-Ring R1)
    ( ab-Ring R2)
    ( hom-ab-hom-Ring R1 R2 f)
    ( is-iso-f)
pr2 (inv-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f) =
  is-ring-homomorphism-inv-is-iso-hom-Ab R1 R2
    ( hom-ab-hom-Ring R1 R2 f)
    ( is-iso-f)
    ( is-ring-homomorphism-hom-Ring R1 R2 f)

abstract
  is-iso-hom-Ring-is-iso-hom-Ab :
    { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2)
    ( f : type-hom-Ring R1 R2) →
    is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) (hom-ab-hom-Ring R1 R2 f) →
    is-iso-hom-Ring R1 R2 f
  pr1 (is-iso-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f) =
    inv-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f
  pr1 (pr2 (is-iso-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f)) =
    eq-htpy-hom-Ring R2 R2
      ( comp-hom-Ring R2 R1 R2 f
        ( inv-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f))
      ( id-hom-Ring R2)
      ( htpy-eq-hom-Ab (ab-Ring R2) (ab-Ring R2)
        ( hom-ab-hom-Ring R2 R2
          ( comp-hom-Ring R2 R1 R2 f
            ( inv-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f)))
        ( id-hom-Ab (ab-Ring R2))
        ( is-section-inv-is-iso-hom-Ab
          ( ab-Ring R1)
          ( ab-Ring R2)
          ( hom-ab-hom-Ring R1 R2 f)
          ( is-iso-f)))
  pr2 (pr2 (is-iso-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f)) =
    eq-htpy-hom-Ring R1 R1
      ( comp-hom-Ring R1 R2 R1
        ( inv-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f)
        ( f))
      ( id-hom-Ring R1)
      ( htpy-eq-hom-Ab (ab-Ring R1) (ab-Ring R1)
        ( hom-ab-hom-Ring R1 R1
          ( comp-hom-Ring R1 R2 R1
            ( inv-hom-Ring-is-iso-hom-Ab R1 R2 f is-iso-f)
            ( f)))
        ( id-hom-Ab (ab-Ring R1))
        ( is-retraction-inv-is-iso-hom-Ab
          ( ab-Ring R1)
          ( ab-Ring R2)
          ( hom-ab-hom-Ring R1 R2 f)
          ( is-iso-f)))

iso-Ab-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) → UU (l1 ⊔ l2)
iso-Ab-Ring R1 R2 =
  Σ ( iso-Ab (ab-Ring R1) (ab-Ring R2))
    ( λ f →
      is-ring-homomorphism-hom-Ab R1 R2
        ( hom-iso-Ab (ab-Ring R1) (ab-Ring R2) f))

iso-Ab-iso-Ab-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  iso-Ab-Ring R1 R2 → iso-Ab (ab-Ring R1) (ab-Ring R2)
iso-Ab-iso-Ab-Ring R1 R2 = pr1

iso-Ab-iso-Ring :
  { l1 l2 : Level} (R1 : Ring l1) (R2 : Ring l2) →
  iso-Ring R1 R2 → iso-Ab (ab-Ring R1) (ab-Ring R2)
pr1 (iso-Ab-iso-Ring R1 R2 f) = hom-ab-hom-Ring R1 R2 (hom-iso-Ring R1 R2 f)
pr2 (iso-Ab-iso-Ring R1 R2 f) =
  is-iso-hom-Ab-is-iso-hom-Ring R1 R2
    ( hom-iso-Ring R1 R2 f)
    ( is-iso-hom-iso-Ring R1 R2 f)

equiv-iso-Ab-iso-Ring :
  { l1 : Level} (R1 : Ring l1) (R2 : Ring l1) →
  (iso-Ring R1 R2) ≃ (iso-Ab-Ring R1 R2)
equiv-iso-Ab-iso-Ring R1 R2 =
  ( ( ( inv-equiv
        ( associative-Σ
          ( type-hom-Ab (ab-Ring R1) (ab-Ring R2))
          ( is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2))
          ( λ f → is-ring-homomorphism-hom-Ab R1 R2 (pr1 f)))) ∘e
      ( equiv-tot (λ f → commutative-prod))) ∘e
    ( associative-Σ
      ( type-hom-Ab (ab-Ring R1) (ab-Ring R2))
      ( is-ring-homomorphism-hom-Ab R1 R2)
      ( λ f → is-iso-hom-Ab (ab-Ring R1) (ab-Ring R2) (pr1 f)))) ∘e
  ( equiv-type-subtype
    ( is-prop-is-iso-hom-Ring R1 R2)
    ( λ f →
      is-prop-is-iso-hom-Ab
        ( ab-Ring R1)
        ( ab-Ring R2)
        ( hom-ab-hom-Ring R1 R2 f))
    ( is-iso-hom-Ab-is-iso-hom-Ring R1 R2)
    ( is-iso-hom-Ring-is-iso-hom-Ab R1 R2))

abstract
  is-contr-total-iso-Ring :
    { l : Level} (R : Ring l) → is-contr (Σ (Ring l) (iso-Ring R))
  is-contr-total-iso-Ring {l} R =
    is-contr-equiv
      ( Σ (Ring l) (iso-Ab-Ring R))
      ( equiv-tot (equiv-iso-Ab-iso-Ring R))
      ( is-contr-total-Eq-structure
        ( λ A μ f →
          is-ring-homomorphism-hom-Ab R (pair A μ) (hom-iso-Ab (ab-Ring R) A f))
        ( is-contr-total-iso-Ab (ab-Ring R))
        ( pair (ab-Ring R) (id-iso-Ab (ab-Ring R)))
        ( is-contr-total-Eq-structure
          ( λ μ H pres-mul → Id (one-Ring R) (pr1 (pr1 H)))
          ( is-contr-total-Eq-subtype
            ( is-contr-total-Eq-Π
              ( λ x m → (y : type-Ring R) → Id (mul-Ring R x y) (m y))
              ( λ x → is-contr-total-htpy (mul-Ring R x)))
            ( λ μ → is-prop-Π (λ x → is-prop-Π (λ y → is-prop-Π (λ z →
              is-set-type-Ring R (μ (μ x y) z) (μ x (μ y z))))))
            ( mul-Ring R)
            ( λ x y → refl)
            ( associative-mul-Ring R))
          ( pair (pair (mul-Ring R) (associative-mul-Ring R)) (λ x y → refl))
          ( is-contr-total-Eq-subtype
            ( is-contr-total-Eq-subtype
              ( is-contr-total-path (one-Ring R))
              ( λ x →
                is-prop-prod
                  ( is-prop-Π (λ y → is-set-type-Ring R (mul-Ring R x y) y))
                  ( is-prop-Π (λ y → is-set-type-Ring R (mul-Ring R y x) y)))
              ( one-Ring R)
              ( refl)
              ( pair (left-unit-law-mul-Ring R) (right-unit-law-mul-Ring R)))
            ( λ u →
              is-prop-prod
                ( is-prop-Π (λ x → is-prop-Π (λ y → is-prop-Π (λ z →
                  is-set-type-Ring R
                    ( mul-Ring R x (add-Ring R y z))
                    ( add-Ring R (mul-Ring R x y) (mul-Ring R x z))))))
                ( is-prop-Π (λ x → is-prop-Π (λ y → is-prop-Π (λ z →
                  is-set-type-Ring R
                    ( mul-Ring R (add-Ring R x y) z)
                    ( add-Ring R (mul-Ring R x z) (mul-Ring R y z)))))))
            ( is-unital-Ring R)
            ( refl)
            ( pair
              ( left-distributive-mul-add-Ring R)
              ( right-distributive-mul-add-Ring R)))))

is-equiv-iso-eq-Ring :
  { l : Level} (R S : Ring l) → is-equiv (iso-eq-Ring R S)
is-equiv-iso-eq-Ring R =
  fundamental-theorem-id
    ( is-contr-total-iso-Ring R)
    ( iso-eq-Ring R)

eq-iso-Ring :
  { l : Level} (R S : Ring l) → iso-Ring R S → Id R S
eq-iso-Ring R S = map-inv-is-equiv (is-equiv-iso-eq-Ring R S)
```
