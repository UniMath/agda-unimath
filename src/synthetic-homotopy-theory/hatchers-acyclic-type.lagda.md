# Hatcher's acyclic type

```agda
module synthetic-homotopy-theory.hatchers-acyclic-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-identifications
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.pointed-universal-property-contractible-types

open import synthetic-homotopy-theory.acyclic-types
open import synthetic-homotopy-theory.eckmann-hilton-argument
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.powers-of-loops
open import synthetic-homotopy-theory.suspensions-of-pointed-types
open import synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types
```

</details>

## Idea

**Hatcher's [acyclic type](synthetic-homotopy-theory.acyclic-types.md)** is a
higher inductive type [equipped](foundation.structure.md) with a base point and
two [loops](synthetic-homotopy-theory.loop-spaces.md) `a` and `b`, and
[identifications](foundation.identity-types.md) witnessing that `a⁵ ＝ b³` and
`b³ = (ab)²`. This type is acyclic, because the structure on Hatcher's acyclic
type on any loop space is [contractible](foundation.contractible-types.md).

## Definitions

### The structure of Hatcher's acyclic type

```agda
structure-Hatcher-Acyclic-Type : {l : Level} → Pointed-Type l → UU l
structure-Hatcher-Acyclic-Type A =
  Σ ( type-Ω A)
    ( λ a →
      Σ ( type-Ω A)
        ( λ b →
          ( power-nat-Ω 5 A a ＝ power-nat-Ω 3 A b) ×
          ( power-nat-Ω 3 A b ＝ power-nat-Ω 2 A (a ∙ b))))
```

### Algebras with the structure of Hatcher's acyclic type

```agda
algebra-Hatcher-Acyclic-Type : (l : Level) → UU (lsuc l)
algebra-Hatcher-Acyclic-Type l =
  Σ (Pointed-Type l) structure-Hatcher-Acyclic-Type
```

### Morphisms of types equipped with the structure of Hatcher's acyclic type

```agda
module _
  {l1 l2 : Level}
  ((A , a1 , a2 , r1 , r2) : algebra-Hatcher-Acyclic-Type l1)
  ((B , b1 , b2 , s1 , s2) : algebra-Hatcher-Acyclic-Type l2)
  where

  is-hom-pointed-map-algebra-Hatcher-Acyclic-Type : (A →∗ B) → UU l2
  is-hom-pointed-map-algebra-Hatcher-Acyclic-Type f =
    Σ ( map-Ω f a1 ＝ b1)
      ( λ u →
        Σ ( map-Ω f a2 ＝ b2)
          ( λ v →
            ( coherence-square-identifications
              ( ap (map-Ω f) r1)
              ( map-power-nat-Ω 5 f a1 ∙ ap (power-nat-Ω 5 B) u)
              ( map-power-nat-Ω 3 f a2 ∙ ap (power-nat-Ω 3 B) v)
              ( s1)) ×
            ( coherence-square-identifications
              ( ap (map-Ω f) r2)
              ( map-power-nat-Ω 3 f a2 ∙ ap (power-nat-Ω 3 B) v)
              ( ( map-power-nat-Ω 2 f (a1 ∙ a2)) ∙
                ( ap
                  ( power-nat-Ω 2 B)
                  ( ( preserves-mul-map-Ω f) ∙
                    ( horizontal-concat-Id² u v))))
              ( s2))))

  hom-algebra-Hatcher-Acyclic-Type : UU (l1 ⊔ l2)
  hom-algebra-Hatcher-Acyclic-Type =
    Σ ( A →∗ B) is-hom-pointed-map-algebra-Hatcher-Acyclic-Type
```

### Initial Hatcher acyclic algebras

One characterization of Hatcher's acyclic type is through its universal property
as being the initial Hatcher acyclic algebra.

```agda
is-initial-algebra-Hatcher-Acyclic-Type :
  {l1 : Level} (A : algebra-Hatcher-Acyclic-Type l1) → UUω
is-initial-algebra-Hatcher-Acyclic-Type A =
  {l : Level} →
  (B : algebra-Hatcher-Acyclic-Type l) →
  is-contr (hom-algebra-Hatcher-Acyclic-Type A B)
```

## Properties

### Characterization of identifications of Hatcher acyclic type structures

```agda
module _
  {l : Level} (A : Pointed-Type l) (s : structure-Hatcher-Acyclic-Type A)
  where

  Eq-structure-Hatcher-Acyclic-Type :
    structure-Hatcher-Acyclic-Type A → UU l
  Eq-structure-Hatcher-Acyclic-Type t =
    Σ ( pr1 s ＝ pr1 t)
      ( λ p →
        Σ ( pr1 (pr2 s) ＝ pr1 (pr2 t))
          ( λ q →
            ( ( pr1 (pr2 (pr2 s)) ∙ ap (power-nat-Ω 3 A) q) ＝
              ( (ap (power-nat-Ω 5 A) p) ∙ pr1 (pr2 (pr2 t)))) ×
            ( ( pr2 (pr2 (pr2 s)) ∙
                ap (power-nat-Ω 2 A) (horizontal-concat-Id² p q)) ＝
              ( ap (power-nat-Ω 3 A) q ∙ pr2 (pr2 (pr2 t))))))

  refl-Eq-structure-Hatcher-Acyclic-Type :
    Eq-structure-Hatcher-Acyclic-Type s
  pr1 refl-Eq-structure-Hatcher-Acyclic-Type = refl
  pr1 (pr2 refl-Eq-structure-Hatcher-Acyclic-Type) = refl
  pr1 (pr2 (pr2 refl-Eq-structure-Hatcher-Acyclic-Type)) = right-unit
  pr2 (pr2 (pr2 refl-Eq-structure-Hatcher-Acyclic-Type)) = right-unit

  is-torsorial-Eq-structure-Hatcher-Acyclic-Type :
    is-torsorial Eq-structure-Hatcher-Acyclic-Type
  is-torsorial-Eq-structure-Hatcher-Acyclic-Type =
    is-torsorial-Eq-structure
      ( is-torsorial-Id (pr1 s))
      ( pr1 s , refl)
      ( is-torsorial-Eq-structure
        ( is-torsorial-Id (pr1 (pr2 s)))
        ( pr1 (pr2 s) , refl)
        ( is-torsorial-Eq-structure
          ( is-torsorial-Id (pr1 (pr2 (pr2 s)) ∙ refl))
          ( pr1 (pr2 (pr2 s)) , right-unit)
          ( is-torsorial-Id (pr2 (pr2 (pr2 s)) ∙ refl))))

  Eq-eq-structure-Hatcher-Acyclic-Type :
    (t : structure-Hatcher-Acyclic-Type A) →
    (s ＝ t) → Eq-structure-Hatcher-Acyclic-Type t
  Eq-eq-structure-Hatcher-Acyclic-Type .s refl =
    refl-Eq-structure-Hatcher-Acyclic-Type

  is-equiv-Eq-eq-structure-Hatcher-Acyclic-Type :
    (t : structure-Hatcher-Acyclic-Type A) →
    is-equiv (Eq-eq-structure-Hatcher-Acyclic-Type t)
  is-equiv-Eq-eq-structure-Hatcher-Acyclic-Type =
    fundamental-theorem-id
      is-torsorial-Eq-structure-Hatcher-Acyclic-Type
      Eq-eq-structure-Hatcher-Acyclic-Type

  extensionality-structure-Hatcher-Acyclic-Type :
    (t : structure-Hatcher-Acyclic-Type A) →
    (s ＝ t) ≃ Eq-structure-Hatcher-Acyclic-Type t
  pr1 (extensionality-structure-Hatcher-Acyclic-Type t) =
    Eq-eq-structure-Hatcher-Acyclic-Type t
  pr2 (extensionality-structure-Hatcher-Acyclic-Type t) =
    is-equiv-Eq-eq-structure-Hatcher-Acyclic-Type t

  eq-Eq-structure-Hatcher-Acyclic-Type :
    (t : structure-Hatcher-Acyclic-Type A) →
    Eq-structure-Hatcher-Acyclic-Type t → s ＝ t
  eq-Eq-structure-Hatcher-Acyclic-Type t =
    map-inv-equiv (extensionality-structure-Hatcher-Acyclic-Type t)
```

### Loop spaces uniquely have the structure of a Hatcher acyclic type

```agda
module _
  {l : Level} (A : Pointed-Type l)
  where

  is-contr-structure-Hatcher-Acyclic-Type-Ω :
    is-contr (structure-Hatcher-Acyclic-Type (Ω A))
  is-contr-structure-Hatcher-Acyclic-Type-Ω =
    is-contr-equiv
      ( Σ (type-Ω (Ω A)) (λ a → refl ＝ a))
      ( equiv-tot
        ( λ a →
          ( ( inv-equiv
              ( equiv-ap
                ( equiv-concat' (refl-Ω A) (power-nat-Ω 5 (Ω A) a))
                ( refl-Ω (Ω A))
                ( a))) ∘e
            ( equiv-concat'
              ( power-nat-Ω 5 (Ω A) a)
              ( ( inv (power-nat-mul-Ω 3 2 (Ω A) a)) ∙
                ( power-nat-succ-Ω' 5 (Ω A) a)))) ∘e
          ( ( ( left-unit-law-Σ-is-contr
                ( is-torsorial-Id' (a ∙ a))
                ( a ∙ a , refl)) ∘e
              ( inv-associative-Σ)) ∘e
            ( equiv-tot
              ( λ b →
                ( commutative-product) ∘e
                ( equiv-product
                  ( id-equiv)
                  ( ( ( inv-equiv
                        ( equiv-ap
                          ( equiv-concat' (refl-Ω A) (b ∙ b))
                          ( b)
                          ( a ∙ a))) ∘e
                      ( equiv-concat
                        ( inv (power-nat-add-Ω 1 2 (Ω A) b))
                        ( (a ∙ a) ∙ (b ∙ b)))) ∘e
                    ( equiv-concat'
                      ( power-nat-Ω 3 (Ω A) b)
                      ( interchange-concat-Ω² a b a b)))))))))
        ( is-torsorial-Id refl)
```

### For a fixed pointed map, the `is-hom-pointed-map-algebra-Hatcher-Acyclic-Type` family is torsorial

In proving this, it is helpful to consider an equivalent formulation of
`is-hom-pointed-map-algebra-Hatcher-Acyclic-Type` for which
[torsoriality](foundation.torsorial-type-families.md) is almost immediate.

```agda
module _
  {l1 l2 : Level}
  ((A , a1 , a2 , r1 , r2) : algebra-Hatcher-Acyclic-Type l1)
  ((B , b1 , b2 , s1 , s2) : algebra-Hatcher-Acyclic-Type l2)
  where

  is-hom-pointed-map-algebra-Hatcher-Acyclic-Type' : (A →∗ B) → UU l2
  is-hom-pointed-map-algebra-Hatcher-Acyclic-Type' f =
    Σ ( map-Ω f a1 ＝ b1)
      ( λ u →
        Σ ( map-Ω f a2 ＝ b2)
          ( λ v →
            ( Id
              ( inv (map-power-nat-Ω 5 f a1 ∙ ap (power-nat-Ω 5 B) u) ∙
                ( ap (map-Ω f) r1 ∙
                  (map-power-nat-Ω 3 f a2 ∙ ap (power-nat-Ω 3 B) v)))
              ( s1)) ×
            ( Id
              ( inv (map-power-nat-Ω 3 f a2 ∙ ap (power-nat-Ω 3 B) v) ∙
                ( ap (map-Ω f) r2 ∙
                  ( ( map-power-nat-Ω 2 f (a1 ∙ a2)) ∙
                    ( ap
                      ( power-nat-Ω 2 B)
                      ( ( preserves-mul-map-Ω f) ∙
                        ( horizontal-concat-Id² u v))))))
              ( s2))))

module _
  {l1 l2 : Level}
  ((A , σ) : algebra-Hatcher-Acyclic-Type l1)
  ((B , τ) : algebra-Hatcher-Acyclic-Type l2)
  where

  equiv-is-hom-pointed-map-algebra-Hatcher-Acyclic-Type :
    (f : A →∗ B) →
    is-hom-pointed-map-algebra-Hatcher-Acyclic-Type (A , σ) (B , τ) f ≃
    is-hom-pointed-map-algebra-Hatcher-Acyclic-Type' (A , σ) (B , τ) f
  equiv-is-hom-pointed-map-algebra-Hatcher-Acyclic-Type f =
    equiv-tot
      ( λ p →
        equiv-tot
          ( λ q →
            equiv-product
              ( equiv-left-transpose-eq-concat' _ _ _ ∘e equiv-inv _ _)
              ( equiv-left-transpose-eq-concat' _ _ _ ∘e equiv-inv _ _)))

module _
  {l1 l2 : Level}
  (A : Pointed-Type l1)
  (B : Pointed-Type l2)
  (σ@(a1 , a2 , r1 , r2) : structure-Hatcher-Acyclic-Type A)
  (f : A →∗ B)
  where

  is-torsorial-is-hom-pointed-map-algebra-Hatcher-Acyclic-Type' :
    is-torsorial
      ( λ τ →
        is-hom-pointed-map-algebra-Hatcher-Acyclic-Type' (A , σ) (B , τ) f)
  is-torsorial-is-hom-pointed-map-algebra-Hatcher-Acyclic-Type' =
    is-torsorial-Eq-structure
      ( is-torsorial-Id (map-Ω f a1)) ((map-Ω f a1) , refl)
      ( is-torsorial-Eq-structure
        ( is-torsorial-Id (map-Ω f a2)) ((map-Ω f a2) , refl)
        ( is-torsorial-Eq-structure
          ( is-torsorial-Id _)
          ( _ , refl)
          ( is-torsorial-Id _)))

  abstract
    is-torsorial-is-hom-pointed-map-algebra-Hatcher-Acyclic-Type :
      is-torsorial
        ( λ τ →
          is-hom-pointed-map-algebra-Hatcher-Acyclic-Type (A , σ) (B , τ) f)
    is-torsorial-is-hom-pointed-map-algebra-Hatcher-Acyclic-Type =
      is-contr-equiv
        ( Σ ( structure-Hatcher-Acyclic-Type B)
            ( λ τ →
              is-hom-pointed-map-algebra-Hatcher-Acyclic-Type'
                ( A , σ)
                ( B , τ)
                ( f)))
        ( equiv-tot
          ( λ τ →
            equiv-is-hom-pointed-map-algebra-Hatcher-Acyclic-Type
              ( A , σ)
              ( B , τ)
              ( f)))
        ( is-torsorial-is-hom-pointed-map-algebra-Hatcher-Acyclic-Type')
```

### Characterization of pointed maps out of Hatcher's acyclic type

For the initial Hatcher acyclic algebra `A` and any pointed type `B`, we exhibit
an equivalence `(A →∗ B) ≃ structure-Hatcher-Acyclic-Type B`.

We first show that for any Hatcher acyclic algebra `A` (so not necessarily the
initial one) and a pointed type `B`, a pointed map `f : A →∗ B` induces a
Hatcher acyclic structure on `B`. Moreover, with this induced structure, the map
`f` becomes a homomorphism of Hatcher acyclic algebras.

```agda
module _
    {l1 l2 : Level}
    (A : Pointed-Type l1)
    (B : Pointed-Type l2)
    (σ@(a1 , a2 , r1 , r2) : structure-Hatcher-Acyclic-Type A)
    where

  map-Ω-structure-Hatcher-Acyclic-Type :
    (f : A →∗ B) →
    ( power-nat-Ω 5 B (map-Ω f a1) ＝
      power-nat-Ω 3 B (map-Ω f a2)) ×
    ( power-nat-Ω 3 B (map-Ω f a2) ＝
      power-nat-Ω 2 B (mul-Ω B (map-Ω f a1) (map-Ω f a2)))
  pr1 (map-Ω-structure-Hatcher-Acyclic-Type f) =
    inv (map-power-nat-Ω 5 f a1) ∙ (ap (map-Ω f) r1 ∙ map-power-nat-Ω 3 f a2)
  pr2 (map-Ω-structure-Hatcher-Acyclic-Type f) =
    inv (map-power-nat-Ω 3 f a2) ∙
    ( ap (map-Ω f) r2 ∙
      ( map-power-nat-Ω 2 f (a1 ∙ a2) ∙
        ap (power-nat-Ω 2 B) (preserves-mul-map-Ω f)))

  structure-Hatcher-Acyclic-Type-pointed-map :
    (A →∗ B) → structure-Hatcher-Acyclic-Type B
  pr1 (structure-Hatcher-Acyclic-Type-pointed-map f) = map-Ω f a1
  pr1 (pr2 (structure-Hatcher-Acyclic-Type-pointed-map f)) = map-Ω f a2
  (pr2 (pr2 (structure-Hatcher-Acyclic-Type-pointed-map f))) =
    map-Ω-structure-Hatcher-Acyclic-Type f

  hom-algebra-Hatcher-Acyclic-Type-pointed-map' :
    (f : A →∗ B) →
    is-hom-pointed-map-algebra-Hatcher-Acyclic-Type'
      ( A , σ)
      ( B , structure-Hatcher-Acyclic-Type-pointed-map f)
      ( f)
  pr1 (hom-algebra-Hatcher-Acyclic-Type-pointed-map' f) = refl
  pr1 (pr2 (hom-algebra-Hatcher-Acyclic-Type-pointed-map' f)) = refl
  pr1 (pr2 (pr2 (hom-algebra-Hatcher-Acyclic-Type-pointed-map' f))) =
    ap-binary
      ( λ p q → inv p ∙ (ap (map-Ω f) r1 ∙ q))
      ( right-unit {p = map-power-nat-Ω 5 f a1})
      ( right-unit)
  pr2 (pr2 (pr2 (hom-algebra-Hatcher-Acyclic-Type-pointed-map' f))) =
    ap-binary
      ( λ p q →
        inv p ∙
        ( ap (map-Ω f) r2 ∙
          ( map-power-nat-Ω 2 f (a1 ∙ a2) ∙ ap (power-nat-Ω 2 B) q)))
      ( right-unit {p = map-power-nat-Ω 3 f a2})
      ( right-unit {p = preserves-mul-map-Ω f})

  hom-algebra-Hatcher-Acyclic-Type-pointed-map :
    (f : A →∗ B) →
    is-hom-pointed-map-algebra-Hatcher-Acyclic-Type
      ( A , σ)
      ( B , structure-Hatcher-Acyclic-Type-pointed-map f)
      ( f)
  hom-algebra-Hatcher-Acyclic-Type-pointed-map f =
    map-inv-equiv
      ( equiv-is-hom-pointed-map-algebra-Hatcher-Acyclic-Type
        ( A , σ)
        ( B , structure-Hatcher-Acyclic-Type-pointed-map f)
        ( f))
      ( hom-algebra-Hatcher-Acyclic-Type-pointed-map' f)

  is-equiv-structure-Hatcher-Acyclic-Type-pointed-map :
    is-initial-algebra-Hatcher-Acyclic-Type (A , σ) →
    is-equiv structure-Hatcher-Acyclic-Type-pointed-map
  is-equiv-structure-Hatcher-Acyclic-Type-pointed-map i =
    is-equiv-htpy-equiv
      ( equivalence-reasoning
          A →∗ B
          ≃ Σ ( A →∗ B)
              ( λ f →
                Σ ( structure-Hatcher-Acyclic-Type B)
                  ( λ τ →
                    is-hom-pointed-map-algebra-Hatcher-Acyclic-Type
                      ( A , σ)
                      ( B , τ)
                      ( f)))
            by inv-right-unit-law-Σ-is-contr
              ( λ f →
                is-torsorial-is-hom-pointed-map-algebra-Hatcher-Acyclic-Type
                  ( A)
                  ( B)
                  ( σ)
                  ( f))
          ≃ Σ ( structure-Hatcher-Acyclic-Type B)
              ( λ τ → hom-algebra-Hatcher-Acyclic-Type (A , σ) (B , τ))
            by equiv-left-swap-Σ
          ≃ structure-Hatcher-Acyclic-Type B
            by equiv-pr1 (λ τ → i (B , τ)))
      ( λ f →
        ap
          ( pr1)
          ( inv
            ( contraction
              ( is-torsorial-is-hom-pointed-map-algebra-Hatcher-Acyclic-Type A B
                ( σ)
                ( f))
              ( structure-Hatcher-Acyclic-Type-pointed-map f ,
                hom-algebra-Hatcher-Acyclic-Type-pointed-map f))))

  equiv-pointed-map-Hatcher-Acyclic-Type :
    is-initial-algebra-Hatcher-Acyclic-Type (A , σ) →
    (A →∗ B) ≃ structure-Hatcher-Acyclic-Type B
  pr1 (equiv-pointed-map-Hatcher-Acyclic-Type i) =
    structure-Hatcher-Acyclic-Type-pointed-map
  pr2 (equiv-pointed-map-Hatcher-Acyclic-Type i) =
    is-equiv-structure-Hatcher-Acyclic-Type-pointed-map i
```

### Hatcher's acyclic type is acyclic

**Proof:** For the Hatcher acyclic type `A`, and any pointed type `X`, we have

```text
 (Σ A →∗ X) ≃ (A →∗ Ω X) ≃ structure-Hatcher-Acyclic-Type (Ω X),
```

where the first equivalence is the
[suspension-loop space adjunction](synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types.md),
the second equivalence was just proven above, and the latter type is
contractible, as shown by `is-contr-structure-Hatcher-Acyclic-Type-Ω`.

Hence, the suspension `Σ A` of `A` satisfies the
[universal property of contractible types with respect to pointed types and maps](structured-types.pointed-universal-property-contractible-types.md),
and hence must be contractible.

```agda
module _
  {l1 : Level}
  ((A , σ) : algebra-Hatcher-Acyclic-Type l1)
  where

  is-acyclic-is-initial-algebra-Hatcher-Acyclic-Type :
    is-initial-algebra-Hatcher-Acyclic-Type (A , σ) →
    is-acyclic (type-Pointed-Type A)
  is-acyclic-is-initial-algebra-Hatcher-Acyclic-Type i =
    is-contr-universal-property-contr-Pointed-Type
      ( suspension-Pointed-Type A)
      ( λ X →
        is-contr-equiv
          ( structure-Hatcher-Acyclic-Type (Ω X))
          ( ( equiv-pointed-map-Hatcher-Acyclic-Type A (Ω X) σ i) ∘e
            ( equiv-transpose-suspension-loop-adjunction A X))
          ( is-contr-structure-Hatcher-Acyclic-Type-Ω X))
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
