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

open import synthetic-homotopy-theory.double-loop-spaces
open import synthetic-homotopy-theory.eckmann-hilton-argument
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.powers-of-loops
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
hom-algebra-Hatcher-Acyclic-Type :
  {l1 l2 : Level} → algebra-Hatcher-Acyclic-Type l1 →
  algebra-Hatcher-Acyclic-Type l2 → UU (l1 ⊔ l2)
hom-algebra-Hatcher-Acyclic-Type
  (A , a1 , a2 , r1 , r2) (B , b1 , b2 , s1 , s2) =
  Σ ( A →∗ B)
    ( λ f →
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
                ( s2)))))
```

### The Hatcher acyclic type is the initial Hatcher acyclic algebra

```agda
is-initial-algebra-Hatcher-Acyclic-Type :
  {l1 : Level} (l : Level)
  (A : algebra-Hatcher-Acyclic-Type l1) → UU (l1 ⊔ lsuc l)
is-initial-algebra-Hatcher-Acyclic-Type l A =
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
            ( ( pr2 (pr2 (pr2 s)) ∙ ap (power-nat-Ω 2 A) (ap-binary _∙_ p q)) ＝
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
      ( λ (ω : type-Ω A) u (p : pr1 s ＝ ω) →
          Σ ( pr1 (pr2 s) ＝ pr1 u)
            ( λ q →
              ( ( pr1 (pr2 (pr2 s)) ∙ ap (power-nat-Ω 3 A) q) ＝
                ( ap (power-nat-Ω 5 A) p ∙ pr1 (pr2 u))) ×
              ( ( pr2
                  ( pr2 (pr2 s)) ∙ ap (power-nat-Ω 2 A) (ap-binary _∙_ p q)) ＝
                ( ap (power-nat-Ω 3 A) q ∙ pr2 (pr2 u)))))
      ( is-torsorial-path (pr1 s))
      ( pr1 s , refl)
      ( is-torsorial-Eq-structure
        ( λ ω u p →
          Σ ( ( pr1 (pr2 (pr2 s)) ∙ ap (power-nat-Ω 3 A) p) ＝
              ( ap (power-nat-Ω 5 A) {pr1 s} refl ∙ pr1 u))
            ( λ a →
              ( ( pr2 (pr2 (pr2 s))) ∙
                ( ap
                  ( power-nat-Ω 2 A)
                  ( ap-binary _∙_ {pr1 s} {pr1 s} refl p))) ＝
              ( ap (power-nat-Ω 3 A) p ∙ pr2 u)))
        ( is-torsorial-path (pr1 (pr2 s)))
        ( pr1 (pr2 s) , refl)
        ( is-torsorial-Eq-structure
          ( λ u v w → Id (pr2 (pr2 (pr2 s)) ∙ refl) v)
          ( is-torsorial-path (pr1 (pr2 (pr2 s)) ∙ refl))
          ( pr1 (pr2 (pr2 s)) , right-unit)
          ( is-torsorial-path (pr2 (pr2 (pr2 s)) ∙ refl))))

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
                ( is-torsorial-path' (a ∙ a))
                ( a ∙ a , refl)) ∘e
              ( inv-associative-Σ
                ( type-Ω (Ω A))
                ( λ b → b ＝ (a ∙ a))
                ( λ bq →
                  power-nat-Ω 5 (Ω A) a ＝ power-nat-Ω 3 (Ω A) (pr1 bq)))) ∘e
            ( equiv-tot
              ( λ b →
                ( commutative-prod) ∘e
                ( equiv-prod
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
        ( is-torsorial-path refl)
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
