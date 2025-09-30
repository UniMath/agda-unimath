# Equivalences between semigroups

```agda
module group-theory.equivalences-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups
open import group-theory.semigroups
```

</details>

## Idea

An equivalence between semigroups is an equivalence between their underlying
types that preserves the binary operation.

## Definition

### Equivalences preserving binary operations

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  preserves-mul-equiv :
    (μA : A → A → A) (μB : B → B → B) → (A ≃ B) → UU (l1 ⊔ l2)
  preserves-mul-equiv μA μB e = preserves-mul μA μB (map-equiv e)
```

### Equivalences of semigroups

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  preserves-mul-equiv-Semigroup :
    (type-Semigroup G ≃ type-Semigroup H) → UU (l1 ⊔ l2)
  preserves-mul-equiv-Semigroup e =
    preserves-mul-equiv (mul-Semigroup G) (mul-Semigroup H) e

  equiv-Semigroup : UU (l1 ⊔ l2)
  equiv-Semigroup =
    Σ (type-Semigroup G ≃ type-Semigroup H) preserves-mul-equiv-Semigroup

  is-equiv-hom-Semigroup : hom-Semigroup G H → UU (l1 ⊔ l2)
  is-equiv-hom-Semigroup f = is-equiv (map-hom-Semigroup G H f)
```

## Properties

### The total space of all equivalences of semigroups with domain `G` is contractible

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  center-total-preserves-mul-id-Semigroup :
    Σ ( has-associative-mul (type-Semigroup G))
      ( λ μ → preserves-mul-Semigroup G (pair (set-Semigroup G) μ) id)
  pr1 (pr1 (center-total-preserves-mul-id-Semigroup)) = mul-Semigroup G
  pr2 (pr1 (center-total-preserves-mul-id-Semigroup)) =
    associative-mul-Semigroup G
  pr2 (center-total-preserves-mul-id-Semigroup) = refl

  contraction-total-preserves-mul-id-Semigroup :
    ( t : Σ ( has-associative-mul (type-Semigroup G))
            ( λ μ →
              preserves-mul-Semigroup G (pair (set-Semigroup G) μ) id)) →
    center-total-preserves-mul-id-Semigroup ＝ t
  contraction-total-preserves-mul-id-Semigroup
    ( (μ-G' , associative-G') , μ-id) =
    eq-type-subtype
      ( λ μ →
        preserves-mul-prop-Semigroup G (pair (set-Semigroup G) μ) id)
      ( eq-type-subtype
        ( λ μ →
          Π-Prop
            ( type-Semigroup G)
            ( λ x →
              Π-Prop
                ( type-Semigroup G)
                ( λ y →
                  Π-Prop
                    ( type-Semigroup G)
                    ( λ z →
                      Id-Prop
                        ( set-Semigroup G)
                        ( μ (μ x y) z) (μ x (μ y z))))))
        ( eq-htpy (λ x → eq-htpy (λ y → μ-id))))

  is-torsorial-preserves-mul-id-Semigroup :
    is-torsorial
      ( λ (μ : has-associative-mul (type-Semigroup G)) →
        preserves-mul (mul-Semigroup G) (pr1 μ) id)
  pr1 is-torsorial-preserves-mul-id-Semigroup =
    center-total-preserves-mul-id-Semigroup
  pr2 is-torsorial-preserves-mul-id-Semigroup =
    contraction-total-preserves-mul-id-Semigroup

  is-torsorial-equiv-Semigroup :
    is-torsorial (equiv-Semigroup G)
  is-torsorial-equiv-Semigroup =
    is-torsorial-Eq-structure
      ( is-torsorial-Eq-subtype
        ( is-torsorial-equiv (type-Semigroup G))
        ( is-prop-is-set)
        ( type-Semigroup G)
        ( id-equiv)
        ( is-set-type-Semigroup G))
      ( pair (set-Semigroup G) id-equiv)
      ( is-torsorial-preserves-mul-id-Semigroup)
```
