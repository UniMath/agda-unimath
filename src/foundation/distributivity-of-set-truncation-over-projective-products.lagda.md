# Distributivity of set truncation over projective products

```agda
module foundation.distributivity-of-set-truncation-over-projective-products where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-extensionality-axiom
open import foundation.function-types
open import foundation.functoriality-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.mere-equality
open import foundation.projective-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-truncations
open import foundation.sets
open import foundation.surjective-maps
open import foundation.truncation-levels
open import foundation.universal-property-set-quotients
open import foundation.universe-levels
```

</details>

## Idea

[Set truncation](foundation.set-truncations.md) distributes over dependent
products on [projective](foundation.projective-types.md) types $X$. The
distributive map

$$
  ║ (x : X) → A(x) ║₀ → ((x : X) → ║ A(x) ║₀)
$$

is an [equivalence](foundation-core.equivalences.md)

## Properties

### Distributivity of set truncation over projective types

```agda
module _
  {l1 l2 : Level} (X : UU l1) (Y : X → UU l2)
  where

  set-map-Π-unit-trunc : Set (l1 ⊔ l2)
  set-map-Π-unit-trunc =
    ( ( (x : X) → ║ Y x ║₀) ,
      ( is-set-Π (λ x → is-set-type-trunc-Set {A = Y x})))

  mere-eq-map-Π-unit-trunc-is-projective-Level :
    (H : is-projective-Level l2 X)
    (f g : (x : X) → Y x) →
    map-Π (λ x → unit-trunc-Set) f ＝ map-Π (λ x → unit-trunc-Set) g →
    mere-eq f g
  mere-eq-map-Π-unit-trunc-is-projective-Level H f g p =
    map-is-inhabited
      ( eq-htpy)
      ( H ( λ x → f x ＝ g x)
          ( λ x → apply-effectiveness-unit-trunc-Set (htpy-eq p x)))

  reflecting-map-map-Π-unit-trunc :
    reflecting-map-equivalence-relation
      ( mere-eq-equivalence-relation ((x : X) → Y x))
      ( type-Set set-map-Π-unit-trunc)
  pr1 reflecting-map-map-Π-unit-trunc =
    map-Π (λ x → unit-trunc-Set)
  pr2 reflecting-map-map-Π-unit-trunc {f} {g} r =
    apply-universal-property-trunc-Prop
      ( r)
      ( Id-Prop
        ( set-map-Π-unit-trunc)
        ( map-Π (λ x → unit-trunc-Set) f)
        ( map-Π (λ x → unit-trunc-Set) g))
      ( ap (map-Π (λ x → unit-trunc-Set)))

  map-map-Π-unit-trunc-trunc-is-projective-Level :
    (H : is-projective-Level l2 X) →
    ║ ((x : X) → Y x) ║₀ →
    (x : X) → ║ Y x ║₀
  map-map-Π-unit-trunc-trunc-is-projective-Level H =
    map-universal-property-set-quotient-is-set-quotient
      ( mere-eq-equivalence-relation ((x : X) → Y x))
      ( trunc-Set ((x : X) → Y x))
      ( reflecting-map-mere-eq-unit-trunc-Set ((x : X) → Y x))
      ( is-set-quotient-trunc-Set ((x : X) → Y x))
      ( set-map-Π-unit-trunc)
      ( reflecting-map-map-Π-unit-trunc)

  triangle-map-map-Π-unit-trunc-trunc-is-projective-Level :
    (H : is-projective-Level l2 X) →
    map-map-Π-unit-trunc-trunc-is-projective-Level H ∘ unit-trunc-Set ~
    map-Π (λ x → unit-trunc-Set)
  triangle-map-map-Π-unit-trunc-trunc-is-projective-Level H =
    triangle-universal-property-set-quotient-is-set-quotient
      ( mere-eq-equivalence-relation ((x : X) → Y x))
      ( trunc-Set ((x : X) → Y x))
      ( reflecting-map-mere-eq-unit-trunc-Set ((x : X) → Y x))
      ( is-set-quotient-trunc-Set ((x : X) → Y x))
      ( set-map-Π-unit-trunc)
      ( reflecting-map-map-Π-unit-trunc)

  htpy-map-distributive-trunc-Π-map-map-Π-unit-trunc-trunc-is-projective-Level :
    (H : is-projective-Level l2 X) →
    map-distributive-trunc-Π zero-𝕋 Y ~
    map-map-Π-unit-trunc-trunc-is-projective-Level H
  htpy-map-distributive-trunc-Π-map-map-Π-unit-trunc-trunc-is-projective-Level
    H t =
    apply-universal-property-trunc-Prop
      ( is-surjective-unit-trunc-Set ((x : X) → Y x) t)
      ( Id-Prop
        ( set-map-Π-unit-trunc)
        ( map-distributive-trunc-Π zero-𝕋 Y t)
        ( map-map-Π-unit-trunc-trunc-is-projective-Level H t))
      ( λ (f , qf) →
        ( inv
          ( ap
            ( map-distributive-trunc-Π zero-𝕋 Y)
            ( qf))) ∙
        ( eq-htpy (compute-distributive-trunc-Π zero-𝕋 f)) ∙
        ( inv (triangle-map-map-Π-unit-trunc-trunc-is-projective-Level H f)) ∙
        ( ap (map-map-Π-unit-trunc-trunc-is-projective-Level H) (qf)))

  is-surjective-map-distributive-trunc-Π-is-projective-Level :
    is-projective-Level l2 X →
    is-surjective (map-distributive-trunc-Π zero-𝕋 Y)
  is-surjective-map-distributive-trunc-Π-is-projective-Level H t =
    map-is-inhabited
      ( λ s →
        ( unit-trunc-Set (λ x → pr1 (s x)) ,
          eq-htpy
            ( λ x →
              ( compute-distributive-trunc-Π zero-𝕋 (λ y → pr1 (s y)) x) ∙
              ( pr2 (s x)))))
      ( H ( λ x → fiber (unit-trunc-Set {A = Y x}) (t x))
          ( λ x → is-surjective-unit-trunc-Set (Y x) (t x)))

  is-emb-map-distributive-trunc-Π-is-projective-Level :
    is-projective-Level l2 X →
    is-emb (map-distributive-trunc-Π zero-𝕋 Y)
  is-emb-map-distributive-trunc-Π-is-projective-Level H =
    is-emb-htpy
      ( htpy-map-distributive-trunc-Π-map-map-Π-unit-trunc-trunc-is-projective-Level
        ( H))
      ( is-emb-map-universal-property-set-quotient-is-set-quotient
        ( mere-eq-equivalence-relation ((x : X) → Y x))
        ( trunc-Set ((x : X) → Y x))
        ( reflecting-map-mere-eq-unit-trunc-Set ((x : X) → Y x))
        ( is-set-quotient-trunc-Set ((x : X) → Y x))
        ( set-map-Π-unit-trunc)
        ( reflecting-map-map-Π-unit-trunc)
        ( mere-eq-map-Π-unit-trunc-is-projective-Level H))

  is-equiv-map-distributive-trunc-Π-is-projective-Level :
    is-projective-Level l2 X →
    is-equiv (map-distributive-trunc-Π zero-𝕋 Y)
  is-equiv-map-distributive-trunc-Π-is-projective-Level H =
    is-equiv-is-emb-is-surjective
      ( is-surjective-map-distributive-trunc-Π-is-projective-Level H)
      ( is-emb-map-distributive-trunc-Π-is-projective-Level H)

  distributive-trunc-Π-is-projective-Level :
    is-projective-Level l2 X →
    is-contr
      ( Σ ( ║ ((x : X) → Y x) ║₀ ≃ ( (x : X) → ║ Y x ║₀))
          ( λ e → map-equiv e ∘ unit-trunc-Set ~ map-Π (λ x → unit-trunc-Set)))
  distributive-trunc-Π-is-projective-Level H =
    uniqueness-trunc-Set
      ( set-map-Π-unit-trunc)
      ( map-Π (λ x → unit-trunc-Set))
      ( is-set-truncation-is-equiv
        ( set-map-Π-unit-trunc)
        ( map-Π (λ x → unit-trunc-Set))
        ( λ f → eq-htpy (compute-distributive-trunc-Π zero-𝕋 f))
        ( is-equiv-map-distributive-trunc-Π-is-projective-Level H))
```

### Set truncation distributes over dependent products over set-projective sets

```agda
module _
  {l1 l2 : Level} (X : UU l1) (Y : X → UU l2)
  where

  is-equiv-map-distributive-trunc-Π-is-set-projective :
    is-set X →
    is-set-projective X →
    is-equiv (map-distributive-trunc-Π zero-𝕋 Y)
  is-equiv-map-distributive-trunc-Π-is-set-projective K H =
    is-equiv-map-distributive-trunc-Π-is-projective-Level X Y
      ( is-projective-is-set-projective K H {l2})

  distributive-trunc-Π-is-set-projective :
    is-set X →
    is-set-projective X →
    is-contr
      ( Σ ( ║ ((x : X) → Y x) ║₀ ≃ ((x : X) → ║ Y x ║₀))
          ( λ e → map-equiv e ∘ unit-trunc-Set ~ map-Π (λ x → unit-trunc-Set)))
  distributive-trunc-Π-is-set-projective K H =
    distributive-trunc-Π-is-projective-Level X Y
      ( is-projective-is-set-projective K H {l2})
```

## See also

- [Distributivity of truncation over truncation-projective products](foundation.distributivity-of-truncation-over-truncation-projective-products.md)
- [Distributivity of set truncation over finite products](univalent-combinatorics.distributivity-of-set-truncation-over-finite-products.md)
