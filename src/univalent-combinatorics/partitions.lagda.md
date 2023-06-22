# Partitions of finite types

```agda
module univalent-combinatorics.partitions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalence-extensionality
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universe-levels

open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A partition of a finite type `X` can be defined in several equivalent ways:

- A partition is a subset `P` of the powerset of `X` such that each `U ⊆ X` in
  `P` is inhabited and each element `x : X` is in exactly one subset `U ⊆ X` in
  `P`.
- A partition is an equivalence relation on `X`
- A partition is a decomposition of `X` into a type of the form `Σ A B` where
  `A` is finite and `B` is a family of inhabited finite types, i.e., it consists
  of such `A` and `B` and an equivalence `X ≃ Σ A B`.

Note that the last description is subtly different from the notion of unlabeled
partition (i.e., Ferrers diagram), because it only uses mere equivalences.

## Definition

### Partitions

```agda
partition-𝔽 : {l1 : Level} (l2 l3 : Level) → 𝔽 l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
partition-𝔽 l2 l3 X =
  Σ ( 𝔽 l2)
    ( λ Y →
      Σ ( type-𝔽 Y → 𝔽 l3)
        ( λ Z →
          ( (y : type-𝔽 Y) → type-trunc-Prop (type-𝔽 (Z y))) ×
          ( equiv-𝔽 X (Σ-𝔽 Y Z))))

module _
  {l1 l2 l3 : Level} (X : 𝔽 l1) (P : partition-𝔽 l2 l3 X)
  where

  finite-indexing-type-partition-𝔽 : 𝔽 l2
  finite-indexing-type-partition-𝔽 = pr1 P

  indexing-type-partition-𝔽 : UU l2
  indexing-type-partition-𝔽 = type-𝔽 finite-indexing-type-partition-𝔽

  is-finite-indexing-type-partition-𝔽 : is-finite indexing-type-partition-𝔽
  is-finite-indexing-type-partition-𝔽 =
    is-finite-type-𝔽 finite-indexing-type-partition-𝔽

  number-of-elements-indexing-type-partition-𝔽 : ℕ
  number-of-elements-indexing-type-partition-𝔽 =
    number-of-elements-is-finite is-finite-indexing-type-partition-𝔽

  finite-block-partition-𝔽 : indexing-type-partition-𝔽 → 𝔽 l3
  finite-block-partition-𝔽 = pr1 (pr2 P)

  block-partition-𝔽 : indexing-type-partition-𝔽 → UU l3
  block-partition-𝔽 i = type-𝔽 (finite-block-partition-𝔽 i)

  is-finite-block-partition-𝔽 :
    (i : indexing-type-partition-𝔽) → is-finite (block-partition-𝔽 i)
  is-finite-block-partition-𝔽 i = is-finite-type-𝔽 (finite-block-partition-𝔽 i)

  number-of-elements-block-partition-𝔽 : indexing-type-partition-𝔽 → ℕ
  number-of-elements-block-partition-𝔽 i =
    number-of-elements-is-finite (is-finite-block-partition-𝔽 i)

  is-inhabited-block-partition-𝔽 :
    (i : indexing-type-partition-𝔽) → type-trunc-Prop (block-partition-𝔽 i)
  is-inhabited-block-partition-𝔽 = pr1 (pr2 (pr2 P))

  conversion-partition-𝔽 :
    equiv-𝔽 X (Σ-𝔽 finite-indexing-type-partition-𝔽 finite-block-partition-𝔽)
  conversion-partition-𝔽 = pr2 (pr2 (pr2 P))

  map-conversion-partition-𝔽 :
    type-𝔽 X → Σ indexing-type-partition-𝔽 block-partition-𝔽
  map-conversion-partition-𝔽 = map-equiv conversion-partition-𝔽

  rel-partition-𝔽-Prop : type-𝔽 X → type-𝔽 X → Prop l2
  rel-partition-𝔽-Prop x y =
    Id-Prop
      ( set-𝔽 finite-indexing-type-partition-𝔽)
      ( pr1 (map-conversion-partition-𝔽 x))
      ( pr1 (map-conversion-partition-𝔽 y))

  rel-partition-𝔽 : type-𝔽 X → type-𝔽 X → UU l2
  rel-partition-𝔽 x y = type-Prop (rel-partition-𝔽-Prop x y)

  is-prop-rel-partition-𝔽 : (x y : type-𝔽 X) → is-prop (rel-partition-𝔽 x y)
  is-prop-rel-partition-𝔽 x y = is-prop-type-Prop (rel-partition-𝔽-Prop x y)

  refl-rel-partition-𝔽 : is-reflexive rel-partition-𝔽
  refl-rel-partition-𝔽 x = refl

  symmetric-rel-partition-𝔽 : is-symmetric rel-partition-𝔽
  symmetric-rel-partition-𝔽 x y = inv

  transitive-rel-partition-𝔽 : is-transitive rel-partition-𝔽
  transitive-rel-partition-𝔽 x y z r s = s ∙ r

  eq-rel-partition-𝔽 : Equivalence-Relation l2 (type-𝔽 X)
  pr1 eq-rel-partition-𝔽 = rel-partition-𝔽-Prop
  pr1 (pr2 eq-rel-partition-𝔽) = refl-rel-partition-𝔽
  pr1 (pr2 (pr2 eq-rel-partition-𝔽)) = symmetric-rel-partition-𝔽
  pr2 (pr2 (pr2 eq-rel-partition-𝔽)) = transitive-rel-partition-𝔽
```

### Equivalences of partitions

```agda
equiv-partition-𝔽 :
  {l1 l2 l3 l4 l5 : Level} (X : 𝔽 l1) →
  partition-𝔽 l2 l3 X → partition-𝔽 l4 l5 X → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
equiv-partition-𝔽 X P Q =
  Σ ( indexing-type-partition-𝔽 X P ≃ indexing-type-partition-𝔽 X Q)
    ( λ e →
      Σ ( (i : indexing-type-partition-𝔽 X P) →
          block-partition-𝔽 X P i ≃ block-partition-𝔽 X Q (map-equiv e i))
        ( λ f →
          htpy-equiv
            ( ( equiv-Σ (block-partition-𝔽 X Q) e f) ∘e
              ( conversion-partition-𝔽 X P))
            ( conversion-partition-𝔽 X Q)))

id-equiv-partition-𝔽 :
  {l1 l2 l3 : Level} (X : 𝔽 l1)
  (P : partition-𝔽 l2 l3 X) → equiv-partition-𝔽 X P P
pr1 (id-equiv-partition-𝔽 X P) = id-equiv
pr1 (pr2 (id-equiv-partition-𝔽 X P)) i = id-equiv
pr2 (pr2 (id-equiv-partition-𝔽 X P)) = refl-htpy

extensionality-partition-𝔽 :
  {l1 l2 l3 : Level} (X : 𝔽 l1) (P Q : partition-𝔽 l2 l3 X) →
  Id P Q ≃ equiv-partition-𝔽 X P Q
extensionality-partition-𝔽 X P =
  extensionality-Σ
    ( λ {Y} Zf e →
      Σ ( (i : indexing-type-partition-𝔽 X P) →
          block-partition-𝔽 X P i ≃ type-𝔽 (pr1 Zf (map-equiv e i)))
        ( λ f →
          htpy-equiv
            ( equiv-Σ (type-𝔽 ∘ pr1 Zf) e f ∘e conversion-partition-𝔽 X P)
            ( pr2 (pr2 Zf))))
    ( id-equiv)
    ( pair (λ i → id-equiv) refl-htpy)
    ( extensionality-𝔽 (finite-indexing-type-partition-𝔽 X P))
    ( extensionality-Σ
      ( λ {Z} f α →
        htpy-equiv
          ( equiv-Σ (type-𝔽 ∘ Z) id-equiv α ∘e conversion-partition-𝔽 X P)
          ( pr2 f))
      ( λ i → id-equiv)
      ( refl-htpy)
      ( extensionality-fam-𝔽 (finite-block-partition-𝔽 X P))
      ( λ α →
        ( ( extensionality-equiv (conversion-partition-𝔽 X P) (pr2 α)) ∘e
          ( left-unit-law-prod-is-contr
            ( is-prop-Π
              ( λ _ → is-prop-type-trunc-Prop)
              ( is-inhabited-block-partition-𝔽 X P)
              ( pr1 α)))) ∘e
        ( equiv-pair-eq (pr2 (pr2 P)) α)))
```

## Properties

### The type of finite partitions of a finite type `X` is equivalent to the type of decidable partitions of `X` in the usual sense

This remains to be shown.

### The type of finite partitions of a finite type `X` is equivalent to the type of equivalence relations on `X`

This remains to be shown.

### The type of finite partitions of a finite type is finite

This remains to be shown.

### The number of elements of the type of finite partitions of a finite type is a Stirling number of the second kind

This remains to be shown.

### The type of finite partitions of a contractible type is contractible

This remains to be shown.
