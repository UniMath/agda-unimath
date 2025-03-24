# Morphisms of binary relations

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.morphisms-binary-relations
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-homotopies funext
open import foundation.binary-relations funext univalence truncations
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
```

</details>

## Idea

A **morphism** of [binary relations](foundation.binary-relations.md) `R` and `S`
on a type `A` is a family of maps `R x y → S x y` for every pair `x y : A`.

## Definition

### Morphisms of binary relations

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  where

  hom-Relation : Relation l2 A → Relation l3 A → UU (l1 ⊔ l2 ⊔ l3)
  hom-Relation R S = (x y : A) → R x y → S x y
```

## Properties

### Characterization of equality of morphisms of binary relations

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {R : Relation l2 A} {S : Relation l3 A}
  where

  htpy-hom-Relation : (f g : hom-Relation R S) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-hom-Relation = binary-htpy

  extensionality-hom-Relation :
    (f g : hom-Relation R S) → (f ＝ g) ≃ binary-htpy f g
  extensionality-hom-Relation = extensionality-binary-Π

  htpy-eq-hom-Relation :
    (f g : hom-Relation R S) → (f ＝ g) → binary-htpy f g
  htpy-eq-hom-Relation = binary-htpy-eq

  eq-htpy-hom-Relation :
    (f g : hom-Relation R S) → binary-htpy f g → f ＝ g
  eq-htpy-hom-Relation = eq-binary-htpy
```

## See also

- [Large binary relations](foundation.large-binary-relations.md)
