# Shriek of concrete group homomorphisms

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.shriek-concrete-group-actions
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext univalence
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.set-truncations funext univalence
open import foundation.sets funext univalence
open import foundation.universe-levels

open import group-theory.concrete-group-actions funext univalence truncations
open import group-theory.concrete-groups funext univalence truncations
open import group-theory.homomorphisms-concrete-groups funext univalence truncations
```

</details>

## Definition

### Operations on group actions

```agda
module _
  {l1 l2 : Level} (G : Concrete-Group l1) (H : Concrete-Group l2)
  (f : hom-Concrete-Group G H)
  where

  left-adjoint-subst-action-Concrete-Group :
    {l : Level} → (action-Concrete-Group l G) →
    (action-Concrete-Group (l1 ⊔ l2 ⊔ l) H)
  left-adjoint-subst-action-Concrete-Group X y =
    trunc-Set
      ( Σ ( classifying-type-Concrete-Group G)
          ( λ x →
            type-Set (X x) × Id (classifying-map-hom-Concrete-Group G H f x) y))
```
