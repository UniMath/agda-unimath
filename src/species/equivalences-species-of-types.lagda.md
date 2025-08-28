# Equivalences of species of types

```agda
module species.equivalences-species-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels

open import species.species-of-types
```

</details>

## Idea

An
{{#concept "equivalence" Disambiguation="of species of types" Agda=equiv-species-types}}
of [species of types](species.species-of-types.md) from `F` to `G` is a
pointwise [equivalence](foundation-core.equivalences.md).

## Definition

```agda
equiv-species-types :
  {l1 l2 l3 : Level} → species-types l1 l2 → species-types l1 l3 →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
equiv-species-types {l1} F G = ((X : UU l1) → F X ≃ G X)
```

## Properties

### The identity type of two species of types is equivalent to the type of equivalences between them

```agda
extensionality-species-types :
  {l1 l2 : Level} (F : species-types l1 l2) (G : species-types l1 l2) →
  (Id F G) ≃ (equiv-species-types F G)
extensionality-species-types = extensionality-fam
```
