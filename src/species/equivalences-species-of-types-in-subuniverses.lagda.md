# Equivalences of species of types in subuniverses

```agda
module species.equivalences-species-of-types-in-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.identity-types
open import foundation.subuniverses
open import foundation.universe-levels

open import species.species-of-types-in-subuniverses
```

</details>

## Idea

An
{{#concept "equivalence" Disambiguation="of species of types in subuniverses" Agda=equiv-species-subuniverse}}
of
[species of types in subuniverses](species.species-of-types-in-subuniverses.md)
from `F` to `G` is a pointwise [equivalence](foundation-core.equivalences.md).

## Definition

```agda
equiv-species-subuniverse :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (Q : subuniverse l1 l3) →
  species-subuniverse P Q → species-subuniverse P Q →
  UU (lsuc l1 ⊔ l2)
equiv-species-subuniverse {l1} P Q S T =
  (X : type-subuniverse P) →
  inclusion-subuniverse Q (S X) ≃ inclusion-subuniverse Q (T X)
```

## Properties

### The identity type of two species of types is equivalent to the type of equivalences between them

```agda
extensionality-species-subuniverse :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (Q : subuniverse l1 l3) →
  (S : species-subuniverse P Q) → (T : species-subuniverse P Q) →
  (S ＝ T) ≃ (equiv-species-subuniverse P Q S T)
extensionality-species-subuniverse P Q S T =
  extensionality-fam-subuniverse Q S T
```
