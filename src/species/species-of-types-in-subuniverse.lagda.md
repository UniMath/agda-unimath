# Species of subuniverses

```agda
module species.species-of-types-in-subuniverse where
<<<<<<< HEAD

=======
```

<details><summary>Imports</summary>

```agda
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
<<<<<<< HEAD
open import foundation.inhabited-types
open import foundation.subuniverses
open import foundation.unit-type
open import foundation.universe-levels

open import species.species-of-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
```

=======
open import foundation.subuniverses
open import foundation.universe-levels

open import species.species-of-types
```

</details>

>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
### Idea

In this file, we define the type of species of subuniverse. A species of
subuniverse is just a map from a subuniverse `P` to a subuniverse `Q`.

## Definitions

### Species of subuniverses

```agda
species-subuniverse :
  {l1 l2 l3 l4 : Level} → subuniverse l1 l2 → subuniverse l3 l4 →
  UU (lsuc l1 ⊔ l2 ⊔ lsuc l3 ⊔ l4)
species-subuniverse P Q =  type-subuniverse P → type-subuniverse Q
```

### Transport in species

```agda
tr-species-subuniverse :
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l2) (Q : subuniverse l3 l4) →
  (F : species-subuniverse P Q) (X Y : type-subuniverse P) →
  inclusion-subuniverse P X ≃ inclusion-subuniverse P Y →
  inclusion-subuniverse Q (F X) → inclusion-subuniverse Q (F Y)
tr-species-subuniverse P Q F X Y e =
  tr ((inclusion-subuniverse Q) ∘ F) (eq-equiv-subuniverse P e)
```

### Extension into species of types

```agda
module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l2) (Q : subuniverse l3 l4)
  (F : species-subuniverse P Q)
  where

  Σ-extension-species-subuniverse :
    species-types l1 (l2 ⊔ l3)
  Σ-extension-species-subuniverse X =
    Σ (is-in-subuniverse P X) (λ p → inclusion-subuniverse Q (F (X , p)))

  Π-extension-species-subuniverse :
    species-types l1 (l2 ⊔ l3)
  Π-extension-species-subuniverse X =
    (p : is-in-subuniverse P X) → inclusion-subuniverse Q (F (X , p))
```
<<<<<<< HEAD

## Examples

### Species of finite types

A species of finite type is a map from `𝔽` to a `𝔽`.

```agda
species-𝔽 : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
species-𝔽 l1 l2 = species-subuniverse (is-finite-Prop {l1}) (is-finite-Prop {l2})
```

### Species of finite inhabited types

A species of finite inhabited type is a map from the subuniverse of inhabited
finite types to a `𝔽`.

```agda
species-Inhabited-Type-𝔽 : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
species-Inhabited-Type-𝔽 l1 l2 =
  species-subuniverse (is-finite-and-inhabited-Prop {l1}) (is-finite-Prop {l2})
```

### Species of inhabited-types

A species of inhabited type is a map from the subuniverse of inhabited types to
a universe.

```agda
species-inhabited-types : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
species-inhabited-types l1 l2 =
  species-subuniverse (is-inhabited-Prop {l1}) λ (X : UU l2) → unit-Prop
```
=======
>>>>>>> 796439c910d829eeb768284e48e75d667da1fbb3
