# Structure

```agda
module foundation.structure where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Given a type family `P` on the universe, a **`P`-structured type** consists of a
type `A` equipped with an element of type `P A`.

## Definition

```agda
structure : {l1 l2 : Level} (P : UU l1 → UU l2) → UU (lsuc l1 ⊔ l2)
structure {l1} P = Σ (UU l1) P

fam-structure :
  {l1 l2 l3 : Level} (P : UU l1 → UU l2) (A : UU l3) → UU (lsuc l1 ⊔ l2 ⊔ l3)
fam-structure P A = A → structure P

structure-map :
  {l1 l2 l3 : Level} (P : UU (l1 ⊔ l2) → UU l3) {A : UU l1} {B : UU l2}
  (f : A → B) → UU (l2 ⊔ l3)
structure-map P {A} {B} f = (b : B) → P (fiber f b)

hom-structure :
  {l1 l2 l3 : Level} (P : UU (l1 ⊔ l2) → UU l3) →
  UU l1 → UU l2 → UU (l1 ⊔ l2 ⊔ l3)
hom-structure P A B = Σ (A → B) (structure-map P)
```

## Properties

### Having structure is closed under equivalences

```agda
has-structure-equiv :
  {l1 l2 : Level} (P : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → P X → P Y
has-structure-equiv P e = tr P (eq-equiv _ _ e)

has-structure-equiv' :
  {l1 l2 : Level} (P : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → P Y → P X
has-structure-equiv' P e = tr P (inv (eq-equiv _ _ e))
```
