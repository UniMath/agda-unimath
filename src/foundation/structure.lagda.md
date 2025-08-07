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

Given a type family `𝒫` on the universe, a {{#concept "`𝒫`-structured type"}}
consists of a type `A` _equipped_ with an element of type `𝒫 A`.

## Definitions

```agda
structure : {l1 l2 : Level} (𝒫 : UU l1 → UU l2) → UU (lsuc l1 ⊔ l2)
structure {l1} 𝒫 = Σ (UU l1) 𝒫

fam-structure :
  {l1 l2 l3 : Level} (𝒫 : UU l1 → UU l2) (A : UU l3) → UU (lsuc l1 ⊔ l2 ⊔ l3)
fam-structure 𝒫 A = A → structure 𝒫

structure-map :
  {l1 l2 l3 : Level} (𝒫 : UU (l1 ⊔ l2) → UU l3) {A : UU l1} {B : UU l2}
  (f : A → B) → UU (l2 ⊔ l3)
structure-map 𝒫 {A} {B} f = (b : B) → 𝒫 (fiber f b)

hom-structure :
  {l1 l2 l3 : Level} (𝒫 : UU (l1 ⊔ l2) → UU l3) →
  UU l1 → UU l2 → UU (l1 ⊔ l2 ⊔ l3)
hom-structure 𝒫 A B = Σ (A → B) (structure-map 𝒫)

structure-equality :
  {l1 l2 : Level} (𝒫 : UU l1 → UU l2) → UU l1 → UU (l1 ⊔ l2)
structure-equality 𝒫 A = (x y : A) → 𝒫 (x ＝ y)
```

## Properties

### Having structure is closed under equivalences

This is a consequence of [the univalence axiom](foundation.univalence.md)

```agda
has-structure-equiv :
  {l1 l2 : Level} (𝒫 : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → 𝒫 X → 𝒫 Y
has-structure-equiv 𝒫 e = tr 𝒫 (eq-equiv e)

has-structure-equiv' :
  {l1 l2 : Level} (𝒫 : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → 𝒫 Y → 𝒫 X
has-structure-equiv' 𝒫 e = tr 𝒫 (inv (eq-equiv e))
```

## See also

- [Species of types](species.species-of-types.md)
