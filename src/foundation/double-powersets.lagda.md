# Double powersets

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.double-powersets
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.existential-quantification funext univalence truncations
open import foundation.powersets funext univalence truncations
open import foundation.propositional-truncations funext univalence
open import foundation.universe-levels

open import foundation-core.propositions
open import foundation-core.subtypes funext

open import order-theory.large-posets funext univalence truncations
open import order-theory.posets funext univalence truncations
```

</details>

## Definitions

### The double powerset

```agda
module _
  {l1 : Level} (l2 : Level)
  where

  double-powerset-Large-Poset :
    UU l1 →
    Large-Poset
      ( λ l3 → l1 ⊔ lsuc l2 ⊔ lsuc l3)
      ( λ l3 l4 → l1 ⊔ lsuc l2 ⊔ l3 ⊔ l4)
  double-powerset-Large-Poset A = powerset-Large-Poset (powerset l2 A)

  double-powerset-Poset :
    (l : Level) → UU l1 → Poset (l1 ⊔ lsuc l2 ⊔ lsuc l) (l1 ⊔ lsuc l2 ⊔ l)
  double-powerset-Poset l A =
    poset-Large-Poset (double-powerset-Large-Poset A) l

  double-powerset : (l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
  double-powerset l3 A = type-Poset (double-powerset-Poset l3 A)
```

## Operations on the double powerset

### Intersections of subtypes of powersets

```agda
intersection-double-powerset :
  {l1 l2 l3 : Level} {A : UU l1} →
  double-powerset l2 l3 A → powerset (l1 ⊔ lsuc l2 ⊔ l3) A
intersection-double-powerset F a =
  Π-Prop (type-subtype F) (λ X → inclusion-subtype F X a)

module _
  {l1 l2 l3 : Level} {A : UU l1} (F : double-powerset l2 l3 A)
  where

  inclusion-intersection-double-powerset :
    (X : type-subtype F) →
    intersection-double-powerset F ⊆ inclusion-subtype F X
  inclusion-intersection-double-powerset X a f = f X

  universal-property-intersection-double-powerset :
    {l : Level} (P : powerset l A)
    (H : (X : type-subtype F) → P ⊆ inclusion-subtype F X) →
    P ⊆ intersection-double-powerset F
  universal-property-intersection-double-powerset P H a p X = H X a p
```

### Unions of subtypes of powersets

```agda
union-double-powerset :
  {l1 l2 l3 : Level} {A : UU l1} →
  double-powerset l2 l3 A → powerset (l1 ⊔ lsuc l2 ⊔ l3) A
union-double-powerset F a =
  ∃ (type-subtype F) (λ X → inclusion-subtype F X a)

module _
  {l1 l2 l3 : Level} {A : UU l1} (F : double-powerset l2 l3 A)
  where

  type-union-double-powerset : UU (l1 ⊔ lsuc l2 ⊔ l3)
  type-union-double-powerset = type-subtype (union-double-powerset F)

  inclusion-union-double-powerset :
    (X : type-subtype F) → inclusion-subtype F X ⊆ union-double-powerset F
  inclusion-union-double-powerset X a = intro-exists X

  universal-property-union-double-powerset :
    {l : Level} (P : powerset l A)
    (H : (X : type-subtype F) → inclusion-subtype F X ⊆ P) →
    union-double-powerset F ⊆ P
  universal-property-union-double-powerset P H a =
    map-universal-property-trunc-Prop
      ( P a)
      ( λ X → H (pr1 X) a (pr2 X))
```
