# The induction principle for propositional truncation

```agda
module foundation.induction-principle-propositional-truncation where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

The induction principle for the propositional truncations present propositional truncations as higher inductive types.

## Definition

```agda
case-paths-induction-principle-propositional-truncation :
  { l : Level} {l1 l2 : Level} {A : UU l1}
  ( P : Prop l2) (α : (p q : type-Prop P) → p ＝ q) (f : A → type-Prop P) →
  ( B : type-Prop P → UU l) → UU (l ⊔ l2)
case-paths-induction-principle-propositional-truncation P α f B =
  (p q : type-Prop P) (x : B p) (y : B q) → tr B (α p q) x ＝ y

induction-principle-propositional-truncation :
  (l : Level) {l1 l2 : Level} {A : UU l1}
  (P : Prop l2) (α : (p q : type-Prop P) → p ＝ q) (f : A → type-Prop P) →
  UU (lsuc l ⊔ l1 ⊔ l2)
induction-principle-propositional-truncation l {l1} {l2} {A} P α f =
  ( B : type-Prop P → UU l) →
  ( g : (x : A) → (B (f x))) →
  ( β : case-paths-induction-principle-propositional-truncation P α f B) →
  Σ ((p : type-Prop P) → B p) (λ h → (x : A) → h (f x) ＝ g x)
```

## Properties

### A type family over the propositional truncation comes equipped with the structure to satisfy the path clause of the induction principle if and only if it is a family of propositions.

```agda
abstract
  is-prop-case-paths-induction-principle-propositional-truncation :
    { l : Level} {l1 l2 : Level} {A : UU l1}
    ( P : Prop l2) (α : (p q : type-Prop P) → p ＝ q) (f : A → type-Prop P) →
    ( B : type-Prop P → UU l) →
    case-paths-induction-principle-propositional-truncation P α f B →
    ( p : type-Prop P) → is-prop (B p)
  is-prop-case-paths-induction-principle-propositional-truncation P α f B β p =
    is-prop-is-proof-irrelevant (λ x → pair (tr B (α p p) x) (β p p x))

  case-paths-induction-principle-propositional-truncation-is-prop :
    { l : Level} {l1 l2 : Level} {A : UU l1}
    ( P : Prop l2) (α : (p q : type-Prop P) → p ＝ q) (f : A → type-Prop P) →
    ( B : type-Prop P → UU l) →
    ( (p : type-Prop P) → is-prop (B p)) →
    case-paths-induction-principle-propositional-truncation P α f B
  case-paths-induction-principle-propositional-truncation-is-prop
    P α f B is-prop-B p q x y =
    eq-is-prop (is-prop-B q)
```
