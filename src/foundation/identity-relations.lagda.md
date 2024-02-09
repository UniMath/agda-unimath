# Identity relations

```agda
module foundation.identity-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.reflexive-relations
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
```

</details>

## Idea

An {{#concept "identity relation" Agda=Identity-Relation}} on a type `A` is a
[reflexive binary relation](foundation.reflexive-relations.md) `R` on `A`, i.e.,
a binary type family `B : A → A → 𝒰` equipped with a map `i : (x : A) → B x x`,
such that the canonical comparison map

```text
  (x y : A) (p : x ＝ y) → B x y
   x x refl ↦ i x
```

is an [equivalence](foundation-core.equivalences.md).

## Definitions

### The predicate of being an identity relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Reflexive-Relation l2 A)
  where

  is-identity-relation : UU (l1 ⊔ l2)
  is-identity-relation =
    (x y : A) → is-equiv (leq-eq-Reflextive-Relation R x y)
```

### The type of identity relations

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  Identity-Relation : UU (l1 ⊔ lsuc l2)
  Identity-Relation = Σ (Reflexive-Relation l2 A) (is-identity-relation)
```

## Properties

### A reflexive binary relation `A` is an identity system if and only if it is torsorial over every point of `A`

```text
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where

  abstract
    is-identity-relation-is-torsorial :
      (H : is-torsorial B) → is-identity-relation B a b
    is-identity-relation-is-torsorial H P p x y = ?

  abstract
    is-torsorial-is-identity-relation :
      is-identity-relation B a b → is-torsorial B
    pr1 (pr1 (is-torsorial-is-identity-relation H)) = a
    pr2 (pr1 (is-torsorial-is-identity-relation H)) = b
    pr2 (is-torsorial-is-identity-relation H) (x , y) =
      pr1 (H (λ x' y' → (a , b) ＝ (x' , y'))) refl x y

  abstract
    fundamental-theorem-id-is-identity-relation :
      is-identity-relation B a b →
      (f : (x : A) → a ＝ x → B x) → is-fiberwise-equiv f
    fundamental-theorem-id-is-identity-relation H =
      fundamental-theorem-id (is-torsorial-is-identity-relation H)
```

## External links

- [Identity systems](https://1lab.dev/1Lab.Path.IdentitySystem.html) at 1lab
- [identity system](https://ncatlab.org/nlab/show/identity+system) at $n$Lab
