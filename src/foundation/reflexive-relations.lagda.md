# Reflexive relations

```agda
module foundation.reflexive-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-dependent-identifications
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

A {{#concept "reflexive relation" Agda=Reflexive-Relation}} on a type `A` is a
type valued [binary relation](foundation.binary-relations.md) `R : A → A → 𝒰`
[equipped](foundation.structure.md) with a proof `r : (x : A) → R x x`.

## Definitions

### Reflexive relations

```agda
Reflexive-Relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Reflexive-Relation l2 A = Σ (Relation l2 A) (λ R → is-reflexive R)

module _
  {l1 l2 : Level} {A : UU l1} (R : Reflexive-Relation l2 A)
  where

  rel-Reflexive-Relation : Relation l2 A
  rel-Reflexive-Relation = pr1 R

  refl-Reflexive-Relation : is-reflexive rel-Reflexive-Relation
  refl-Reflexive-Relation = pr2 R
```

### The identity reflexive relation on a type

```agda
Id-Reflexive-Relation : {l : Level} (A : UU l) → Reflexive-Relation l A
Id-Reflexive-Relation A = (Id , (λ x → refl))
```

## Properties

### A formulation of the dependent action on identifications of reflexivity

Consider a reflexive relation `R` on a type `A` with reflexivity
`r : (x : A) → R x x`, and consider an
[identification](foundation-core.identity-types.md) `p : x ＝ y` in `A`. The
usual
[action on identifications](foundation.action-on-identifications-dependent-functions.md)
yields a [dependent identification](foundation.dependent-identifications.md)

```text
  tr (λ u → R u u) p (r x) ＝ (r y).
```

However, since `R` is a binary indexed family of types, there is also the
[binary dependent identity type](foundation.binary-dependent-identifications.md),
which can be used to express another version of the action on identifications of
the reflexivity element `r`:

```text
  binary-dependent-identification R p p (r x) (r y).
```

This action on identifications can be seen as an instance of a dependent
function over the diagonal map `Δ : A → A × A`, a situation which can be
generalized. At the time of writing, however, the library lacks infrastructure
for the general formulation of the action on identifications of dependent
functions over functions yielding binary dependent identifications.

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Reflexive-Relation l2 A)
  where

  binary-dependent-identification-refl-Reflexive-Relation :
    {x y : A} (p : x ＝ y) →
    binary-dependent-identification
      ( rel-Reflexive-Relation R)
      ( p)
      ( p)
      ( refl-Reflexive-Relation R x)
      ( refl-Reflexive-Relation R y)
  binary-dependent-identification-refl-Reflexive-Relation refl = refl
```
