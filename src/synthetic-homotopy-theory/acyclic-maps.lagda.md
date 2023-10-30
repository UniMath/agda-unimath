# Acyclic maps

```agda
module synthetic-homotopy-theory.acyclic-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.epimorphisms
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.acyclic-types
open import synthetic-homotopy-theory.codiagonals-of-maps
open import synthetic-homotopy-theory.suspensions-of-types
```

</details>

## Idea

A map `f : A → B` is said to be **acyclic** if its
[fibers](foundation-core.fibers-of-maps.md) are
[acyclic types](synthetic-homotopy-theory.acyclic-types.md).

## Definitions

### The predicate of being an acyclic map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-acyclic-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-acyclic-map-Prop f = Π-Prop B (λ b → is-acyclic-Prop (fiber f b))

  is-acyclic-map : (A → B) → UU (l1 ⊔ l2)
  is-acyclic-map f = type-Prop (is-acyclic-map-Prop f)

  is-prop-is-acyclic-map : (f : A → B) → is-prop (is-acyclic-map f)
  is-prop-is-acyclic-map f = is-prop-type-Prop (is-acyclic-map-Prop f)
```

## Properties

### A map is acyclic if and only if it is an [epimorphism](foundation.epimorphisms.md)

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-acyclic-map-is-epimorphism : is-epimorphism f → is-acyclic-map f
  is-acyclic-map-is-epimorphism e b =
    is-contr-equiv
      ( fiber (codiagonal-map f) b)
      ( equiv-fiber-codiagonal-map-suspension-fiber f b)
      ( is-contr-map-is-equiv
        ( is-equiv-codiagonal-map-is-epimorphism f e)
        ( b))

  is-epimorphism-is-acyclic-map : is-acyclic-map f → is-epimorphism f
  is-epimorphism-is-acyclic-map ac =
    is-epimorphism-is-equiv-codiagonal-map f
      ( is-equiv-is-contr-map
        ( λ b →
          ( is-contr-equiv
            ( suspension (fiber f b))
            ( inv-equiv (equiv-fiber-codiagonal-map-suspension-fiber f b))
            ( ac b))))
```

## See also

- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
