# Acyclic maps

```agda
module synthetic-homotopy-theory.acyclic-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.contractible-types
open import foundation-core.equivalences -- REMOVE
open import foundation.contractible-maps
open import foundation.dependent-pair-types -- REMOVE(?)
open import foundation.epimorphisms
open import foundation.fibers-of-maps
open import foundation.propositions
open import foundation.universe-levels
open import foundation.unit-type

open import synthetic-homotopy-theory.acyclic-types
open import synthetic-homotopy-theory.codiagonals-of-maps
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.universal-property-pushouts
open import synthetic-homotopy-theory.cocones-under-spans -- REMOVE
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

### A map is acyclic if and only if it is an epimorphism

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-acyclic-map-is-epimorphism : is-epimorphism f → is-acyclic-map f
  is-acyclic-map-is-epimorphism e b =
    is-contr-equiv
      ( fiber (codiagonal-map f) b)
      ( cogap terminal-map terminal-map (suspension-cocone-fiber f b) ,
        is-equiv-up-pushout-up-pushout
          ( terminal-map)
          ( terminal-map)
          ( cocone-pushout terminal-map terminal-map)
          ( suspension-cocone-fiber f b)
          ( cogap terminal-map terminal-map (suspension-cocone-fiber f b))
          ( htpy-cocone-map-universal-property-pushout
            ( terminal-map)
            ( terminal-map)
            ( cocone-pushout terminal-map terminal-map)
            ( up-pushout terminal-map terminal-map)
            ( suspension-cocone-fiber f b))
          ( up-pushout terminal-map terminal-map)
          ( universal-property-suspension-fiber f b))
      ( is-contr-map-is-equiv
        ( is-equiv-codiagonal-map-is-epimorphism f e)
        ( b))

  is-epimorphism-if-is-acyclic-map : is-acyclic-map f → is-epimorphism f
  is-epimorphism-if-is-acyclic-map a =
    {!is-epimorphism-is-equiv-codiagonal-map!}
```

## See also

- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
