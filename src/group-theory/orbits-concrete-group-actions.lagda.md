# Orbits of concrete group actions

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.orbits-concrete-group-actions
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types funext
open import foundation.sets funext
open import foundation.universe-levels

open import group-theory.concrete-group-actions funext
open import group-theory.concrete-groups funext
```

</details>

## Idea

The type of **orbits** of a
[concrete group action](group-theory.concrete-group-actions.md) of `G` on `X` is
defined to be the [total space](foundation.dependent-pair-types.md)

```text
  Σ (u : BG), X u.
```

of the type family `X` over the classifying type of the
[concrete group](group-theory.concrete-groups.md) `G`. The idea is that the
"standard" elements of this type are of the form `(* , x)`, where `x` is an
element of the underlying [set](foundation-core.sets.md) `X *` of `X`, and that
the type of [identifications](foundation-core.identity-types.md) from `(* , x)`
to `(* , y)` is [equivalent](foundation-core.equivalences.md) to the type

```text
  Σ (g : G), g x ＝ y.
```

In other words, identifications between the elements `(* , x)` and `(* , y)` in
the type of orbits of `X` are equivalently described as group elements `g` such
that `g x ＝ y`.

Note that the type of orbits of a concrete group is typically a
[`1`-type](foundation-core.1-types.md). In
[Free concrete group actions](group-theory.free-concrete-group-actions.md) we
will show that the type of orbits is a set if and only if the action of `G` on
`X` is free, and in
[Transitive concrete group actions](group-theory.transitive-concrete-group-actions.md)
we will show that the type of orbits is
[`0`-connected](foundation.0-connected-types.md) if and only if the action is
transitive.

## Definition

```agda
orbit-action-Concrete-Group :
  {l1 l2 : Level} (G : Concrete-Group l1) (X : action-Concrete-Group l2 G) →
  UU (l1 ⊔ l2)
orbit-action-Concrete-Group G X =
  Σ (classifying-type-Concrete-Group G) (type-Set ∘ X)
```

## See also

- [Free concrete group actions](group-theory.free-concrete-group-actions.md)
- [Transitive concrete group actions](group-theory.transitive-concrete-group-actions.md)
