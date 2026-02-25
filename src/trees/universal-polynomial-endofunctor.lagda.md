# The universal polynomial endofunctor

```agda
module trees.universal-polynomial-endofunctor where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import trees.polynomial-endofunctors
```

</details>

## Idea

The
{{#concept "universal polynomial endofunctor" Agda=universal-polynomial-endofunctor}}
is the [polynomial endofunctor](trees.polynomial-endofunctors.md) whose type of
shapes is the universe of types `Type`, and whose family of positions is the
identity function.

## Definition

```agda
universal-polynomial-endofunctor :
  (l : Level) → polynomial-endofunctor (lsuc l) l
universal-polynomial-endofunctor l = (UU l , id)
```
