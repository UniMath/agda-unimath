# Constant maps

```agda
module foundation-core.constant-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "constant map" Agda=const}} from `A` to `B` at an element `b : B`
is the function `x ↦ b` mapping every element `x : A` to the given element
`b : B`. In common type theoretic notation, the constant map at `b` is the
function

```text
  λ x → b.
```

## Definition

```agda
const : {l1 l2 : Level} (A : UU l1) {B : UU l2} → B → A → B
const A b x = b
```

## See also

- [Coherently constant maps](foundation.coherently-constant-maps.md) for the
  condition on a map of being constant
- [Constant pointed maps](structured-types.constant-pointed-maps.md)
