# Sequences in pseudometric spaces

```agda
module metric-spaces.sequences-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import metric-spaces.pseudometric-spaces
open import metric-spaces.sequences-premetric-spaces
```

</details>

## Ideas

A
{{#concept "sequence" Disambiguation="in a pseudometric space" Agda=sequence-type-Pseudometric-Space}}
in a [pseudometric space](metric-spaces.pseudometric-spaces.md) is a
[sequence](foundation.sequences.md) in its underlying type.

## Definition

### Sequences in pseudometric spaces

```agda
module _
  {l1 l2 : Level} (M : Pseudometric-Space l1 l2)
  where

  sequence-type-Pseudometric-Space : UU l1
  sequence-type-Pseudometric-Space =
    sequence-type-Premetric-Space (premetric-Pseudometric-Space M)
```
