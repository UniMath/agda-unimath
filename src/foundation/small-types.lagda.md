# Small types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.small-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import foundation-core.small-types funext univalence truncations public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.images funext univalence truncations
open import foundation.locally-small-types funext univalence truncations
open import foundation.replacement funext univalence truncations
open import foundation.surjective-maps funext univalence truncations
open import foundation.uniqueness-image funext univalence truncations
open import foundation.universal-property-image funext univalence truncations
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.homotopies
```

</details>

## Properties

### If `f` is a surjective map from a small type into a locally small type, then replacement implies that the codomain is small

```agda
is-small-is-surjective :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-surjective f → is-small l3 A → is-locally-small l3 B →
  is-small l3 B
is-small-is-surjective {f = f} H K L =
  is-small-equiv'
    ( im f)
    ( equiv-equiv-slice-uniqueness-im f id-emb
      ( f , refl-htpy)
      ( is-image-is-surjective f id-emb (f , refl-htpy) H))
    ( replacement f K L)
```

## See also

- [Small maps](foundation.small-maps.md)
