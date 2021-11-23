{-# OPTIONS --without-K --exact-split #-}

module groups.examples-higher-groups where

open import groups.higher-groups public

module _
  {l : Level} (X : UU l)
  where

  classifying-type-symmetric-∞-Group : UU (lsuc l)
  classifying-type-symmetric-∞-Group = component-UU X

  shape-symmetric-∞-Group : classifying-type-symmetric-∞-Group
  shape-symmetric-∞-Group =
    pair X (refl-mere-equiv X)

  classifying-pointed-type-symmetric-∞-Group : Pointed-Type (lsuc l)
  classifying-pointed-type-symmetric-∞-Group =
    pair
      classifying-type-symmetric-∞-Group
      shape-symmetric-∞-Group

  is-path-connected-classifying-type-symmetric-∞-Group :
    is-path-connected classifying-type-symmetric-∞-Group
  is-path-connected-classifying-type-symmetric-∞-Group =
    is-path-connected-component-UU X
  
  symmetric-∞-Group : ∞-Group (lsuc l)
  symmetric-∞-Group =
    pair
      classifying-pointed-type-symmetric-∞-Group
      is-path-connected-classifying-type-symmetric-∞-Group
