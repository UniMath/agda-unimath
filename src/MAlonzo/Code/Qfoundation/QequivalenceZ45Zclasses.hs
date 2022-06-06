{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.Qfoundation.QequivalenceZ45Zclasses where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qembeddings
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qequivalences
import qualified MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qpropositions
import qualified MAlonzo.Code.Qfoundation.QequivalenceZ45Zrelations
import qualified MAlonzo.Code.Qfoundation.Qimages
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Zextensionality
import qualified MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations
import qualified MAlonzo.Code.Qfoundation.Qsets
import qualified MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45Zimage

-- foundation.equivalence-classes._.class-Eq-Rel
d_class'45'Eq'45'Rel_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny -> ()
d_class'45'Eq'45'Rel_16 = erased
-- foundation.equivalence-classes._.is-equivalence-class-Eq-Rel
d_is'45'equivalence'45'class'45'Eq'45'Rel_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  ()
d_is'45'equivalence'45'class'45'Eq'45'Rel_18 = erased
-- foundation.equivalence-classes._.large-set-quotient
d_large'45'set'45'quotient_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  ()
d_large'45'set'45'quotient_24 = erased
-- foundation.equivalence-classes._.quotient-map-large-set-quotient
d_quotient'45'map'45'large'45'set'45'quotient_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_quotient'45'map'45'large'45'set'45'quotient_26 ~v0 ~v1 ~v2 v3
  = du_quotient'45'map'45'large'45'set'45'quotient_26 v3
du_quotient'45'map'45'large'45'set'45'quotient_26 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_quotient'45'map'45'large'45'set'45'quotient_26 v0
  = coe
      MAlonzo.Code.Qfoundation.Qimages.du_map'45'unit'45'im_24
      (coe
         MAlonzo.Code.Qfoundation.QequivalenceZ45Zrelations.du_prop'45'Eq'45'Rel_34
         v0)
-- foundation.equivalence-classes._.emb-large-set-quotient
d_emb'45'large'45'set'45'quotient_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_emb'45'large'45'set'45'quotient_28 ~v0 ~v1 ~v2 ~v3
  = du_emb'45'large'45'set'45'quotient_28
du_emb'45'large'45'set'45'quotient_28 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_emb'45'large'45'set'45'quotient_28
  = coe MAlonzo.Code.Qfoundation.Qimages.du_emb'45'im_136
-- foundation.equivalence-classes._.class-large-set-quotient
d_class'45'large'45'set'45'quotient_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_class'45'large'45'set'45'quotient_30 ~v0 ~v1 ~v2 ~v3
  = du_class'45'large'45'set'45'quotient_30
du_class'45'large'45'set'45'quotient_30 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_class'45'large'45'set'45'quotient_30
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qembeddings.du_map'45'emb_46
      (coe du_emb'45'large'45'set'45'quotient_28)
-- foundation.equivalence-classes._.type-class-large-set-quotient
d_type'45'class'45'large'45'set'45'quotient_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> ()
d_type'45'class'45'large'45'set'45'quotient_32 = erased
-- foundation.equivalence-classes._.is-prop-type-class-large-set-quotient
d_is'45'prop'45'type'45'class'45'large'45'set'45'quotient_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'type'45'class'45'large'45'set'45'quotient_42 ~v0
                                                             ~v1 ~v2 ~v3 v4 v5
  = du_is'45'prop'45'type'45'class'45'large'45'set'45'quotient_42
      v4 v5
du_is'45'prop'45'type'45'class'45'large'45'set'45'quotient_42 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'type'45'class'45'large'45'set'45'quotient_42 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qpropositions.du_is'45'prop'45'type'45'Prop_30
      (coe du_class'45'large'45'set'45'quotient_30 v0 v1)
-- foundation.equivalence-classes._.is-set-large-set-quotient
d_is'45'set'45'large'45'set'45'quotient_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'set'45'large'45'set'45'quotient_48 v0 v1 ~v2 v3
  = du_is'45'set'45'large'45'set'45'quotient_48 v0 v1 v3
du_is'45'set'45'large'45'set'45'quotient_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'set'45'large'45'set'45'quotient_48 v0 v1 v2
  = coe
      MAlonzo.Code.Qfoundation.Qimages.du_is'45'set'45'im_226
      (coe
         MAlonzo.Code.Qfoundation.QequivalenceZ45Zrelations.du_prop'45'Eq'45'Rel_34
         v2)
      (coe
         MAlonzo.Code.Qfoundation.Qsets.du_is'45'set'45'function'45'type_200
         v0 ()
         (MAlonzo.Code.Qfoundation.QpropositionalZ45Zextensionality.d_is'45'set'45'UU'45'Prop_78
            (coe v1)))
-- foundation.equivalence-classes._.large-quotient-Set
d_large'45'quotient'45'Set_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_large'45'quotient'45'Set_50 v0 v1 ~v2 v3
  = du_large'45'quotient'45'Set_50 v0 v1 v3
du_large'45'quotient'45'Set_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_large'45'quotient'45'Set_50 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         du_is'45'set'45'large'45'set'45'quotient_48 (coe v0) (coe v1)
         (coe v2))
-- foundation.equivalence-classes._.unit-im-large-set-quotient
d_unit'45'im'45'large'45'set'45'quotient_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_unit'45'im'45'large'45'set'45'quotient_52 ~v0 ~v1 ~v2 v3
  = du_unit'45'im'45'large'45'set'45'quotient_52 v3
du_unit'45'im'45'large'45'set'45'quotient_52 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_unit'45'im'45'large'45'set'45'quotient_52 v0
  = coe
      MAlonzo.Code.Qfoundation.Qimages.du_unit'45'im_34
      (coe
         MAlonzo.Code.Qfoundation.QequivalenceZ45Zrelations.du_prop'45'Eq'45'Rel_34
         v0)
-- foundation.equivalence-classes._.is-image-large-set-quotient
d_is'45'image'45'large'45'set'45'quotient_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'image'45'large'45'set'45'quotient_56 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_is'45'image'45'large'45'set'45'quotient_56
du_is'45'image'45'large'45'set'45'quotient_56 ::
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'image'45'large'45'set'45'quotient_56
  = coe
      MAlonzo.Code.Qfoundation.QuniversalZ45ZpropertyZ45Zimage.du_is'45'image'45'im_372
-- foundation.equivalence-classes._.is-surjective-quotient-map-large-set-quotient
d_is'45'surjective'45'quotient'45'map'45'large'45'set'45'quotient_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_is'45'surjective'45'quotient'45'map'45'large'45'set'45'quotient_58 ~v0
                                                                     ~v1 ~v2 ~v3
  = du_is'45'surjective'45'quotient'45'map'45'large'45'set'45'quotient_58
du_is'45'surjective'45'quotient'45'map'45'large'45'set'45'quotient_58 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
du_is'45'surjective'45'quotient'45'map'45'large'45'set'45'quotient_58
  = coe
      MAlonzo.Code.Qfoundation.Qimages.du_is'45'surjective'45'map'45'unit'45'im_166
-- foundation.equivalence-classes._.center-total-class-Eq-Rel
d_center'45'total'45'class'45'Eq'45'Rel_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_center'45'total'45'class'45'Eq'45'Rel_76 ~v0 ~v1 ~v2 v3 v4
  = du_center'45'total'45'class'45'Eq'45'Rel_76 v3 v4
du_center'45'total'45'class'45'Eq'45'Rel_76 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_center'45'total'45'class'45'Eq'45'Rel_76 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_quotient'45'map'45'large'45'set'45'quotient_26 v0 v1)
      (coe
         MAlonzo.Code.Qfoundation.QequivalenceZ45Zrelations.du_refl'45'Eq'45'Rel_82
         (coe v0) (coe v1))
-- foundation.equivalence-classes._.contraction-total-class-Eq-Rel
d_contraction'45'total'45'class'45'Eq'45'Rel_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_contraction'45'total'45'class'45'Eq'45'Rel_82 = erased
-- foundation.equivalence-classes._._.α
d_α_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_α_94 = erased
-- foundation.equivalence-classes._.is-contr-total-class-Eq-Rel
d_is'45'contr'45'total'45'class'45'Eq'45'Rel_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'contr'45'total'45'class'45'Eq'45'Rel_106 ~v0 ~v1 ~v2 v3 v4
  = du_is'45'contr'45'total'45'class'45'Eq'45'Rel_106 v3 v4
du_is'45'contr'45'total'45'class'45'Eq'45'Rel_106 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'contr'45'total'45'class'45'Eq'45'Rel_106 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_center'45'total'45'class'45'Eq'45'Rel_76 (coe v0) (coe v1))
      erased
-- foundation.equivalence-classes._.related-eq-quotient
d_related'45'eq'45'quotient_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_related'45'eq'45'quotient_110 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6
  = du_related'45'eq'45'quotient_110 v3 v4
du_related'45'eq'45'quotient_110 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny
du_related'45'eq'45'quotient_110 v0 v1
  = coe
      MAlonzo.Code.Qfoundation.QequivalenceZ45Zrelations.du_refl'45'Eq'45'Rel_82
      (coe v0) (coe v1)
-- foundation.equivalence-classes._.is-equiv-related-eq-quotient
d_is'45'equiv'45'related'45'eq'45'quotient_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'related'45'eq'45'quotient_114 ~v0 ~v1 ~v2 v3 v4
  = du_is'45'equiv'45'related'45'eq'45'quotient_114 v3 v4
du_is'45'equiv'45'related'45'eq'45'quotient_114 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'equiv'45'related'45'eq'45'quotient_114 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QfundamentalZ45ZtheoremZ45ZofZ45ZidentityZ45Ztypes.du_fundamental'45'theorem'45'id_24
      (coe du_quotient'45'map'45'large'45'set'45'quotient_26 v0 v1)
-- foundation.equivalence-classes._.effective-quotient'
d_effective'45'quotient''_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_effective'45'quotient''_118 ~v0 ~v1 ~v2 v3 v4 v5
  = du_effective'45'quotient''_118 v3 v4 v5
du_effective'45'quotient''_118 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_effective'45'quotient''_118 v0 v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (\ v3 -> coe du_related'45'eq'45'quotient_110 (coe v0) (coe v1))
      (coe du_is'45'equiv'45'related'45'eq'45'quotient_114 v0 v1 v2)
-- foundation.equivalence-classes._.eq-effective-quotient'
d_eq'45'effective'45'quotient''_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'effective'45'quotient''_126 = erased
-- foundation.equivalence-classes._.is-effective-quotient-map-large-set-quotient
d_is'45'effective'45'quotient'45'map'45'large'45'set'45'quotient_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'effective'45'quotient'45'map'45'large'45'set'45'quotient_142 ~v0
                                                                     ~v1 ~v2 v3 v4 v5
  = du_is'45'effective'45'quotient'45'map'45'large'45'set'45'quotient_142
      v3 v4 v5
du_is'45'effective'45'quotient'45'map'45'large'45'set'45'quotient_142 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'effective'45'quotient'45'map'45'large'45'set'45'quotient_142 v0
                                                                      v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du__'8728'e__386
      (coe
         MAlonzo.Code.Qfoundation.QequivalenceZ45Zrelations.du_equiv'45'symm'45'Eq'45'Rel_110
         (coe v0) (coe v2) (coe v1))
      (coe
         du_effective'45'quotient''_118 (coe v0) (coe v1)
         (coe du_quotient'45'map'45'large'45'set'45'quotient_26 v0 v2))
-- foundation.equivalence-classes._.apply-effectiveness-quotient-map-large-set-quotient
d_apply'45'effectiveness'45'quotient'45'map'45'large'45'set'45'quotient_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
d_apply'45'effectiveness'45'quotient'45'map'45'large'45'set'45'quotient_152 ~v0
                                                                            ~v1 ~v2 v3 v4 v5
  = du_apply'45'effectiveness'45'quotient'45'map'45'large'45'set'45'quotient_152
      v3 v4 v5
du_apply'45'effectiveness'45'quotient'45'map'45'large'45'set'45'quotient_152 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  AgdaAny
du_apply'45'effectiveness'45'quotient'45'map'45'large'45'set'45'quotient_152 v0
                                                                             v1 v2
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.Qequivalences.du_map'45'equiv_46
      (coe
         du_is'45'effective'45'quotient'45'map'45'large'45'set'45'quotient_142
         (coe v0) (coe v1) (coe v2))
-- foundation.equivalence-classes._.apply-effectiveness-quotient-map-large-set-quotient'
d_apply'45'effectiveness'45'quotient'45'map'45'large'45'set'45'quotient''_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_apply'45'effectiveness'45'quotient'45'map'45'large'45'set'45'quotient''_162
  = erased
-- foundation.equivalence-classes._.is-surjective-and-effective-quotient-map-large-set-quotient
d_is'45'surjective'45'and'45'effective'45'quotient'45'map'45'large'45'set'45'quotient_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'surjective'45'and'45'effective'45'quotient'45'map'45'large'45'set'45'quotient_180 ~v0
                                                                                          ~v1 ~v2 v3
  = du_is'45'surjective'45'and'45'effective'45'quotient'45'map'45'large'45'set'45'quotient_180
      v3
du_is'45'surjective'45'and'45'effective'45'quotient'45'map'45'large'45'set'45'quotient_180 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'surjective'45'and'45'effective'45'quotient'45'map'45'large'45'set'45'quotient_180 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         du_is'45'surjective'45'quotient'45'map'45'large'45'set'45'quotient_58)
      (coe
         du_is'45'effective'45'quotient'45'map'45'large'45'set'45'quotient_142
         (coe v0))
-- foundation.equivalence-classes._.quotient-reflecting-map-large-set-quotient
d_quotient'45'reflecting'45'map'45'large'45'set'45'quotient_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_quotient'45'reflecting'45'map'45'large'45'set'45'quotient_194 ~v0
                                                                ~v1 ~v2 v3
  = du_quotient'45'reflecting'45'map'45'large'45'set'45'quotient_194
      v3
du_quotient'45'reflecting'45'map'45'large'45'set'45'quotient_194 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_quotient'45'reflecting'45'map'45'large'45'set'45'quotient_194 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe du_quotient'45'map'45'large'45'set'45'quotient_26 (coe v0))
      erased
-- foundation.equivalence-classes._.transitive-type-class-large-set-quotient
d_transitive'45'type'45'class'45'large'45'set'45'quotient_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  () ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transitive'45'type'45'class'45'large'45'set'45'quotient_214 ~v0
                                                              v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_transitive'45'type'45'class'45'large'45'set'45'quotient_214
      v1 v3 v4 v5 v6 v7 v8
du_transitive'45'type'45'class'45'large'45'set'45'quotient_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_14 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transitive'45'type'45'class'45'large'45'set'45'quotient_214 v0
                                                               v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Qfoundation.QpropositionalZ45Ztruncations.du_apply'45'universal'45'property'45'trunc'45'Prop_194
      (coe ()) (coe v0)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr2_28
         (coe v2))
      (coe du_class'45'large'45'set'45'quotient_30 v2 v4)
      (coe
         (\ v7 ->
            coe
              MAlonzo.Code.Qfoundation.QequivalenceZ45Zrelations.du_trans'45'Eq'45'Rel_126
              v1
              (MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
                 (coe v7))
              v3 v4 v5 v6))
